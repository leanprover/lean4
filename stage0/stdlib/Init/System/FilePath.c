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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
extern uint8_t l_System_Platform_isWindows;
uint8_t lean_bool_not(uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0;
static const lean_array_object l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1 = (const lean_object*)&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_System_FilePath_fileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_System_FilePath_fileName___closed__0 = (const lean_object*)&l_System_FilePath_fileName___closed__0_value;
static const lean_string_object l_System_FilePath_fileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
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
lean_object* v_countdown_72_; lean_object* v_inner_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_92_; 
v_countdown_72_ = lean_ctor_get(v_a_70_, 0);
v_inner_73_ = lean_ctor_get(v_a_70_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_a_70_);
if (v_isSharedCheck_92_ == 0)
{
v___x_75_ = v_a_70_;
v_isShared_76_ = v_isSharedCheck_92_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_inner_73_);
lean_inc(v_countdown_72_);
lean_dec(v_a_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_92_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_dec_eq(v_countdown_72_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v_startInclusive_79_; lean_object* v_endExclusive_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_startInclusive_79_ = lean_ctor_get(v___x_68_, 1);
v_endExclusive_80_ = lean_ctor_get(v___x_68_, 2);
v___x_81_ = lean_nat_sub(v_endExclusive_80_, v_startInclusive_79_);
v___x_82_ = lean_nat_dec_eq(v_inner_73_, v___x_81_);
lean_dec(v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint32_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_83_ = lean_string_utf8_next_fast(v___x_69_, v_inner_73_);
v___x_84_ = lean_string_utf8_get_fast(v___x_69_, v_inner_73_);
lean_dec(v_inner_73_);
v___x_85_ = lean_nat_sub(v_countdown_72_, v___x_77_);
lean_dec(v_countdown_72_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_83_);
lean_ctor_set(v___x_75_, 0, v___x_85_);
v___x_87_ = v___x_75_;
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
v___x_89_ = lean_array_push(v_b_71_, v___x_88_);
v_a_70_ = v___x_87_;
v_b_71_ = v___x_89_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v___x_93_, lean_object* v___x_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_93_, v___x_94_, v_a_95_, v_b_96_);
lean_dec_ref(v___x_94_);
lean_dec_ref(v___x_93_);
return v_res_97_;
}
}
static uint8_t _init_l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0(void){
_start:
{
uint8_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_System_Platform_isWindows;
v___x_99_ = lean_bool_not(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object* v_p_102_){
_start:
{
uint8_t v___y_104_; uint8_t v___x_116_; 
v___x_116_ = lean_uint8_once(&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0, &l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_once, _init_l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_string_utf8_byte_size(v_p_102_);
lean_inc_ref(v_p_102_);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v_p_102_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
v___x_120_ = l_String_Slice_positions(v___x_119_);
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
v___x_123_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1));
v___x_124_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_119_, v_p_102_, v___x_122_, v___x_123_);
lean_dec_ref_known(v___x_119_, 3);
v___x_125_ = lean_array_to_list(v___x_124_);
if (lean_obj_tag(v___x_125_) == 1)
{
lean_object* v_tail_126_; 
v_tail_126_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_tail_126_);
if (lean_obj_tag(v_tail_126_) == 1)
{
lean_object* v_head_127_; lean_object* v_head_128_; lean_object* v_tail_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint8_t v___x_132_; 
v_head_127_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_head_127_);
lean_dec_ref_known(v___x_125_, 2);
v_head_128_ = lean_ctor_get(v_tail_126_, 0);
lean_inc(v_head_128_);
v_tail_129_ = lean_ctor_get(v_tail_126_, 1);
lean_inc(v_tail_129_);
lean_dec_ref_known(v_tail_126_, 2);
v___x_130_ = 58;
v___x_131_ = lean_unbox_uint32(v_head_128_);
lean_dec(v_head_128_);
v___x_132_ = lean_uint32_dec_eq(v___x_131_, v___x_130_);
if (v___x_132_ == 0)
{
lean_dec(v_tail_129_);
lean_dec(v_head_127_);
return v_p_102_;
}
else
{
if (lean_obj_tag(v_tail_129_) == 0)
{
uint32_t v___x_133_; uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_133_ = 97;
v___x_134_ = lean_unbox_uint32(v_head_127_);
v___x_135_ = lean_uint32_dec_le(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v_head_127_);
v___y_104_ = v___x_135_;
goto v___jp_103_;
}
else
{
uint32_t v___x_136_; uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = 122;
v___x_137_ = lean_unbox_uint32(v_head_127_);
lean_dec(v_head_127_);
v___x_138_ = lean_uint32_dec_le(v___x_137_, v___x_136_);
v___y_104_ = v___x_138_;
goto v___jp_103_;
}
}
else
{
lean_dec(v_tail_129_);
lean_dec(v_head_127_);
return v_p_102_;
}
}
}
else
{
lean_dec_ref_known(v___x_125_, 2);
lean_dec(v_tail_126_);
return v_p_102_;
}
}
else
{
lean_dec(v___x_125_);
return v_p_102_;
}
}
else
{
return v_p_102_;
}
v___jp_103_:
{
if (v___y_104_ == 0)
{
return v_p_102_;
}
else
{
lean_object* v___x_105_; uint32_t v___x_106_; uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_string_utf8_get(v_p_102_, v___x_105_);
v___x_107_ = 97;
v___x_108_ = lean_uint32_dec_le(v___x_107_, v___x_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_string_utf8_set(v_p_102_, v___x_105_, v___x_106_);
return v___x_109_;
}
else
{
uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 122;
v___x_111_ = lean_uint32_dec_le(v___x_106_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_string_utf8_set(v_p_102_, v___x_105_, v___x_106_);
return v___x_112_;
}
else
{
uint32_t v___x_113_; uint32_t v___x_114_; lean_object* v___x_115_; 
v___x_113_ = 4294967264;
v___x_114_ = lean_uint32_add(v___x_106_, v___x_113_);
v___x_115_ = lean_string_utf8_set(v_p_102_, v___x_105_, v___x_114_);
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object* v___x_139_, lean_object* v___x_140_, lean_object* v_inst_141_, lean_object* v_R_142_, lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_139_, v___x_140_, v_a_143_, v_b_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_146_, lean_object* v___x_147_, lean_object* v_inst_148_, lean_object* v_R_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_146_, v___x_147_, v_inst_148_, v_R_149_, v_a_150_, v_b_151_);
lean_dec_ref(v___x_147_);
lean_dec_ref(v___x_146_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; uint32_t v___x_158_; uint8_t v___x_159_; 
v_head_156_ = lean_ctor_get(v_x_154_, 0);
v_tail_157_ = lean_ctor_get(v_x_154_, 1);
v___x_158_ = lean_unbox_uint32(v_head_156_);
v___x_159_ = lean_uint32_dec_eq(v_a_153_, v___x_158_);
if (v___x_159_ == 0)
{
v_x_154_ = v_tail_157_;
goto _start;
}
else
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_161_, lean_object* v_x_162_){
_start:
{
uint32_t v_a_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_a_boxed_163_ = lean_unbox_uint32(v_a_161_);
lean_dec(v_a_161_);
v_res_164_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_163_, v_x_162_);
lean_dec(v_x_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_166_, lean_object* v_p_167_){
_start:
{
uint32_t v___y_169_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_string_utf8_byte_size(v_s_166_);
v___x_175_ = lean_nat_dec_eq(v_p_167_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_176_ = l_System_FilePath_pathSeparators;
v___x_177_ = lean_string_utf8_get_fast(v_s_166_, v_p_167_);
v___x_178_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_177_, v___x_176_);
if (v___x_178_ == 0)
{
v___y_169_ = v___x_177_;
goto v___jp_168_;
}
else
{
uint32_t v___x_179_; 
v___x_179_ = l_System_FilePath_pathSeparator;
v___y_169_ = v___x_179_;
goto v___jp_168_;
}
}
else
{
lean_dec(v_p_167_);
return v_s_166_;
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_p_167_);
v___x_170_ = lean_string_utf8_set(v_s_166_, v_p_167_, v___y_169_);
v___x_171_ = l_Char_utf8Size(v___y_169_);
v___x_172_ = lean_nat_add(v_p_167_, v___x_171_);
lean_dec(v___x_171_);
lean_dec(v_p_167_);
v_s_166_ = v___x_170_;
v_p_167_ = v___x_172_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = l_System_FilePath_pathSeparators;
v___x_181_ = l_List_lengthTR___redArg(v___x_180_);
return v___x_181_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_184_ = lean_nat_dec_eq(v___x_183_, v___x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_185_){
_start:
{
lean_object* v_p_186_; uint8_t v___x_187_; 
v_p_186_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_185_);
v___x_187_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v_p_189_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v_p_189_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_186_, v___x_188_);
return v_p_189_;
}
else
{
return v_p_186_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
if (lean_obj_tag(v_x_191_) == 0)
{
uint8_t v___x_192_; 
v___x_192_ = 1;
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
else
{
if (lean_obj_tag(v_x_191_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
else
{
lean_object* v_val_195_; lean_object* v_val_196_; uint32_t v___x_197_; uint32_t v___x_198_; uint8_t v___x_199_; 
v_val_195_ = lean_ctor_get(v_x_190_, 0);
v_val_196_ = lean_ctor_get(v_x_191_, 0);
v___x_197_ = lean_unbox_uint32(v_val_195_);
v___x_198_ = lean_unbox_uint32(v_val_196_);
v___x_199_ = lean_uint32_dec_eq(v___x_197_, v___x_198_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec(v_x_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_204_, lean_object* v___x_205_, lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v_str_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_str_208_ = lean_ctor_get(v___x_205_, 0);
v_startInclusive_209_ = lean_ctor_get(v___x_205_, 1);
v_endExclusive_210_ = lean_ctor_get(v___x_205_, 2);
v___x_211_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
v___x_212_ = lean_nat_dec_eq(v_a_206_, v___x_211_);
lean_dec(v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v_zero_213_; uint8_t v_isZero_214_; 
v_zero_213_ = lean_unsigned_to_nat(0u);
v_isZero_214_ = lean_nat_dec_eq(v_b_207_, v_zero_213_);
if (v_isZero_214_ == 1)
{
uint32_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_b_207_);
v___x_215_ = lean_string_utf8_get_fast(v___x_204_, v_a_206_);
lean_dec(v_a_206_);
v___x_216_ = lean_box_uint32(v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_one_221_; lean_object* v_n_222_; 
v___x_218_ = lean_nat_add(v_startInclusive_209_, v_a_206_);
lean_dec(v_a_206_);
v___x_219_ = lean_string_utf8_next_fast(v_str_208_, v___x_218_);
lean_dec(v___x_218_);
v___x_220_ = lean_nat_sub(v___x_219_, v_startInclusive_209_);
v_one_221_ = lean_unsigned_to_nat(1u);
v_n_222_ = lean_nat_sub(v_b_207_, v_one_221_);
lean_dec(v_b_207_);
v_a_206_ = v___x_220_;
v_b_207_ = v_n_222_;
goto _start;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v_b_207_);
lean_dec(v_a_206_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_225_, v___x_226_, v_a_227_, v_b_228_);
lean_dec_ref(v___x_226_);
lean_dec_ref(v___x_225_);
return v_res_229_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 58;
v___x_231_ = lean_box_uint32(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_234_){
_start:
{
lean_object* v___x_235_; uint32_t v___y_237_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_235_ = l_System_FilePath_pathSeparators;
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_string_utf8_byte_size(v_p_234_);
lean_inc_ref(v_p_234_);
v___x_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_250_, 0, v_p_234_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
lean_ctor_set(v___x_250_, 2, v___x_249_);
v___x_251_ = l_String_Slice_Pos_get_x3f(v___x_250_, v___x_248_);
lean_dec_ref_known(v___x_250_, 3);
if (lean_obj_tag(v___x_251_) == 0)
{
uint32_t v___x_252_; 
v___x_252_ = 65;
v___y_237_ = v___x_252_;
goto v___jp_236_;
}
else
{
lean_object* v_val_253_; uint32_t v___x_254_; 
v_val_253_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v___x_251_, 1);
v___x_254_ = lean_unbox_uint32(v_val_253_);
lean_dec(v_val_253_);
v___y_237_ = v___x_254_;
goto v___jp_236_;
}
v___jp_236_:
{
uint8_t v___x_238_; 
v___x_238_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_237_, v___x_235_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = l_System_Platform_isWindows;
if (v___x_239_ == 0)
{
lean_dec_ref(v_p_234_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_string_utf8_byte_size(v_p_234_);
lean_inc_ref(v_p_234_);
v___x_242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_242_, 0, v_p_234_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = l_String_Slice_positions(v___x_242_);
v___x_245_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_234_, v___x_242_, v___x_244_, v___x_243_);
lean_dec_ref_known(v___x_242_, 3);
lean_dec_ref(v_p_234_);
v___x_246_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_247_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_245_, v___x_246_);
lean_dec(v___x_245_);
return v___x_247_;
}
}
else
{
lean_dec_ref(v_p_234_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_System_FilePath_isAbsolute(v_p_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_258_, lean_object* v___x_259_, lean_object* v_n_260_, lean_object* v_it_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_259_, v___x_258_, v_it_261_, v_n_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_n_265_, lean_object* v_it_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_263_, v___x_264_, v_n_265_, v_it_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v_inst_270_, lean_object* v_R_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_268_, v___x_269_, v_a_272_, v_b_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_R_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_275_, v___x_276_, v_inst_277_, v_R_278_, v_a_279_, v_b_280_);
lean_dec_ref(v___x_276_);
lean_dec_ref(v___x_275_);
return v_res_281_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_282_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_System_FilePath_isAbsolute(v_p_282_);
v___x_284_ = lean_bool_not(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_System_FilePath_isRelative(v_p_285_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = l_System_FilePath_pathSeparator;
v___x_289_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_290_ = lean_string_push(v___x_289_, v___x_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_291_, lean_object* v_sub_292_){
_start:
{
uint8_t v___x_293_; 
lean_inc_ref(v_sub_292_);
v___x_293_ = l_System_FilePath_isAbsolute(v_sub_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_295_ = lean_string_append(v_p_291_, v___x_294_);
v___x_296_ = lean_string_append(v___x_295_, v_sub_292_);
lean_dec_ref(v_sub_292_);
return v___x_296_;
}
else
{
lean_dec_ref(v_p_291_);
return v_sub_292_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_300_, lean_object* v_a_301_, lean_object* v_b_302_){
_start:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v_a_301_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v_str_305_; lean_object* v_startInclusive_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint32_t v___x_315_; uint8_t v___x_316_; 
v_str_305_ = lean_ctor_get(v_s_300_, 0);
v_startInclusive_306_ = lean_ctor_get(v_s_300_, 1);
v___x_307_ = l_System_FilePath_pathSeparators;
v___x_308_ = lean_nat_add(v_startInclusive_306_, v_a_301_);
lean_inc(v___x_308_);
lean_inc(v_startInclusive_306_);
lean_inc_ref(v_str_305_);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v_str_305_);
lean_ctor_set(v___x_309_, 1, v_startInclusive_306_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
v___x_310_ = lean_nat_sub(v___x_308_, v_startInclusive_306_);
lean_dec(v___x_308_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_sub(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
v___x_313_ = l_String_Slice_posLE(v___x_309_, v___x_312_);
lean_dec_ref_known(v___x_309_, 3);
v___x_314_ = lean_nat_add(v_startInclusive_306_, v___x_313_);
v___x_315_ = lean_string_utf8_get_fast(v_str_305_, v___x_314_);
lean_dec(v___x_314_);
v___x_316_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_315_, v___x_307_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v___x_313_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_nat_sub(v_a_301_, v___x_311_);
lean_dec(v_a_301_);
v___x_319_ = l_String_Slice_posLE(v_s_300_, v___x_318_);
v_a_301_ = v___x_319_;
v_b_302_ = v___x_317_;
goto _start;
}
else
{
lean_object* v___x_321_; 
lean_dec(v_a_301_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_313_);
return v___x_321_;
}
}
else
{
lean_dec(v_a_301_);
lean_inc(v_b_302_);
return v_b_302_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_322_, v_a_323_, v_b_324_);
lean_dec(v_b_324_);
lean_dec_ref(v_s_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_326_){
_start:
{
lean_object* v_startInclusive_327_; lean_object* v_endExclusive_328_; lean_object* v_searcher_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_startInclusive_327_ = lean_ctor_get(v_s_326_, 1);
v_endExclusive_328_ = lean_ctor_get(v_s_326_, 2);
v_searcher_329_ = lean_nat_sub(v_endExclusive_328_, v_startInclusive_327_);
v___x_330_ = lean_box(0);
v___x_331_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_326_, v_searcher_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_332_);
lean_dec_ref(v_s_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_string_utf8_byte_size(v_p_334_);
v___x_337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_337_, 0, v_p_334_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_337_);
lean_dec_ref_known(v___x_337_, 3);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_val_340_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_val_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_348_, lean_object* v_inst_349_, lean_object* v_R_350_, lean_object* v_a_351_, lean_object* v_b_352_, lean_object* v_c_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_348_, v_a_351_, v_b_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_355_, lean_object* v_inst_356_, lean_object* v_R_357_, lean_object* v_a_358_, lean_object* v_b_359_, lean_object* v_c_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_355_, v_inst_356_, v_R_357_, v_a_358_, v_b_359_, v_c_360_);
lean_dec(v_b_359_);
lean_dec_ref(v_s_355_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_362_){
_start:
{
lean_object* v___x_363_; uint32_t v___y_365_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_363_ = l_System_FilePath_pathSeparators;
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_string_utf8_byte_size(v_p_362_);
lean_inc_ref(v_p_362_);
v___x_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_379_, 0, v_p_362_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
v___x_380_ = l_String_Slice_Pos_get_x3f(v___x_379_, v___x_377_);
lean_dec_ref_known(v___x_379_, 3);
if (lean_obj_tag(v___x_380_) == 0)
{
uint32_t v___x_381_; 
v___x_381_ = 65;
v___y_365_ = v___x_381_;
goto v___jp_364_;
}
else
{
lean_object* v_val_382_; uint32_t v___x_383_; 
v_val_382_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v___x_380_, 1);
v___x_383_ = lean_unbox_uint32(v_val_382_);
lean_dec(v_val_382_);
v___y_365_ = v___x_383_;
goto v___jp_364_;
}
v___jp_364_:
{
uint8_t v___x_366_; 
v___x_366_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_365_, v___x_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = lean_string_utf8_byte_size(v_p_362_);
v___x_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_370_, 0, v_p_362_);
lean_ctor_set(v___x_370_, 1, v___x_367_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
v___x_371_ = l_String_Slice_Pos_nextn(v___x_370_, v___x_367_, v___x_368_);
lean_dec_ref_known(v___x_370_, 3);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_string_utf8_byte_size(v_p_362_);
v___x_375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_375_, 0, v_p_362_);
lean_ctor_set(v___x_375_, 1, v___x_372_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
v___x_376_ = l_String_Slice_Pos_nextn(v___x_375_, v___x_372_, v___x_373_);
lean_dec_ref_known(v___x_375_, 3);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_384_){
_start:
{
lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___x_395_; lean_object* v___y_397_; 
lean_inc_ref(v_p_384_);
v___x_395_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_384_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
v___y_397_ = v___x_417_;
goto v___jp_396_;
}
else
{
lean_object* v_val_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_val_418_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_418_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_string_utf8_extract(v_p_384_, v___x_419_, v_val_418_);
lean_dec(v_val_418_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
v___y_397_ = v___x_421_;
goto v___jp_396_;
}
v___jp_385_:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
lean_inc(v___y_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___y_388_);
v___x_391_ = l_Option_instDecidableEq___redArg(v___y_387_, v___y_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v___y_388_);
lean_dec_ref(v_p_384_);
return v___y_386_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v___y_386_);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_string_utf8_extract(v_p_384_, v___x_392_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v_p_384_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
v___jp_396_:
{
uint8_t v___x_398_; 
lean_inc_ref(v_p_384_);
v___x_398_ = l_System_FilePath_isAbsolute(v_p_384_);
if (v___x_398_ == 0)
{
lean_dec(v___x_395_);
lean_dec_ref(v_p_384_);
return v___y_397_;
}
else
{
lean_object* v_afterRootDirectory_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
lean_inc_ref(v_p_384_);
v_afterRootDirectory_399_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_384_);
v___x_400_ = lean_string_utf8_byte_size(v_p_384_);
v___x_401_ = lean_nat_dec_eq(v_afterRootDirectory_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_inc_ref(v_p_384_);
v___x_402_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_402_, 0, v_p_384_);
if (lean_obj_tag(v___x_395_) == 0)
{
v___y_386_ = v___y_397_;
v___y_387_ = v___x_402_;
v___y_388_ = v_afterRootDirectory_399_;
v___y_389_ = v___x_395_;
goto v___jp_385_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_val_403_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_395_, 1);
v___x_404_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_384_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v_p_384_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v___x_400_);
v___x_406_ = l_String_Slice_Pos_next_x3f(v___x_405_, v_val_403_);
lean_dec(v_val_403_);
lean_dec_ref_known(v___x_405_, 3);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
v___y_386_ = v___y_397_;
v___y_387_ = v___x_402_;
v___y_388_ = v_afterRootDirectory_399_;
v___y_389_ = v___x_407_;
goto v___jp_385_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_val_408_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_406_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v___x_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_val_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
v___y_386_ = v___y_397_;
v___y_387_ = v___x_402_;
v___y_388_ = v_afterRootDirectory_399_;
v___y_389_ = v___x_413_;
goto v___jp_385_;
}
}
}
}
}
else
{
lean_object* v___x_416_; 
lean_dec(v_afterRootDirectory_399_);
lean_dec(v___y_397_);
lean_dec(v___x_395_);
lean_dec_ref(v_p_384_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_424_){
_start:
{
lean_object* v___y_426_; uint8_t v___y_427_; lean_object* v___y_434_; lean_object* v___x_440_; 
lean_inc_ref(v_p_424_);
v___x_440_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_424_);
if (lean_obj_tag(v___x_440_) == 0)
{
v___y_434_ = v_p_424_;
goto v___jp_433_;
}
else
{
lean_object* v_val_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_val_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_val_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_string_utf8_byte_size(v_p_424_);
lean_inc_ref(v_p_424_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v_p_424_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
v___x_445_ = l_String_Slice_Pos_next_x21(v___x_444_, v_val_441_);
lean_dec(v_val_441_);
lean_dec_ref_known(v___x_444_, 3);
v___x_446_ = lean_string_utf8_extract(v_p_424_, v___x_445_, v___x_443_);
lean_dec(v___x_445_);
lean_dec_ref(v_p_424_);
v___y_434_ = v___x_446_;
goto v___jp_433_;
}
v___jp_425_:
{
if (v___y_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_429_ = lean_string_dec_eq(v___y_426_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v___y_426_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v___y_426_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
else
{
lean_object* v___x_432_; 
lean_dec_ref(v___y_426_);
v___x_432_ = lean_box(0);
return v___x_432_;
}
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_string_utf8_byte_size(v___y_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_439_ = lean_string_dec_eq(v___y_434_, v___x_438_);
v___y_426_ = v___y_434_;
v___y_427_ = v___x_439_;
goto v___jp_425_;
}
else
{
v___y_426_ = v___y_434_;
v___y_427_ = v___x_437_;
goto v___jp_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_447_, lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v_a_448_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v_str_452_; lean_object* v_startInclusive_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint32_t v___x_461_; uint32_t v___x_462_; uint8_t v___x_463_; 
v_str_452_ = lean_ctor_get(v_s_447_, 0);
v_startInclusive_453_ = lean_ctor_get(v_s_447_, 1);
v___x_454_ = lean_nat_add(v_startInclusive_453_, v_a_448_);
lean_inc(v___x_454_);
lean_inc(v_startInclusive_453_);
lean_inc_ref(v_str_452_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_str_452_);
lean_ctor_set(v___x_455_, 1, v_startInclusive_453_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
v___x_456_ = lean_nat_sub(v___x_454_, v_startInclusive_453_);
lean_dec(v___x_454_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_sub(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
v___x_459_ = l_String_Slice_posLE(v___x_455_, v___x_458_);
lean_dec_ref_known(v___x_455_, 3);
v___x_460_ = lean_nat_add(v_startInclusive_453_, v___x_459_);
v___x_461_ = lean_string_utf8_get_fast(v_str_452_, v___x_460_);
lean_dec(v___x_460_);
v___x_462_ = 46;
v___x_463_ = lean_uint32_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v___x_459_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_nat_sub(v_a_448_, v___x_457_);
lean_dec(v_a_448_);
v___x_466_ = l_String_Slice_posLE(v_s_447_, v___x_465_);
v_a_448_ = v___x_466_;
v_b_449_ = v___x_464_;
goto _start;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_a_448_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_459_);
return v___x_468_;
}
}
else
{
lean_dec(v_a_448_);
lean_inc(v_b_449_);
return v_b_449_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_469_, v_a_470_, v_b_471_);
lean_dec(v_b_471_);
lean_dec_ref(v_s_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_473_){
_start:
{
lean_object* v_startInclusive_474_; lean_object* v_endExclusive_475_; lean_object* v_searcher_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_startInclusive_474_ = lean_ctor_get(v_s_473_, 1);
v_endExclusive_475_ = lean_ctor_get(v_s_473_, 2);
v_searcher_476_ = lean_nat_sub(v_endExclusive_475_, v_startInclusive_474_);
v___x_477_ = lean_box(0);
v___x_478_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_473_, v_searcher_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_479_);
lean_dec_ref(v_s_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_System_FilePath_fileName(v_p_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_val_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_n(v_val_483_, 2);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_string_utf8_byte_size(v_val_483_);
v___x_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_486_, 0, v_val_483_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
v___x_487_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_486_);
lean_dec_ref_known(v___x_486_, 3);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_dec(v_val_483_);
return v___x_482_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v_val_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_val_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_eq(v_val_488_, v___x_484_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec_ref_known(v___x_482_, 1);
v___x_493_ = lean_string_utf8_extract(v_val_483_, v___x_484_, v_val_488_);
lean_dec(v_val_488_);
lean_dec(v_val_483_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_del_object(v___x_490_);
lean_dec(v_val_488_);
lean_dec(v_val_483_);
return v___x_482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_498_, lean_object* v_inst_499_, lean_object* v_R_500_, lean_object* v_a_501_, lean_object* v_b_502_, lean_object* v_c_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_498_, v_a_501_, v_b_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_505_, lean_object* v_inst_506_, lean_object* v_R_507_, lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v_c_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_505_, v_inst_506_, v_R_507_, v_a_508_, v_b_509_, v_c_510_);
lean_dec(v_b_509_);
lean_dec_ref(v_s_505_);
return v_res_511_;
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0(void){
_start:
{
uint32_t v___x_512_; lean_object* v___x_513_; 
v___x_512_ = 46;
v___x_513_ = l_Char_utf8Size(v___x_512_);
return v___x_513_;
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
v___x_527_ = lean_obj_once(&l_System_FilePath_extension___closed__0, &l_System_FilePath_extension___closed__0_once, _init_l_System_FilePath_extension___closed__0);
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
v___x_547_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
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
v___x_562_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
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
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_571_ = lean_string_utf8_byte_size(v___x_570_);
return v___x_571_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_574_ = lean_nat_dec_eq(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_575_);
return v___x_578_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_580_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
v___x_583_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_584_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
lean_ctor_set(v___x_584_, 3, v___x_581_);
return v___x_584_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7));
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_597_);
lean_dec_ref(v_s_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
lean_object* v_it_605_; lean_object* v_startInclusive_606_; lean_object* v_endExclusive_607_; 
if (lean_obj_tag(v_a_602_) == 0)
{
lean_object* v_currPos_612_; lean_object* v_searcher_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_717_; 
v_currPos_612_ = lean_ctor_get(v_a_602_, 0);
v_searcher_613_ = lean_ctor_get(v_a_602_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_717_ == 0)
{
v___x_615_ = v_a_602_;
v_isShared_616_ = v_isSharedCheck_717_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_searcher_613_);
lean_inc(v_currPos_612_);
lean_dec(v_a_602_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_717_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_it_618_; lean_object* v_it_624_; lean_object* v_startPos_625_; lean_object* v_endPos_626_; 
switch(lean_obj_tag(v_searcher_613_))
{
case 0:
{
lean_object* v_pos_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_615_);
v_pos_639_ = lean_ctor_get(v_searcher_613_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_searcher_613_);
if (v_isSharedCheck_651_ == 0)
{
v___x_641_ = v_searcher_613_;
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_pos_639_);
lean_dec(v_searcher_613_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_startInclusive_643_; lean_object* v_endExclusive_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_startInclusive_643_ = lean_ctor_get(v___x_600_, 1);
v_endExclusive_644_ = lean_ctor_get(v___x_600_, 2);
v___x_645_ = lean_nat_sub(v_endExclusive_644_, v_startInclusive_643_);
v___x_646_ = lean_nat_dec_eq(v_pos_639_, v___x_645_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
lean_inc(v_pos_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 1);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_pos_639_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_inc(v_pos_639_);
v_it_624_ = v___x_648_;
v_startPos_625_ = v_pos_639_;
v_endPos_626_ = v_pos_639_;
goto v___jp_623_;
}
}
else
{
lean_object* v___x_650_; 
lean_del_object(v___x_641_);
v___x_650_ = lean_box(3);
lean_inc(v_pos_639_);
v_it_624_ = v___x_650_;
v_startPos_625_ = v_pos_639_;
v_endPos_626_ = v_pos_639_;
goto v___jp_623_;
}
}
}
case 1:
{
lean_object* v_pos_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_pos_652_ = lean_ctor_get(v_searcher_613_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_searcher_613_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v_searcher_613_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_pos_652_);
lean_dec(v_searcher_613_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_string_utf8_next_fast(v___x_599_, v_pos_652_);
lean_dec(v_pos_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v_it_618_ = v___x_658_;
goto v___jp_617_;
}
}
}
case 2:
{
lean_object* v_needle_661_; lean_object* v_table_662_; lean_object* v_stackPos_663_; lean_object* v_needlePos_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_716_; 
v_needle_661_ = lean_ctor_get(v_searcher_613_, 0);
v_table_662_ = lean_ctor_get(v_searcher_613_, 1);
v_stackPos_663_ = lean_ctor_get(v_searcher_613_, 2);
v_needlePos_664_ = lean_ctor_get(v_searcher_613_, 3);
v_isSharedCheck_716_ = !lean_is_exclusive(v_searcher_613_);
if (v_isSharedCheck_716_ == 0)
{
v___x_666_ = v_searcher_613_;
v_isShared_667_ = v_isSharedCheck_716_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_needlePos_664_);
lean_inc(v_stackPos_663_);
lean_inc(v_table_662_);
lean_inc(v_needle_661_);
lean_dec(v_searcher_613_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_716_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_str_668_; lean_object* v_startInclusive_669_; lean_object* v_endExclusive_670_; lean_object* v_basePos_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_str_668_ = lean_ctor_get(v_needle_661_, 0);
v_startInclusive_669_ = lean_ctor_get(v_needle_661_, 1);
v_endExclusive_670_ = lean_ctor_get(v_needle_661_, 2);
v_basePos_671_ = lean_nat_sub(v_stackPos_663_, v_needlePos_664_);
v___x_672_ = lean_nat_sub(v_endExclusive_670_, v_startInclusive_669_);
v___x_673_ = lean_nat_add(v_basePos_671_, v___x_672_);
v___x_674_ = lean_nat_dec_le(v___x_673_, v___x_601_);
lean_dec(v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
lean_dec(v___x_672_);
lean_del_object(v___x_666_);
lean_dec(v_needlePos_664_);
lean_dec(v_stackPos_663_);
lean_dec_ref(v_table_662_);
lean_dec_ref(v_needle_661_);
v___x_675_ = lean_nat_dec_lt(v_basePos_671_, v___x_601_);
lean_dec(v_basePos_671_);
if (v___x_675_ == 0)
{
lean_del_object(v___x_615_);
goto v___jp_637_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_box(3);
v_it_618_ = v___x_676_;
goto v___jp_617_;
}
}
else
{
uint8_t v_stackByte_677_; lean_object* v___x_678_; uint8_t v_patByte_679_; uint8_t v___x_680_; 
lean_dec(v_basePos_671_);
lean_inc(v_stackPos_663_);
v_stackByte_677_ = lean_string_get_byte_fast(v___x_599_, v_stackPos_663_);
v___x_678_ = lean_nat_add(v_startInclusive_669_, v_needlePos_664_);
v_patByte_679_ = lean_string_get_byte_fast(v_str_668_, v___x_678_);
v___x_680_ = lean_uint8_dec_eq(v_stackByte_677_, v_patByte_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
lean_dec(v___x_672_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v_needlePos_664_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_newNeedlePos_685_; uint8_t v___x_686_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_sub(v_needlePos_664_, v___x_683_);
lean_dec(v_needlePos_664_);
v_newNeedlePos_685_ = lean_array_fget_borrowed(v_table_662_, v___x_684_);
lean_dec(v___x_684_);
v___x_686_ = lean_nat_dec_eq(v_newNeedlePos_685_, v___x_681_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; 
lean_inc(v_newNeedlePos_685_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v_newNeedlePos_685_);
v___x_688_ = v___x_666_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_needle_661_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_table_662_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_stackPos_663_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_newNeedlePos_685_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_it_618_ = v___x_688_;
goto v___jp_617_;
}
}
else
{
lean_object* v_nextStackPos_690_; lean_object* v___x_692_; 
v_nextStackPos_690_ = l_String_Slice_posGE___redArg(v___x_600_, v_stackPos_663_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v___x_681_);
lean_ctor_set(v___x_666_, 2, v_nextStackPos_690_);
v___x_692_ = v___x_666_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_needle_661_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_table_662_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_nextStackPos_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v___x_681_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_it_618_ = v___x_692_;
goto v___jp_617_;
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_nextStackPos_696_; lean_object* v___x_698_; 
lean_dec(v_needlePos_664_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_stackPos_663_, v___x_694_);
lean_dec(v_stackPos_663_);
v_nextStackPos_696_ = l_String_Slice_posGE___redArg(v___x_600_, v___x_695_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v___x_681_);
lean_ctor_set(v___x_666_, 2, v_nextStackPos_696_);
v___x_698_ = v___x_666_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_needle_661_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_table_662_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_nextStackPos_696_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___x_681_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_it_618_ = v___x_698_;
goto v___jp_617_;
}
}
}
else
{
lean_object* v___x_700_; lean_object* v_nextStackPos_701_; lean_object* v_nextNeedlePos_702_; uint8_t v___x_703_; 
lean_del_object(v___x_615_);
v___x_700_ = lean_unsigned_to_nat(1u);
v_nextStackPos_701_ = lean_nat_add(v_stackPos_663_, v___x_700_);
lean_dec(v_stackPos_663_);
v_nextNeedlePos_702_ = lean_nat_add(v_needlePos_664_, v___x_700_);
lean_dec(v_needlePos_664_);
v___x_703_ = lean_nat_dec_eq(v_nextNeedlePos_702_, v___x_672_);
lean_dec(v___x_672_);
if (v___x_703_ == 0)
{
lean_object* v___x_705_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v_nextNeedlePos_702_);
lean_ctor_set(v___x_666_, 2, v_nextStackPos_701_);
v___x_705_ = v___x_666_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_needle_661_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_table_662_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_nextStackPos_701_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_nextNeedlePos_702_);
v___x_705_ = v_reuseFailAlloc_708_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_currPos_612_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v_a_602_ = v___x_706_;
goto _start;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_709_ = lean_nat_sub(v_nextStackPos_701_, v_nextNeedlePos_702_);
lean_dec(v_nextNeedlePos_702_);
v___x_710_ = l_String_Slice_pos_x21(v___x_600_, v___x_709_);
lean_dec(v___x_709_);
v___x_711_ = l_String_Slice_pos_x21(v___x_600_, v_nextStackPos_701_);
v___x_712_ = lean_unsigned_to_nat(0u);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 3, v___x_712_);
lean_ctor_set(v___x_666_, 2, v_nextStackPos_701_);
v___x_714_ = v___x_666_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_needle_661_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_table_662_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_nextStackPos_701_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_it_624_ = v___x_714_;
v_startPos_625_ = v___x_710_;
v_endPos_626_ = v___x_711_;
goto v___jp_623_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_615_);
goto v___jp_637_;
}
}
v___jp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v_it_618_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_currPos_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_it_618_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v_a_602_ = v___x_620_;
goto _start;
}
}
v___jp_623_:
{
lean_object* v_slice_627_; lean_object* v_startInclusive_628_; lean_object* v_endExclusive_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_slice_627_ = l_String_Slice_subslice_x21(v___x_600_, v_currPos_612_, v_startPos_625_);
v_startInclusive_628_ = lean_ctor_get(v_slice_627_, 0);
v_endExclusive_629_ = lean_ctor_get(v_slice_627_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_slice_627_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v_slice_627_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_endExclusive_629_);
lean_inc(v_startInclusive_628_);
lean_dec(v_slice_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_nextIt_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_it_624_);
lean_ctor_set(v___x_631_, 0, v_endPos_626_);
v_nextIt_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_endPos_626_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_it_624_);
v_nextIt_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_it_605_ = v_nextIt_634_;
v_startInclusive_606_ = v_startInclusive_628_;
v_endExclusive_607_ = v_endExclusive_629_;
goto v___jp_604_;
}
}
}
v___jp_637_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_box(1);
lean_inc(v___x_601_);
v_it_605_ = v___x_638_;
v_startInclusive_606_ = v_currPos_612_;
v_endExclusive_607_ = v___x_601_;
goto v___jp_604_;
}
}
}
else
{
lean_dec(v___x_601_);
lean_dec_ref(v___x_599_);
return v_b_603_;
}
v___jp_604_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc_ref(v___x_599_);
v___x_608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_599_);
lean_ctor_set(v___x_608_, 1, v_startInclusive_606_);
lean_ctor_set(v___x_608_, 2, v_endExclusive_607_);
v___x_609_ = l_String_Slice_toString(v___x_608_);
lean_dec_ref_known(v___x_608_, 3);
v___x_610_ = lean_array_push(v_b_603_, v___x_609_);
v_a_602_ = v_it_605_;
v_b_603_ = v___x_610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v_a_721_, lean_object* v_b_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_718_, v___x_719_, v___x_720_, v_a_721_, v_b_722_);
lean_dec_ref(v___x_719_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_727_ = l_System_FilePath_normalize(v_p_726_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_string_utf8_byte_size(v___x_727_);
lean_inc_ref(v___x_727_);
v___x_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_730_, 0, v___x_727_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_729_);
v___x_731_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_730_);
v___x_732_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_733_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_727_, v___x_730_, v___x_729_, v___x_731_, v___x_732_);
lean_dec_ref_known(v___x_730_, 3);
v___x_734_ = lean_array_to_list(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v___x_737_, lean_object* v_inst_738_, lean_object* v_R_739_, lean_object* v_a_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_735_, v___x_736_, v___x_737_, v_a_740_, v_b_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_inst_746_, lean_object* v_R_747_, lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_743_, v___x_744_, v___x_745_, v_inst_746_, v_R_747_, v_a_748_, v_b_749_);
lean_dec_ref(v___x_744_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_753_ = l_String_intercalate(v___x_752_, v_parts_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_754_){
_start:
{
lean_inc_ref(v_toString_754_);
return v_toString_754_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_System_instCoeStringFilePath___lam__0(v_toString_755_);
lean_dec_ref(v_toString_755_);
return v_res_756_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = l_System_Platform_isWindows;
if (v___x_759_ == 0)
{
uint32_t v___x_760_; 
v___x_760_ = 58;
return v___x_760_;
}
else
{
uint32_t v___x_761_; 
v___x_761_ = 59;
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0));
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
lean_object* v_currPos_780_; lean_object* v_searcher_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_807_; 
v_currPos_780_ = lean_ctor_get(v_a_771_, 0);
v_searcher_781_ = lean_ctor_get(v_a_771_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_807_ == 0)
{
v___x_783_ = v_a_771_;
v_isShared_784_ = v_isSharedCheck_807_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_searcher_781_);
lean_inc(v_currPos_780_);
lean_dec(v_a_771_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_807_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_startInclusive_785_; lean_object* v_endExclusive_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_startInclusive_785_ = lean_ctor_get(v___x_769_, 1);
v_endExclusive_786_ = lean_ctor_get(v___x_769_, 2);
v___x_787_ = lean_nat_sub(v_endExclusive_786_, v_startInclusive_785_);
v___x_788_ = lean_nat_dec_eq(v_searcher_781_, v___x_787_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
uint32_t v___x_789_; uint32_t v___x_790_; uint8_t v___x_791_; 
v___x_789_ = l_System_SearchPath_separator;
v___x_790_ = lean_string_utf8_get_fast(v_s_768_, v_searcher_781_);
v___x_791_ = lean_uint32_dec_eq(v___x_790_, v___x_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_string_utf8_next_fast(v_s_768_, v_searcher_781_);
lean_dec(v_searcher_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_792_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_currPos_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v_a_771_ = v___x_794_;
goto _start;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_slice_800_; lean_object* v_nextIt_802_; 
v___x_797_ = lean_string_utf8_next_fast(v_s_768_, v_searcher_781_);
v___x_798_ = lean_nat_sub(v___x_797_, v_searcher_781_);
v___x_799_ = lean_nat_add(v_searcher_781_, v___x_798_);
lean_dec(v___x_798_);
v_slice_800_ = l_String_Slice_subslice_x21(v___x_769_, v_currPos_780_, v_searcher_781_);
lean_inc(v___x_799_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_799_);
lean_ctor_set(v___x_783_, 0, v___x_799_);
v_nextIt_802_ = v___x_783_;
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
v_it_774_ = v_nextIt_802_;
v_startInclusive_775_ = v_startInclusive_803_;
v_endExclusive_776_ = v_endExclusive_804_;
goto v___jp_773_;
}
}
}
else
{
lean_object* v___x_806_; 
lean_del_object(v___x_783_);
lean_dec(v_searcher_781_);
v___x_806_ = lean_box(1);
lean_inc(v___x_770_);
v_it_774_ = v___x_806_;
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
v___x_777_ = lean_string_utf8_extract(v_s_768_, v_startInclusive_775_, v_endExclusive_776_);
lean_dec(v_endExclusive_776_);
lean_dec(v_startInclusive_775_);
v___x_778_ = lean_array_push(v_b_772_, v___x_777_);
v_a_771_ = v_it_774_;
v_b_772_ = v___x_778_;
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
v___x_818_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_817_);
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
