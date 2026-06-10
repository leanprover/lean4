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
static const lean_array_object l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object* v_p_100_){
_start:
{
uint8_t v___y_102_; uint8_t v___x_114_; 
v___x_114_ = l_System_Platform_isWindows;
if (v___x_114_ == 0)
{
return v_p_100_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_string_utf8_byte_size(v_p_100_);
lean_inc_ref(v_p_100_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_p_100_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
v___x_118_ = l_String_Slice_positions(v___x_117_);
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
v___x_121_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0));
v___x_122_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_117_, v_p_100_, v___x_120_, v___x_121_);
lean_dec_ref_known(v___x_117_, 3);
v___x_123_ = lean_array_to_list(v___x_122_);
if (lean_obj_tag(v___x_123_) == 1)
{
lean_object* v_tail_124_; 
v_tail_124_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_tail_124_);
if (lean_obj_tag(v_tail_124_) == 1)
{
lean_object* v_head_125_; lean_object* v_head_126_; lean_object* v_tail_127_; uint32_t v___x_128_; uint32_t v___x_129_; uint8_t v___x_130_; 
v_head_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_head_125_);
lean_dec_ref_known(v___x_123_, 2);
v_head_126_ = lean_ctor_get(v_tail_124_, 0);
lean_inc(v_head_126_);
v_tail_127_ = lean_ctor_get(v_tail_124_, 1);
lean_inc(v_tail_127_);
lean_dec_ref_known(v_tail_124_, 2);
v___x_128_ = 58;
v___x_129_ = lean_unbox_uint32(v_head_126_);
lean_dec(v_head_126_);
v___x_130_ = lean_uint32_dec_eq(v___x_129_, v___x_128_);
if (v___x_130_ == 0)
{
lean_dec(v_tail_127_);
lean_dec(v_head_125_);
return v_p_100_;
}
else
{
if (lean_obj_tag(v_tail_127_) == 0)
{
uint32_t v___x_131_; uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = 97;
v___x_132_ = lean_unbox_uint32(v_head_125_);
v___x_133_ = lean_uint32_dec_le(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v_head_125_);
v___y_102_ = v___x_133_;
goto v___jp_101_;
}
else
{
uint32_t v___x_134_; uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = 122;
v___x_135_ = lean_unbox_uint32(v_head_125_);
lean_dec(v_head_125_);
v___x_136_ = lean_uint32_dec_le(v___x_135_, v___x_134_);
v___y_102_ = v___x_136_;
goto v___jp_101_;
}
}
else
{
lean_dec(v_tail_127_);
lean_dec(v_head_125_);
return v_p_100_;
}
}
}
else
{
lean_dec(v_tail_124_);
lean_dec_ref_known(v___x_123_, 2);
return v_p_100_;
}
}
else
{
lean_dec(v___x_123_);
return v_p_100_;
}
}
v___jp_101_:
{
if (v___y_102_ == 0)
{
return v_p_100_;
}
else
{
lean_object* v___x_103_; uint32_t v___x_104_; uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_string_utf8_get(v_p_100_, v___x_103_);
v___x_105_ = 97;
v___x_106_ = lean_uint32_dec_le(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_string_utf8_set(v_p_100_, v___x_103_, v___x_104_);
return v___x_107_;
}
else
{
uint32_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 122;
v___x_109_ = lean_uint32_dec_le(v___x_104_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_string_utf8_set(v_p_100_, v___x_103_, v___x_104_);
return v___x_110_;
}
else
{
uint32_t v___x_111_; uint32_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = 4294967264;
v___x_112_ = lean_uint32_add(v___x_104_, v___x_111_);
v___x_113_ = lean_string_utf8_set(v_p_100_, v___x_103_, v___x_112_);
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v_inst_139_, lean_object* v_R_140_, lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_137_, v___x_138_, v_a_141_, v_b_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_144_, lean_object* v___x_145_, lean_object* v_inst_146_, lean_object* v_R_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_144_, v___x_145_, v_inst_146_, v_R_147_, v_a_148_, v_b_149_);
lean_dec_ref(v___x_145_);
lean_dec_ref(v___x_144_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v_head_154_ = lean_ctor_get(v_x_152_, 0);
v_tail_155_ = lean_ctor_get(v_x_152_, 1);
v___x_156_ = lean_unbox_uint32(v_head_154_);
v___x_157_ = lean_uint32_dec_eq(v_a_151_, v___x_156_);
if (v___x_157_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_159_, lean_object* v_x_160_){
_start:
{
uint32_t v_a_boxed_161_; uint8_t v_res_162_; lean_object* v_r_163_; 
v_a_boxed_161_ = lean_unbox_uint32(v_a_159_);
lean_dec(v_a_159_);
v_res_162_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_161_, v_x_160_);
lean_dec(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_164_, lean_object* v_p_165_){
_start:
{
uint32_t v___y_167_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_string_utf8_byte_size(v_s_164_);
v___x_173_ = lean_nat_dec_eq(v_p_165_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; uint32_t v___x_175_; uint8_t v___x_176_; 
v___x_174_ = l_System_FilePath_pathSeparators;
v___x_175_ = lean_string_utf8_get_fast(v_s_164_, v_p_165_);
v___x_176_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_175_, v___x_174_);
if (v___x_176_ == 0)
{
v___y_167_ = v___x_175_;
goto v___jp_166_;
}
else
{
uint32_t v___x_177_; 
v___x_177_ = l_System_FilePath_pathSeparator;
v___y_167_ = v___x_177_;
goto v___jp_166_;
}
}
else
{
lean_dec(v_p_165_);
return v_s_164_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_inc(v_p_165_);
v___x_168_ = lean_string_utf8_set(v_s_164_, v_p_165_, v___y_167_);
v___x_169_ = l_Char_utf8Size(v___y_167_);
v___x_170_ = lean_nat_add(v_p_165_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v_p_165_);
v_s_164_ = v___x_168_;
v_p_165_ = v___x_170_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = l_System_FilePath_pathSeparators;
v___x_179_ = l_List_lengthTR___redArg(v___x_178_);
return v___x_179_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_182_ = lean_nat_dec_eq(v___x_181_, v___x_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_183_){
_start:
{
lean_object* v_p_184_; uint8_t v___x_185_; 
v_p_184_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_183_);
v___x_185_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v_p_187_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v_p_187_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_184_, v___x_186_);
return v_p_187_;
}
else
{
return v_p_184_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
if (lean_obj_tag(v_x_189_) == 0)
{
uint8_t v___x_190_; 
v___x_190_ = 1;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
else
{
if (lean_obj_tag(v_x_189_) == 0)
{
uint8_t v___x_192_; 
v___x_192_ = 0;
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v_val_194_; uint32_t v___x_195_; uint32_t v___x_196_; uint8_t v___x_197_; 
v_val_193_ = lean_ctor_get(v_x_188_, 0);
v_val_194_ = lean_ctor_get(v_x_189_, 0);
v___x_195_ = lean_unbox_uint32(v_val_193_);
v___x_196_ = lean_unbox_uint32(v_val_194_);
v___x_197_ = lean_uint32_dec_eq(v___x_195_, v___x_196_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_198_, v_x_199_);
lean_dec(v_x_199_);
lean_dec(v_x_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v_str_206_; lean_object* v_startInclusive_207_; lean_object* v_endExclusive_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_str_206_ = lean_ctor_get(v___x_203_, 0);
v_startInclusive_207_ = lean_ctor_get(v___x_203_, 1);
v_endExclusive_208_ = lean_ctor_get(v___x_203_, 2);
v___x_209_ = lean_nat_sub(v_endExclusive_208_, v_startInclusive_207_);
v___x_210_ = lean_nat_dec_eq(v_a_204_, v___x_209_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v_zero_211_; uint8_t v_isZero_212_; 
v_zero_211_ = lean_unsigned_to_nat(0u);
v_isZero_212_ = lean_nat_dec_eq(v_b_205_, v_zero_211_);
if (v_isZero_212_ == 1)
{
uint32_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_b_205_);
v___x_213_ = lean_string_utf8_get_fast(v___x_202_, v_a_204_);
lean_dec(v_a_204_);
v___x_214_ = lean_box_uint32(v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_one_219_; lean_object* v_n_220_; 
v___x_216_ = lean_nat_add(v_startInclusive_207_, v_a_204_);
lean_dec(v_a_204_);
v___x_217_ = lean_string_utf8_next_fast(v_str_206_, v___x_216_);
lean_dec(v___x_216_);
v___x_218_ = lean_nat_sub(v___x_217_, v_startInclusive_207_);
v_one_219_ = lean_unsigned_to_nat(1u);
v_n_220_ = lean_nat_sub(v_b_205_, v_one_219_);
lean_dec(v_b_205_);
v_a_204_ = v___x_218_;
v_b_205_ = v_n_220_;
goto _start;
}
}
else
{
lean_object* v___x_222_; 
lean_dec(v_b_205_);
lean_dec(v_a_204_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_223_, v___x_224_, v_a_225_, v_b_226_);
lean_dec_ref(v___x_224_);
lean_dec_ref(v___x_223_);
return v_res_227_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_228_; lean_object* v___x_229_; 
v___x_228_ = 58;
v___x_229_ = lean_box_uint32(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_232_){
_start:
{
lean_object* v___x_233_; uint32_t v___y_235_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_233_ = l_System_FilePath_pathSeparators;
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_string_utf8_byte_size(v_p_232_);
lean_inc_ref(v_p_232_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v_p_232_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
v___x_249_ = l_String_Slice_Pos_get_x3f(v___x_248_, v___x_246_);
lean_dec_ref_known(v___x_248_, 3);
if (lean_obj_tag(v___x_249_) == 0)
{
uint32_t v___x_250_; 
v___x_250_ = 65;
v___y_235_ = v___x_250_;
goto v___jp_234_;
}
else
{
lean_object* v_val_251_; uint32_t v___x_252_; 
v_val_251_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v___x_249_, 1);
v___x_252_ = lean_unbox_uint32(v_val_251_);
lean_dec(v_val_251_);
v___y_235_ = v___x_252_;
goto v___jp_234_;
}
v___jp_234_:
{
uint8_t v___x_236_; 
v___x_236_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_235_, v___x_233_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; 
v___x_237_ = l_System_Platform_isWindows;
if (v___x_237_ == 0)
{
lean_dec_ref(v_p_232_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_string_utf8_byte_size(v_p_232_);
lean_inc_ref(v_p_232_);
v___x_240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_240_, 0, v_p_232_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = l_String_Slice_positions(v___x_240_);
v___x_243_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_232_, v___x_240_, v___x_242_, v___x_241_);
lean_dec_ref_known(v___x_240_, 3);
lean_dec_ref(v_p_232_);
v___x_244_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_245_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_243_, v___x_244_);
lean_dec(v___x_243_);
return v___x_245_;
}
}
else
{
lean_dec_ref(v_p_232_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_System_FilePath_isAbsolute(v_p_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v_n_258_, lean_object* v_it_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_257_, v___x_256_, v_it_259_, v_n_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_261_, lean_object* v___x_262_, lean_object* v_n_263_, lean_object* v_it_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_261_, v___x_262_, v_n_263_, v_it_264_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v___x_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v_inst_268_, lean_object* v_R_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_266_, v___x_267_, v_a_270_, v_b_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_273_, v___x_274_, v_inst_275_, v_R_276_, v_a_277_, v_b_278_);
lean_dec_ref(v___x_274_);
lean_dec_ref(v___x_273_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_System_FilePath_isAbsolute(v_p_280_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; 
v___x_282_ = 1;
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
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
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_dec_eq(v_a_300_, v___x_302_);
if (v___x_303_ == 0)
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
lean_inc(v_val_417_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_utf8_extract(v_p_383_, v___x_418_, v_val_417_);
lean_dec(v_val_417_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___y_396_ = v___x_420_;
goto v___jp_395_;
}
v___jp_384_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
lean_inc(v___y_385_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___y_385_);
v___x_390_ = l_Option_instDecidableEq___redArg(v___y_387_, v___y_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v___y_385_);
lean_dec_ref(v_p_383_);
return v___y_386_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v___y_386_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_string_utf8_extract(v_p_383_, v___x_391_, v___y_385_);
lean_dec(v___y_385_);
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
lean_object* v_afterRootDirectory_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
lean_inc_ref(v_p_383_);
v_afterRootDirectory_398_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_383_);
v___x_399_ = lean_string_utf8_byte_size(v_p_383_);
v___x_400_ = lean_nat_dec_eq(v_afterRootDirectory_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_inc_ref(v_p_383_);
v___x_401_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_401_, 0, v_p_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
v___y_385_ = v_afterRootDirectory_398_;
v___y_386_ = v___y_396_;
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
v___y_385_ = v_afterRootDirectory_398_;
v___y_386_ = v___y_396_;
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
v___y_385_ = v_afterRootDirectory_398_;
v___y_386_ = v___y_396_;
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
lean_object* v___y_425_; uint8_t v___y_426_; lean_object* v___y_433_; lean_object* v___x_439_; 
lean_inc_ref(v_p_423_);
v___x_439_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_423_);
if (lean_obj_tag(v___x_439_) == 0)
{
v___y_433_ = v_p_423_;
goto v___jp_432_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_string_utf8_byte_size(v_p_423_);
lean_inc_ref(v_p_423_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v_p_423_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = l_String_Slice_Pos_next_x21(v___x_443_, v_val_440_);
lean_dec(v_val_440_);
lean_dec_ref_known(v___x_443_, 3);
v___x_445_ = lean_string_utf8_extract(v_p_423_, v___x_444_, v___x_442_);
lean_dec(v___x_444_);
lean_dec_ref(v_p_423_);
v___y_433_ = v___x_445_;
goto v___jp_432_;
}
v___jp_424_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_428_ = lean_string_dec_eq(v___y_425_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v___y_425_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
lean_dec_ref(v___y_425_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v___y_425_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_string_utf8_byte_size(v___y_433_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_nat_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_438_ = lean_string_dec_eq(v___y_433_, v___x_437_);
v___y_425_ = v___y_433_;
v___y_426_ = v___x_438_;
goto v___jp_424_;
}
else
{
v___y_425_ = v___y_433_;
v___y_426_ = v___x_436_;
goto v___jp_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_446_, lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v_a_447_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v_str_451_; lean_object* v_startInclusive_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint32_t v___x_460_; uint32_t v___x_461_; uint8_t v___x_462_; 
v_str_451_ = lean_ctor_get(v_s_446_, 0);
v_startInclusive_452_ = lean_ctor_get(v_s_446_, 1);
v___x_453_ = lean_nat_add(v_startInclusive_452_, v_a_447_);
lean_inc(v___x_453_);
lean_inc(v_startInclusive_452_);
lean_inc_ref(v_str_451_);
v___x_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_454_, 0, v_str_451_);
lean_ctor_set(v___x_454_, 1, v_startInclusive_452_);
lean_ctor_set(v___x_454_, 2, v___x_453_);
v___x_455_ = lean_nat_sub(v___x_453_, v_startInclusive_452_);
lean_dec(v___x_453_);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_sub(v___x_455_, v___x_456_);
lean_dec(v___x_455_);
v___x_458_ = l_String_Slice_posLE(v___x_454_, v___x_457_);
lean_dec_ref_known(v___x_454_, 3);
v___x_459_ = lean_nat_add(v_startInclusive_452_, v___x_458_);
v___x_460_ = lean_string_utf8_get_fast(v_str_451_, v___x_459_);
lean_dec(v___x_459_);
v___x_461_ = 46;
v___x_462_ = lean_uint32_dec_eq(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_458_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_nat_sub(v_a_447_, v___x_456_);
lean_dec(v_a_447_);
v___x_465_ = l_String_Slice_posLE(v_s_446_, v___x_464_);
v_a_447_ = v___x_465_;
v_b_448_ = v___x_463_;
goto _start;
}
else
{
lean_object* v___x_467_; 
lean_dec(v_a_447_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_458_);
return v___x_467_;
}
}
else
{
lean_dec(v_a_447_);
lean_inc(v_b_448_);
return v_b_448_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_468_, lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_468_, v_a_469_, v_b_470_);
lean_dec(v_b_470_);
lean_dec_ref(v_s_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_472_){
_start:
{
lean_object* v_startInclusive_473_; lean_object* v_endExclusive_474_; lean_object* v_searcher_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_startInclusive_473_ = lean_ctor_get(v_s_472_, 1);
v_endExclusive_474_ = lean_ctor_get(v_s_472_, 2);
v_searcher_475_ = lean_nat_sub(v_endExclusive_474_, v_startInclusive_473_);
v___x_476_ = lean_box(0);
v___x_477_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_472_, v_searcher_475_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_478_);
lean_dec_ref(v_s_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_System_FilePath_fileName(v_p_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
return v___x_481_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_n(v_val_482_, 2);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_string_utf8_byte_size(v_val_482_);
v___x_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_485_, 0, v_val_482_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
lean_ctor_set(v___x_485_, 2, v___x_484_);
v___x_486_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_485_);
lean_dec_ref_known(v___x_485_, 3);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec(v_val_482_);
return v___x_481_;
}
else
{
lean_object* v_val_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_496_; 
v_val_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_val_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; 
v___x_491_ = lean_nat_dec_eq(v_val_487_, v___x_483_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_492_ = lean_string_utf8_extract(v_val_482_, v___x_483_, v_val_487_);
lean_dec(v_val_487_);
lean_dec(v_val_482_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_del_object(v___x_489_);
lean_dec(v_val_487_);
lean_dec(v_val_482_);
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_497_, lean_object* v_inst_498_, lean_object* v_R_499_, lean_object* v_a_500_, lean_object* v_b_501_, lean_object* v_c_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_497_, v_a_500_, v_b_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_504_, lean_object* v_inst_505_, lean_object* v_R_506_, lean_object* v_a_507_, lean_object* v_b_508_, lean_object* v_c_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_504_, v_inst_505_, v_R_506_, v_a_507_, v_b_508_, v_c_509_);
lean_dec(v_b_508_);
lean_dec_ref(v_s_504_);
return v_res_510_;
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0(void){
_start:
{
uint32_t v___x_511_; lean_object* v___x_512_; 
v___x_511_ = 46;
v___x_512_ = l_Char_utf8Size(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_System_FilePath_fileName(v_p_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
return v___x_514_;
}
else
{
lean_object* v_val_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_val_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_n(v_val_515_, 2);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_string_utf8_byte_size(v_val_515_);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v_val_515_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
v___x_519_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_518_);
lean_dec_ref_known(v___x_518_, 3);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
lean_dec(v_val_515_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_val_521_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_533_ == 0)
{
v___x_523_ = v___x_519_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v___x_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_eq(v_val_521_, v___x_516_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_526_ = lean_obj_once(&l_System_FilePath_extension___closed__0, &l_System_FilePath_extension___closed__0_once, _init_l_System_FilePath_extension___closed__0);
v___x_527_ = lean_nat_add(v_val_521_, v___x_526_);
lean_dec(v_val_521_);
v___x_528_ = lean_string_utf8_extract(v_val_515_, v___x_527_, v___x_517_);
lean_dec(v___x_527_);
lean_dec(v_val_515_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_528_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v___x_532_; 
lean_del_object(v___x_523_);
lean_dec(v_val_521_);
lean_dec(v_val_515_);
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_534_, lean_object* v_fname_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_System_FilePath_parent(v_p_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
return v_fname_535_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
v_val_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = l_System_FilePath_join(v_val_537_, v_fname_535_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_539_, lean_object* v_ext_540_){
_start:
{
lean_object* v___x_541_; 
lean_inc_ref(v_p_539_);
v___x_541_ = l_System_FilePath_fileName(v_p_539_);
if (lean_obj_tag(v___x_541_) == 0)
{
return v_p_539_;
}
else
{
lean_object* v_val_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_val_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = lean_string_utf8_byte_size(v_ext_540_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_nat_dec_eq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_547_ = lean_string_append(v_val_542_, v___x_546_);
v___x_548_ = lean_string_append(v___x_547_, v_ext_540_);
v___x_549_ = l_System_FilePath_withFileName(v_p_539_, v___x_548_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = l_System_FilePath_withFileName(v_p_539_, v_val_542_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_551_, lean_object* v_ext_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_System_FilePath_addExtension(v_p_551_, v_ext_552_);
lean_dec_ref(v_ext_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_554_, lean_object* v_ext_555_){
_start:
{
lean_object* v___x_556_; 
lean_inc_ref(v_p_554_);
v___x_556_ = l_System_FilePath_fileStem(v_p_554_);
if (lean_obj_tag(v___x_556_) == 0)
{
return v_p_554_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_string_utf8_byte_size(v_ext_555_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_nat_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_562_ = lean_string_append(v_val_557_, v___x_561_);
v___x_563_ = lean_string_append(v___x_562_, v_ext_555_);
v___x_564_ = l_System_FilePath_withFileName(v_p_554_, v___x_563_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = l_System_FilePath_withFileName(v_p_554_, v_val_557_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_566_, lean_object* v_ext_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_System_FilePath_withExtension(v_p_566_, v_ext_567_);
lean_dec_ref(v_ext_567_);
return v_res_568_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_570_ = lean_string_utf8_byte_size(v___x_569_);
return v___x_570_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_573_ = lean_nat_dec_eq(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_574_);
return v___x_577_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_579_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
v___x_582_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_583_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
lean_ctor_set(v___x_583_, 3, v___x_580_);
return v___x_583_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
return v___x_594_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7));
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_596_);
lean_dec_ref(v_s_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_it_604_; lean_object* v_startInclusive_605_; lean_object* v_endExclusive_606_; 
if (lean_obj_tag(v_a_601_) == 0)
{
lean_object* v_currPos_611_; lean_object* v_searcher_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_716_; 
v_currPos_611_ = lean_ctor_get(v_a_601_, 0);
v_searcher_612_ = lean_ctor_get(v_a_601_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_716_ == 0)
{
v___x_614_ = v_a_601_;
v_isShared_615_ = v_isSharedCheck_716_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_searcher_612_);
lean_inc(v_currPos_611_);
lean_dec(v_a_601_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_716_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_it_617_; lean_object* v_it_623_; lean_object* v_startPos_624_; lean_object* v_endPos_625_; 
switch(lean_obj_tag(v_searcher_612_))
{
case 0:
{
lean_object* v_pos_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_614_);
v_pos_638_ = lean_ctor_get(v_searcher_612_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_searcher_612_);
if (v_isSharedCheck_650_ == 0)
{
v___x_640_ = v_searcher_612_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_pos_638_);
lean_dec(v_searcher_612_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_startInclusive_642_; lean_object* v_endExclusive_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_startInclusive_642_ = lean_ctor_get(v___x_599_, 1);
v_endExclusive_643_ = lean_ctor_get(v___x_599_, 2);
v___x_644_ = lean_nat_sub(v_endExclusive_643_, v_startInclusive_642_);
v___x_645_ = lean_nat_dec_eq(v_pos_638_, v___x_644_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
lean_inc(v_pos_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 1);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_pos_638_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_inc(v_pos_638_);
v_it_623_ = v___x_647_;
v_startPos_624_ = v_pos_638_;
v_endPos_625_ = v_pos_638_;
goto v___jp_622_;
}
}
else
{
lean_object* v___x_649_; 
lean_del_object(v___x_640_);
v___x_649_ = lean_box(3);
lean_inc(v_pos_638_);
v_it_623_ = v___x_649_;
v_startPos_624_ = v_pos_638_;
v_endPos_625_ = v_pos_638_;
goto v___jp_622_;
}
}
}
case 1:
{
lean_object* v_pos_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v_pos_651_ = lean_ctor_get(v_searcher_612_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_searcher_612_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v_searcher_612_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_pos_651_);
lean_dec(v_searcher_612_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = lean_string_utf8_next_fast(v___x_598_, v_pos_651_);
lean_dec(v_pos_651_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
v_it_617_ = v___x_657_;
goto v___jp_616_;
}
}
}
case 2:
{
lean_object* v_needle_660_; lean_object* v_table_661_; lean_object* v_stackPos_662_; lean_object* v_needlePos_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_715_; 
v_needle_660_ = lean_ctor_get(v_searcher_612_, 0);
v_table_661_ = lean_ctor_get(v_searcher_612_, 1);
v_stackPos_662_ = lean_ctor_get(v_searcher_612_, 2);
v_needlePos_663_ = lean_ctor_get(v_searcher_612_, 3);
v_isSharedCheck_715_ = !lean_is_exclusive(v_searcher_612_);
if (v_isSharedCheck_715_ == 0)
{
v___x_665_ = v_searcher_612_;
v_isShared_666_ = v_isSharedCheck_715_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_needlePos_663_);
lean_inc(v_stackPos_662_);
lean_inc(v_table_661_);
lean_inc(v_needle_660_);
lean_dec(v_searcher_612_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_715_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_str_667_; lean_object* v_startInclusive_668_; lean_object* v_endExclusive_669_; lean_object* v_basePos_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_str_667_ = lean_ctor_get(v_needle_660_, 0);
v_startInclusive_668_ = lean_ctor_get(v_needle_660_, 1);
v_endExclusive_669_ = lean_ctor_get(v_needle_660_, 2);
v_basePos_670_ = lean_nat_sub(v_stackPos_662_, v_needlePos_663_);
v___x_671_ = lean_nat_sub(v_endExclusive_669_, v_startInclusive_668_);
v___x_672_ = lean_nat_add(v_basePos_670_, v___x_671_);
v___x_673_ = lean_nat_dec_le(v___x_672_, v___x_600_);
lean_dec(v___x_672_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
lean_dec(v___x_671_);
lean_del_object(v___x_665_);
lean_dec(v_needlePos_663_);
lean_dec(v_stackPos_662_);
lean_dec_ref(v_table_661_);
lean_dec_ref(v_needle_660_);
v___x_674_ = lean_nat_dec_lt(v_basePos_670_, v___x_600_);
lean_dec(v_basePos_670_);
if (v___x_674_ == 0)
{
lean_del_object(v___x_614_);
goto v___jp_636_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(3);
v_it_617_ = v___x_675_;
goto v___jp_616_;
}
}
else
{
uint8_t v_stackByte_676_; lean_object* v___x_677_; uint8_t v_patByte_678_; uint8_t v___x_679_; 
lean_dec(v_basePos_670_);
lean_inc(v_stackPos_662_);
v_stackByte_676_ = lean_string_get_byte_fast(v___x_598_, v_stackPos_662_);
v___x_677_ = lean_nat_add(v_startInclusive_668_, v_needlePos_663_);
v_patByte_678_ = lean_string_get_byte_fast(v_str_667_, v___x_677_);
v___x_679_ = lean_uint8_dec_eq(v_stackByte_676_, v_patByte_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; uint8_t v___x_681_; 
lean_dec(v___x_671_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_nat_dec_eq(v_needlePos_663_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_newNeedlePos_684_; uint8_t v___x_685_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v_needlePos_663_, v___x_682_);
lean_dec(v_needlePos_663_);
v_newNeedlePos_684_ = lean_array_fget_borrowed(v_table_661_, v___x_683_);
lean_dec(v___x_683_);
v___x_685_ = lean_nat_dec_eq(v_newNeedlePos_684_, v___x_680_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
lean_inc(v_newNeedlePos_684_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v_newNeedlePos_684_);
v___x_687_ = v___x_665_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_needle_660_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_table_661_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_stackPos_662_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_newNeedlePos_684_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v_it_617_ = v___x_687_;
goto v___jp_616_;
}
}
else
{
lean_object* v_nextStackPos_689_; lean_object* v___x_691_; 
v_nextStackPos_689_ = l_String_Slice_posGE___redArg(v___x_599_, v_stackPos_662_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v___x_680_);
lean_ctor_set(v___x_665_, 2, v_nextStackPos_689_);
v___x_691_ = v___x_665_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_needle_660_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_table_661_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_nextStackPos_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v___x_680_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_it_617_ = v___x_691_;
goto v___jp_616_;
}
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_nextStackPos_695_; lean_object* v___x_697_; 
lean_dec(v_needlePos_663_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_stackPos_662_, v___x_693_);
lean_dec(v_stackPos_662_);
v_nextStackPos_695_ = l_String_Slice_posGE___redArg(v___x_599_, v___x_694_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v___x_680_);
lean_ctor_set(v___x_665_, 2, v_nextStackPos_695_);
v___x_697_ = v___x_665_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_needle_660_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_table_661_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_nextStackPos_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v___x_680_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_it_617_ = v___x_697_;
goto v___jp_616_;
}
}
}
else
{
lean_object* v___x_699_; lean_object* v_nextStackPos_700_; lean_object* v_nextNeedlePos_701_; uint8_t v___x_702_; 
lean_del_object(v___x_614_);
v___x_699_ = lean_unsigned_to_nat(1u);
v_nextStackPos_700_ = lean_nat_add(v_stackPos_662_, v___x_699_);
lean_dec(v_stackPos_662_);
v_nextNeedlePos_701_ = lean_nat_add(v_needlePos_663_, v___x_699_);
lean_dec(v_needlePos_663_);
v___x_702_ = lean_nat_dec_eq(v_nextNeedlePos_701_, v___x_671_);
lean_dec(v___x_671_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v_nextNeedlePos_701_);
lean_ctor_set(v___x_665_, 2, v_nextStackPos_700_);
v___x_704_ = v___x_665_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_needle_660_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_table_661_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_nextStackPos_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_nextNeedlePos_701_);
v___x_704_ = v_reuseFailAlloc_707_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_currPos_611_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v_a_601_ = v___x_705_;
goto _start;
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_708_ = lean_nat_sub(v_nextStackPos_700_, v_nextNeedlePos_701_);
lean_dec(v_nextNeedlePos_701_);
v___x_709_ = l_String_Slice_pos_x21(v___x_599_, v___x_708_);
lean_dec(v___x_708_);
v___x_710_ = l_String_Slice_pos_x21(v___x_599_, v_nextStackPos_700_);
v___x_711_ = lean_unsigned_to_nat(0u);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v___x_711_);
lean_ctor_set(v___x_665_, 2, v_nextStackPos_700_);
v___x_713_ = v___x_665_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_needle_660_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_table_661_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_nextStackPos_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v_it_623_ = v___x_713_;
v_startPos_624_ = v___x_709_;
v_endPos_625_ = v___x_710_;
goto v___jp_622_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_614_);
goto v___jp_636_;
}
}
v___jp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_it_617_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_currPos_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_it_617_);
v___x_619_ = v_reuseFailAlloc_621_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v_a_601_ = v___x_619_;
goto _start;
}
}
v___jp_622_:
{
lean_object* v_slice_626_; lean_object* v_startInclusive_627_; lean_object* v_endExclusive_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
v_slice_626_ = l_String_Slice_subslice_x21(v___x_599_, v_currPos_611_, v_startPos_624_);
v_startInclusive_627_ = lean_ctor_get(v_slice_626_, 0);
v_endExclusive_628_ = lean_ctor_get(v_slice_626_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_slice_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v_slice_626_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_endExclusive_628_);
lean_inc(v_startInclusive_627_);
lean_dec(v_slice_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_nextIt_633_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_it_623_);
lean_ctor_set(v___x_630_, 0, v_endPos_625_);
v_nextIt_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_endPos_625_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_it_623_);
v_nextIt_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
v_it_604_ = v_nextIt_633_;
v_startInclusive_605_ = v_startInclusive_627_;
v_endExclusive_606_ = v_endExclusive_628_;
goto v___jp_603_;
}
}
}
v___jp_636_:
{
lean_object* v___x_637_; 
v___x_637_ = lean_box(1);
lean_inc(v___x_600_);
v_it_604_ = v___x_637_;
v_startInclusive_605_ = v_currPos_611_;
v_endExclusive_606_ = v___x_600_;
goto v___jp_603_;
}
}
}
else
{
lean_dec(v___x_600_);
lean_dec_ref(v___x_598_);
return v_b_602_;
}
v___jp_603_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc_ref(v___x_598_);
v___x_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_598_);
lean_ctor_set(v___x_607_, 1, v_startInclusive_605_);
lean_ctor_set(v___x_607_, 2, v_endExclusive_606_);
v___x_608_ = l_String_Slice_toString(v___x_607_);
lean_dec_ref_known(v___x_607_, 3);
v___x_609_ = lean_array_push(v_b_602_, v___x_608_);
v_a_601_ = v_it_604_;
v_b_602_ = v___x_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_717_, v___x_718_, v___x_719_, v_a_720_, v_b_721_);
lean_dec_ref(v___x_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_726_ = l_System_FilePath_normalize(v_p_725_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_string_utf8_byte_size(v___x_726_);
lean_inc_ref(v___x_726_);
v___x_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_729_);
v___x_731_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_732_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_726_, v___x_729_, v___x_728_, v___x_730_, v___x_731_);
lean_dec_ref_known(v___x_729_, 3);
v___x_733_ = lean_array_to_list(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_inst_737_, lean_object* v_R_738_, lean_object* v_a_739_, lean_object* v_b_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_734_, v___x_735_, v___x_736_, v_a_739_, v_b_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_inst_745_, lean_object* v_R_746_, lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_742_, v___x_743_, v___x_744_, v_inst_745_, v_R_746_, v_a_747_, v_b_748_);
lean_dec_ref(v___x_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_752_ = l_String_intercalate(v___x_751_, v_parts_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_753_){
_start:
{
lean_inc_ref(v_toString_753_);
return v_toString_753_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_System_instCoeStringFilePath___lam__0(v_toString_754_);
lean_dec_ref(v_toString_754_);
return v_res_755_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = l_System_Platform_isWindows;
if (v___x_758_ == 0)
{
uint32_t v___x_759_; 
v___x_759_ = 58;
return v___x_759_;
}
else
{
uint32_t v___x_760_; 
v___x_760_ = 59;
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0));
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_765_);
lean_dec_ref(v_s_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v_a_770_, lean_object* v_b_771_){
_start:
{
lean_object* v_it_773_; lean_object* v_startInclusive_774_; lean_object* v_endExclusive_775_; 
if (lean_obj_tag(v_a_770_) == 0)
{
lean_object* v_currPos_779_; lean_object* v_searcher_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_806_; 
v_currPos_779_ = lean_ctor_get(v_a_770_, 0);
v_searcher_780_ = lean_ctor_get(v_a_770_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_806_ == 0)
{
v___x_782_ = v_a_770_;
v_isShared_783_ = v_isSharedCheck_806_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_searcher_780_);
lean_inc(v_currPos_779_);
lean_dec(v_a_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_806_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_startInclusive_784_; lean_object* v_endExclusive_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_startInclusive_784_ = lean_ctor_get(v___x_768_, 1);
v_endExclusive_785_ = lean_ctor_get(v___x_768_, 2);
v___x_786_ = lean_nat_sub(v_endExclusive_785_, v_startInclusive_784_);
v___x_787_ = lean_nat_dec_eq(v_searcher_780_, v___x_786_);
lean_dec(v___x_786_);
if (v___x_787_ == 0)
{
uint32_t v___x_788_; uint32_t v___x_789_; uint8_t v___x_790_; 
v___x_788_ = l_System_SearchPath_separator;
v___x_789_ = lean_string_utf8_get_fast(v_s_767_, v_searcher_780_);
v___x_790_ = lean_uint32_dec_eq(v___x_789_, v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_string_utf8_next_fast(v_s_767_, v_searcher_780_);
lean_dec(v_searcher_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_791_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_currPos_779_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v_a_770_ = v___x_793_;
goto _start;
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_slice_799_; lean_object* v_nextIt_801_; 
v___x_796_ = lean_string_utf8_next_fast(v_s_767_, v_searcher_780_);
v___x_797_ = lean_nat_sub(v___x_796_, v_searcher_780_);
v___x_798_ = lean_nat_add(v_searcher_780_, v___x_797_);
lean_dec(v___x_797_);
v_slice_799_ = l_String_Slice_subslice_x21(v___x_768_, v_currPos_779_, v_searcher_780_);
lean_inc(v___x_798_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_798_);
lean_ctor_set(v___x_782_, 0, v___x_798_);
v_nextIt_801_ = v___x_782_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_798_);
v_nextIt_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v_startInclusive_802_; lean_object* v_endExclusive_803_; 
v_startInclusive_802_ = lean_ctor_get(v_slice_799_, 0);
lean_inc(v_startInclusive_802_);
v_endExclusive_803_ = lean_ctor_get(v_slice_799_, 1);
lean_inc(v_endExclusive_803_);
lean_dec_ref(v_slice_799_);
v_it_773_ = v_nextIt_801_;
v_startInclusive_774_ = v_startInclusive_802_;
v_endExclusive_775_ = v_endExclusive_803_;
goto v___jp_772_;
}
}
}
else
{
lean_object* v___x_805_; 
lean_del_object(v___x_782_);
lean_dec(v_searcher_780_);
v___x_805_ = lean_box(1);
lean_inc(v___x_769_);
v_it_773_ = v___x_805_;
v_startInclusive_774_ = v_currPos_779_;
v_endExclusive_775_ = v___x_769_;
goto v___jp_772_;
}
}
}
else
{
lean_dec(v___x_769_);
return v_b_771_;
}
v___jp_772_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_string_utf8_extract(v_s_767_, v_startInclusive_774_, v_endExclusive_775_);
lean_dec(v_endExclusive_775_);
lean_dec(v_startInclusive_774_);
v___x_777_ = lean_array_push(v_b_771_, v___x_776_);
v_a_770_ = v_it_773_;
v_b_771_ = v___x_777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_807_, lean_object* v___x_808_, lean_object* v___x_809_, lean_object* v_a_810_, lean_object* v_b_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_807_, v___x_808_, v___x_809_, v_a_810_, v_b_811_);
lean_dec_ref(v___x_808_);
lean_dec_ref(v_s_807_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_string_utf8_byte_size(v_s_813_);
lean_inc_ref(v_s_813_);
v___x_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_816_, 0, v_s_813_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
v___x_817_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_816_);
v___x_818_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_813_, v___x_816_, v___x_815_, v___x_817_, v___x_818_);
lean_dec_ref_known(v___x_816_, 3);
lean_dec_ref(v_s_813_);
v___x_820_ = lean_array_to_list(v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_821_, lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v_inst_824_, lean_object* v_R_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_821_, v___x_822_, v___x_823_, v_a_826_, v_b_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_inst_832_, lean_object* v_R_833_, lean_object* v_a_834_, lean_object* v_b_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_829_, v___x_830_, v___x_831_, v_inst_832_, v_R_833_, v_a_834_, v_b_835_);
lean_dec_ref(v___x_830_);
lean_dec_ref(v_s_829_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
if (lean_obj_tag(v_a_837_) == 0)
{
lean_object* v___x_839_; 
v___x_839_ = l_List_reverse___redArg(v_a_838_);
return v___x_839_;
}
else
{
lean_object* v_head_840_; lean_object* v_tail_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_head_840_ = lean_ctor_get(v_a_837_, 0);
v_tail_841_ = lean_ctor_get(v_a_837_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_837_);
if (v_isSharedCheck_849_ == 0)
{
v___x_843_ = v_a_837_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_tail_841_);
lean_inc(v_head_840_);
lean_dec(v_a_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_a_838_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_head_840_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_838_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v_a_837_ = v_tail_841_;
v_a_838_ = v___x_846_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = l_System_SearchPath_separator;
v___x_851_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_852_ = lean_string_push(v___x_851_, v___x_850_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_854_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_855_ = lean_box(0);
v___x_856_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_853_, v___x_855_);
v___x_857_ = l_String_intercalate(v___x_854_, v___x_856_);
return v___x_857_;
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
