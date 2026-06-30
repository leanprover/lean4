// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter public import Lean.Linter.PersistentLintLog import Lean.CoreM import Lake.Config.Workspace
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* lean_get_stdout();
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "weak"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 5, 49, 232, 223, 147, 119, 138)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_BuiltinLint_leanOptOverrides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value;
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "internal"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__1 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value;
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cmdlineSnapshots"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__2 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 49, 45, 44, 152, 148, 209, 41)}};
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value_aux_0),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 168, 39, 157, 17, 55, 119, 69)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__3 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__4 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__4_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__4_value)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__5 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0_value;
static lean_once_cell_t l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "-- recorded by `lake lint --record-exceptions`"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "set_option "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " false in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "warning: could not read `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`; skipping its "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exception(s)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "warning: no declaration range for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "`; cannot record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "warning: could not locate source file for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` to record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "warning: could not determine the command position of a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` text-linter warning in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; skipping its exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__4_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__5_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "-- No environment linters were run for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__19_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__21_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t v_sz_4_, size_t v_i_5_, lean_object* v_bs_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_lt(v_i_5_, v_sz_4_);
if (v___x_7_ == 0)
{
return v_bs_6_;
}
else
{
lean_object* v_v_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_27_; 
v_v_8_ = lean_array_uget(v_bs_6_, v_i_5_);
v_fst_9_ = lean_ctor_get(v_v_8_, 0);
v_snd_10_ = lean_ctor_get(v_v_8_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_v_8_);
if (v_isSharedCheck_27_ == 0)
{
v___x_12_ = v_v_8_;
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_snd_10_);
lean_inc(v_fst_9_);
lean_dec(v_v_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v_bs_x27_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_21_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v_bs_x27_15_ = lean_array_uset(v_bs_6_, v_i_5_, v___x_14_);
v___x_16_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1));
v___x_17_ = l_Lean_Name_append(v___x_16_, v_fst_9_);
v___x_18_ = lean_alloc_ctor(1, 0, 1);
v___x_19_ = lean_unbox(v_snd_10_);
lean_dec(v_snd_10_);
lean_ctor_set_uint8(v___x_18_, 0, v___x_19_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_18_);
lean_ctor_set(v___x_12_, 0, v___x_17_);
v___x_21_ = v___x_12_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_18_);
v___x_21_ = v_reuseFailAlloc_26_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
size_t v___x_22_; size_t v___x_23_; lean_object* v___x_24_; 
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_5_, v___x_22_);
v___x_24_ = lean_array_uset(v_bs_x27_15_, v_i_5_, v___x_21_);
v_i_5_ = v___x_23_;
v_bs_6_ = v___x_24_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object* v_sz_28_, lean_object* v_i_29_, lean_object* v_bs_30_){
_start:
{
size_t v_sz_boxed_31_; size_t v_i_boxed_32_; lean_object* v_res_33_; 
v_sz_boxed_31_ = lean_unbox_usize(v_sz_28_);
lean_dec(v_sz_28_);
v_i_boxed_32_ = lean_unbox_usize(v_i_29_);
lean_dec(v_i_29_);
v_res_33_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_boxed_31_, v_i_boxed_32_, v_bs_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object* v_as_34_, size_t v_i_35_, size_t v_stop_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_eq(v_i_35_, v_stop_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___x_42_; size_t v___x_43_; size_t v___x_44_; 
v___x_39_ = lean_array_uget_borrowed(v_as_34_, v_i_35_);
v_fst_40_ = lean_ctor_get(v___x_39_, 0);
v_snd_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_snd_41_);
lean_inc(v_fst_40_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_40_, v_snd_41_, v_b_37_);
v___x_43_ = ((size_t)1ULL);
v___x_44_ = lean_usize_add(v_i_35_, v___x_43_);
v_i_35_ = v___x_44_;
v_b_37_ = v___x_42_;
goto _start;
}
else
{
return v_b_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object* v_as_46_, lean_object* v_i_47_, lean_object* v_stop_48_, lean_object* v_b_49_){
_start:
{
size_t v_i_boxed_50_; size_t v_stop_boxed_51_; lean_object* v_res_52_; 
v_i_boxed_50_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_stop_boxed_51_ = lean_unbox_usize(v_stop_48_);
lean_dec(v_stop_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_46_, v_i_boxed_50_, v_stop_boxed_51_, v_b_49_);
lean_dec_ref(v_as_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object* v_init_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_l_57_; lean_object* v_r_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_k_55_ = lean_ctor_get(v_x_54_, 1);
v_v_56_ = lean_ctor_get(v_x_54_, 2);
v_l_57_ = lean_ctor_get(v_x_54_, 3);
v_r_58_ = lean_ctor_get(v_x_54_, 4);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_53_, v_l_57_);
lean_inc(v_v_56_);
lean_inc(v_k_55_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_k_55_);
lean_ctor_set(v___x_60_, 1, v_v_56_);
v___x_61_ = lean_array_push(v___x_59_, v___x_60_);
v_init_53_ = v___x_61_;
v_x_54_ = v_r_58_;
goto _start;
}
else
{
return v_init_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object* v_init_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_63_, v_x_64_);
lean_dec(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_78_){
_start:
{
lean_object* v_linterOverrides_79_; uint8_t v_recordExceptions_80_; lean_object* v___y_82_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_linterOverrides_79_ = lean_ctor_get(v_args_78_, 0);
v_recordExceptions_80_ = lean_ctor_get_uint8(v_args_78_, sizeof(void*)*3 + 1);
v___x_92_ = lean_box(1);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_linterOverrides_79_);
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
v___y_82_ = v___x_92_;
goto v___jp_81_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = lean_nat_dec_le(v___x_94_, v___x_94_);
if (v___x_96_ == 0)
{
if (v___x_95_ == 0)
{
v___y_82_ = v___x_92_;
goto v___jp_81_;
}
else
{
size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_94_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_79_, v___x_97_, v___x_98_, v___x_92_);
v___y_82_ = v___x_99_;
goto v___jp_81_;
}
}
else
{
size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; 
v___x_100_ = ((size_t)0ULL);
v___x_101_ = lean_usize_of_nat(v___x_94_);
v___x_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_79_, v___x_100_, v___x_101_, v___x_92_);
v___y_82_ = v___x_102_;
goto v___jp_81_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; size_t v_sz_85_; size_t v___x_86_; lean_object* v_base_87_; 
v___x_83_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__0));
v___x_84_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v___x_83_, v___y_82_);
lean_dec(v___y_82_);
v_sz_85_ = lean_array_size(v___x_84_);
v___x_86_ = ((size_t)0ULL);
v_base_87_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_85_, v___x_86_, v___x_84_);
if (v_recordExceptions_80_ == 0)
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_LeanOptions_ofArray(v_base_87_);
lean_dec_ref(v_base_87_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__5));
v___x_90_ = lean_array_push(v_base_87_, v___x_89_);
v___x_91_ = l_Lean_LeanOptions_ofArray(v___x_90_);
lean_dec_ref(v___x_90_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_103_);
lean_dec_ref(v_args_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_105_, lean_object* v_t_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_105_, v_t_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_108_, lean_object* v_t_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_108_, v_t_109_);
lean_dec(v_t_109_);
return v_res_110_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_box(0);
v___x_113_ = l_Lean_instInhabitedPosition_default;
v___x_114_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1, &l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once, _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_118_, lean_object* v_as_119_, size_t v_i_120_, size_t v_stop_121_, lean_object* v_b_122_){
_start:
{
lean_object* v___y_124_; uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_120_, v_stop_121_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; uint8_t v___y_131_; lean_object* v_fst_133_; lean_object* v_snd_134_; uint8_t v___x_135_; 
v___x_129_ = lean_array_uget_borrowed(v_as_119_, v_i_120_);
v_fst_133_ = lean_ctor_get(v___x_129_, 0);
v_snd_134_ = lean_ctor_get(v___x_129_, 1);
v___x_135_ = l_Lean_Name_isPrefixOf(v_pkgRoot_118_, v_fst_133_);
if (v___x_135_ == 0)
{
v___y_131_ = v___x_135_;
goto v___jp_130_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_array_get_size(v_snd_134_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
v___y_131_ = v___x_135_;
goto v___jp_130_;
}
else
{
v___y_124_ = v_b_122_;
goto v___jp_123_;
}
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
v___y_124_ = v_b_122_;
goto v___jp_123_;
}
else
{
lean_object* v___x_132_; 
lean_inc(v___x_129_);
v___x_132_ = lean_array_push(v_b_122_, v___x_129_);
v___y_124_ = v___x_132_;
goto v___jp_123_;
}
}
}
else
{
return v_b_122_;
}
v___jp_123_:
{
size_t v___x_125_; size_t v___x_126_; 
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_120_, v___x_125_);
v_i_120_ = v___x_126_;
v_b_122_ = v___y_124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_139_, lean_object* v_as_140_, lean_object* v_i_141_, lean_object* v_stop_142_, lean_object* v_b_143_){
_start:
{
size_t v_i_boxed_144_; size_t v_stop_boxed_145_; lean_object* v_res_146_; 
v_i_boxed_144_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_145_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_139_, v_as_140_, v_i_boxed_144_, v_stop_boxed_145_, v_b_143_);
lean_dec_ref(v_as_140_);
lean_dec(v_pkgRoot_139_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_149_, lean_object* v_pkgRoot_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_153_ = l_Lean_Linter_getAllLints(v_env_149_);
v___x_154_ = lean_array_get_size(v___x_153_);
v___x_155_ = lean_nat_dec_lt(v___x_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec_ref(v___x_153_);
return v___x_152_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_le(v___x_154_, v___x_154_);
if (v___x_156_ == 0)
{
if (v___x_155_ == 0)
{
lean_dec_ref(v___x_153_);
return v___x_152_;
}
else
{
size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((size_t)0ULL);
v___x_158_ = lean_usize_of_nat(v___x_154_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_150_, v___x_153_, v___x_157_, v___x_158_, v___x_152_);
lean_dec_ref(v___x_153_);
return v___x_159_;
}
}
else
{
size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((size_t)0ULL);
v___x_161_ = lean_usize_of_nat(v___x_154_);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_150_, v___x_153_, v___x_160_, v___x_161_, v___x_152_);
lean_dec_ref(v___x_153_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_163_, lean_object* v_pkgRoot_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_163_, v_pkgRoot_164_);
lean_dec(v_pkgRoot_164_);
lean_dec_ref(v_env_163_);
return v_res_165_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_166_){
_start:
{
uint8_t v_isModule_168_; 
v_isModule_168_ = lean_ctor_get_uint8(v_modData_166_, sizeof(void*)*5);
return v_isModule_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_169_, lean_object* v_a_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_169_);
lean_dec_ref(v_modData_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_175_){
_start:
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 32;
v___x_177_ = lean_uint32_dec_eq(v_c_175_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 9;
v___x_179_ = lean_uint32_dec_eq(v_c_175_, v___x_178_);
return v___x_179_;
}
else
{
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_180_){
_start:
{
uint32_t v_c_boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_c_boxed_181_ = lean_unbox_uint32(v_c_180_);
lean_dec(v_c_180_);
v_res_182_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_184_, lean_object* v_stopPos_185_, lean_object* v_i_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_lt(v_i_186_, v_stopPos_185_);
if (v___x_187_ == 0)
{
return v_i_186_;
}
else
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_string_utf8_get(v_s_184_, v_i_186_);
v___x_189_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_188_);
if (v___x_189_ == 0)
{
return v_i_186_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_string_utf8_next(v_s_184_, v_i_186_);
lean_dec(v_i_186_);
v_i_186_ = v___x_190_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_192_, lean_object* v_stopPos_193_, lean_object* v_i_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_192_, v_stopPos_193_, v_i_194_);
lean_dec(v_stopPos_193_);
lean_dec_ref(v_s_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_e_199_; lean_object* v___x_200_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_string_utf8_byte_size(v_line_196_);
v_e_199_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_196_, v___x_198_, v___x_197_);
v___x_200_ = lean_string_utf8_extract(v_line_196_, v___x_197_, v_e_199_);
lean_dec(v_e_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_201_);
lean_dec_ref(v_line_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_207_);
lean_dec_ref(v_s_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_key_211_; lean_object* v_value_212_; lean_object* v_tail_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_key_211_ = lean_ctor_get(v_x_210_, 0);
v_value_212_ = lean_ctor_get(v_x_210_, 1);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
lean_inc(v_value_212_);
lean_inc(v_key_211_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_key_211_);
lean_ctor_set(v___x_214_, 1, v_value_212_);
v___x_215_ = lean_array_push(v_x_209_, v___x_214_);
v_x_209_ = v___x_215_;
v_x_210_ = v_tail_213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_217_, v_x_218_);
lean_dec(v_x_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_, lean_object* v_b_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_221_, v_stop_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; size_t v___x_227_; size_t v___x_228_; 
v___x_225_ = lean_array_uget_borrowed(v_as_220_, v_i_221_);
v___x_226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_223_, v___x_225_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_add(v_i_221_, v___x_227_);
v_i_221_ = v___x_228_;
v_b_223_ = v___x_226_;
goto _start;
}
else
{
return v_b_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_230_, v_i_boxed_234_, v_stop_boxed_235_, v_b_233_);
lean_dec_ref(v_as_230_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_putStr_240_; lean_object* v___x_241_; 
v___x_239_ = lean_get_stderr();
v_putStr_240_ = lean_ctor_get(v___x_239_, 4);
lean_inc_ref(v_putStr_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = lean_apply_2(v_putStr_240_, v_s_237_, lean_box(0));
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_245_){
_start:
{
uint32_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = 10;
v___x_248_ = lean_string_push(v_s_245_, v___x_247_);
v___x_249_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
return v_x_253_;
}
else
{
lean_object* v_key_255_; lean_object* v_value_256_; lean_object* v_tail_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_key_255_ = lean_ctor_get(v_x_254_, 0);
v_value_256_ = lean_ctor_get(v_x_254_, 1);
v_tail_257_ = lean_ctor_get(v_x_254_, 2);
lean_inc(v_value_256_);
lean_inc(v_key_255_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_key_255_);
lean_ctor_set(v___x_258_, 1, v_value_256_);
v___x_259_ = lean_array_push(v_x_253_, v___x_258_);
v_x_253_ = v___x_259_;
v_x_254_ = v_tail_257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_261_, v_x_262_);
lean_dec(v_x_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_264_, size_t v_i_265_, size_t v_stop_266_, lean_object* v_b_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_eq(v_i_265_, v_stop_266_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; size_t v___x_271_; size_t v___x_272_; 
v___x_269_ = lean_array_uget_borrowed(v_as_264_, v_i_265_);
v___x_270_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_267_, v___x_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_265_, v___x_271_);
v_i_265_ = v___x_272_;
v_b_267_ = v___x_270_;
goto _start;
}
else
{
return v_b_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_stop_276_, lean_object* v_b_277_){
_start:
{
size_t v_i_boxed_278_; size_t v_stop_boxed_279_; lean_object* v_res_280_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_stop_boxed_279_ = lean_unbox_usize(v_stop_276_);
lean_dec(v_stop_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_274_, v_i_boxed_278_, v_stop_boxed_279_, v_b_277_);
lean_dec_ref(v_as_274_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_fst_283_; lean_object* v_fst_284_; uint8_t v___x_285_; 
v_fst_283_ = lean_ctor_get(v_b_282_, 0);
v_fst_284_ = lean_ctor_get(v_a_281_, 0);
v___x_285_ = lean_nat_dec_lt(v_fst_283_, v_fst_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_286_, v_b_287_);
lean_dec_ref(v_b_287_);
lean_dec_ref(v_a_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_290_, lean_object* v_pivot_291_, lean_object* v_as_292_, lean_object* v_i_293_, lean_object* v_k_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_lt(v_k_294_, v_hi_290_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_k_294_);
v___x_296_ = lean_array_fswap(v_as_292_, v_i_293_, v_hi_290_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_i_293_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_fst_298_; lean_object* v___x_299_; lean_object* v_fst_300_; uint8_t v___x_301_; 
v_fst_298_ = lean_ctor_get(v_pivot_291_, 0);
v___x_299_ = lean_array_fget_borrowed(v_as_292_, v_k_294_);
v_fst_300_ = lean_ctor_get(v___x_299_, 0);
v___x_301_ = lean_nat_dec_lt(v_fst_298_, v_fst_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_k_294_, v___x_302_);
lean_dec(v_k_294_);
v_k_294_ = v___x_303_;
goto _start;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = lean_array_fswap(v_as_292_, v_i_293_, v_k_294_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_i_293_, v___x_306_);
lean_dec(v_i_293_);
v___x_308_ = lean_nat_add(v_k_294_, v___x_306_);
lean_dec(v_k_294_);
v_as_292_ = v___x_305_;
v_i_293_ = v___x_307_;
v_k_294_ = v___x_308_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_310_, lean_object* v_pivot_311_, lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_k_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_310_, v_pivot_311_, v_as_312_, v_i_313_, v_k_314_);
lean_dec_ref(v_pivot_311_);
lean_dec(v_hi_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_316_, lean_object* v_as_317_, lean_object* v_lo_318_, lean_object* v_hi_319_){
_start:
{
lean_object* v___y_321_; uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_lt(v_lo_318_, v_hi_319_);
if (v___x_331_ == 0)
{
lean_dec(v_lo_318_);
return v_as_317_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_mid_334_; lean_object* v___y_336_; lean_object* v___y_342_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_332_ = lean_nat_add(v_lo_318_, v_hi_319_);
v___x_333_ = lean_unsigned_to_nat(1u);
v_mid_334_ = lean_nat_shiftr(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
v___x_347_ = lean_array_fget_borrowed(v_as_317_, v_mid_334_);
v___x_348_ = lean_array_fget_borrowed(v_as_317_, v_lo_318_);
v___x_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
v___y_342_ = v_as_317_;
goto v___jp_341_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_array_fswap(v_as_317_, v_lo_318_, v_mid_334_);
v___y_342_ = v___x_350_;
goto v___jp_341_;
}
v___jp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_array_fget_borrowed(v___y_336_, v_mid_334_);
v___x_338_ = lean_array_fget_borrowed(v___y_336_, v_hi_319_);
v___x_339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v_mid_334_);
v___y_321_ = v___y_336_;
goto v___jp_320_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_fswap(v___y_336_, v_mid_334_, v_hi_319_);
lean_dec(v_mid_334_);
v___y_321_ = v___x_340_;
goto v___jp_320_;
}
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_array_fget_borrowed(v___y_342_, v_hi_319_);
v___x_344_ = lean_array_fget_borrowed(v___y_342_, v_lo_318_);
v___x_345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
v___y_336_ = v___y_342_;
goto v___jp_335_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_array_fswap(v___y_342_, v_lo_318_, v_hi_319_);
v___y_336_ = v___x_346_;
goto v___jp_335_;
}
}
}
v___jp_320_:
{
lean_object* v_pivot_322_; lean_object* v___x_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; uint8_t v___x_326_; 
v_pivot_322_ = lean_array_fget(v___y_321_, v_hi_319_);
lean_inc_n(v_lo_318_, 2);
v___x_323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_319_, v_pivot_322_, v___y_321_, v_lo_318_, v_lo_318_);
lean_dec(v_pivot_322_);
v_fst_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_fst_324_);
v_snd_325_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_snd_325_);
lean_dec_ref(v___x_323_);
v___x_326_ = lean_nat_dec_le(v_hi_319_, v_fst_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_316_, v_snd_325_, v_lo_318_, v_fst_324_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_fst_324_, v___x_328_);
lean_dec(v_fst_324_);
v_as_317_ = v___x_327_;
v_lo_318_ = v___x_329_;
goto _start;
}
else
{
lean_dec(v_fst_324_);
lean_dec(v_lo_318_);
return v_snd_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_351_, lean_object* v_as_352_, lean_object* v_lo_353_, lean_object* v_hi_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_351_, v_as_352_, v_lo_353_, v_hi_354_);
lean_dec(v_hi_354_);
lean_dec(v_n_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_356_, lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_it_362_; lean_object* v_startInclusive_363_; lean_object* v_endExclusive_364_; 
if (lean_obj_tag(v_a_359_) == 0)
{
lean_object* v_currPos_368_; lean_object* v_searcher_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_395_; 
v_currPos_368_ = lean_ctor_get(v_a_359_, 0);
v_searcher_369_ = lean_ctor_get(v_a_359_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_a_359_);
if (v_isSharedCheck_395_ == 0)
{
v___x_371_ = v_a_359_;
v_isShared_372_ = v_isSharedCheck_395_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_searcher_369_);
lean_inc(v_currPos_368_);
lean_dec(v_a_359_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_395_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_startInclusive_373_; lean_object* v_endExclusive_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_startInclusive_373_ = lean_ctor_get(v___x_357_, 1);
v_endExclusive_374_ = lean_ctor_get(v___x_357_, 2);
v___x_375_ = lean_nat_sub(v_endExclusive_374_, v_startInclusive_373_);
v___x_376_ = lean_nat_dec_eq(v_searcher_369_, v___x_375_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_377_ = 10;
v___x_378_ = lean_string_utf8_get_fast(v_a_356_, v_searcher_369_);
v___x_379_ = lean_uint32_dec_eq(v___x_378_, v___x_377_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_string_utf8_next_fast(v_a_356_, v_searcher_369_);
lean_dec(v_searcher_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_380_);
v___x_382_ = v___x_371_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_currPos_368_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v_a_359_ = v___x_382_;
goto _start;
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_slice_388_; lean_object* v_nextIt_390_; 
v___x_385_ = lean_string_utf8_next_fast(v_a_356_, v_searcher_369_);
v___x_386_ = lean_nat_sub(v___x_385_, v_searcher_369_);
v___x_387_ = lean_nat_add(v_searcher_369_, v___x_386_);
lean_dec(v___x_386_);
v_slice_388_ = l_String_Slice_subslice_x21(v___x_357_, v_currPos_368_, v_searcher_369_);
lean_inc(v___x_387_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_387_);
lean_ctor_set(v___x_371_, 0, v___x_387_);
v_nextIt_390_ = v___x_371_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_387_);
v_nextIt_390_ = v_reuseFailAlloc_393_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; 
v_startInclusive_391_ = lean_ctor_get(v_slice_388_, 0);
lean_inc(v_startInclusive_391_);
v_endExclusive_392_ = lean_ctor_get(v_slice_388_, 1);
lean_inc(v_endExclusive_392_);
lean_dec_ref(v_slice_388_);
v_it_362_ = v_nextIt_390_;
v_startInclusive_363_ = v_startInclusive_391_;
v_endExclusive_364_ = v_endExclusive_392_;
goto v___jp_361_;
}
}
}
else
{
lean_object* v___x_394_; 
lean_del_object(v___x_371_);
lean_dec(v_searcher_369_);
v___x_394_ = lean_box(1);
lean_inc(v___x_358_);
v_it_362_ = v___x_394_;
v_startInclusive_363_ = v_currPos_368_;
v_endExclusive_364_ = v___x_358_;
goto v___jp_361_;
}
}
}
else
{
lean_dec(v___x_358_);
lean_dec_ref(v_a_356_);
return v_b_360_;
}
v___jp_361_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_inc_ref(v_a_356_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_a_356_);
lean_ctor_set(v___x_365_, 1, v_startInclusive_363_);
lean_ctor_set(v___x_365_, 2, v_endExclusive_364_);
v___x_366_ = lean_array_push(v_b_360_, v___x_365_);
v_a_359_ = v_it_362_;
v_b_360_ = v___x_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_396_, v___x_397_, v___x_398_, v_a_399_, v_b_400_);
lean_dec_ref(v___x_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_402_, size_t v_i_403_, lean_object* v_bs_404_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = lean_usize_dec_lt(v_i_403_, v_sz_402_);
if (v___x_405_ == 0)
{
return v_bs_404_;
}
else
{
lean_object* v_v_406_; lean_object* v___x_407_; lean_object* v_bs_x27_408_; lean_object* v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v_v_406_ = lean_array_uget(v_bs_404_, v_i_403_);
v___x_407_ = lean_unsigned_to_nat(0u);
v_bs_x27_408_ = lean_array_uset(v_bs_404_, v_i_403_, v___x_407_);
v___x_409_ = l_String_Slice_toString(v_v_406_);
lean_dec(v_v_406_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_403_, v___x_410_);
v___x_412_ = lean_array_uset(v_bs_x27_408_, v_i_403_, v___x_409_);
v_i_403_ = v___x_411_;
v_bs_404_ = v___x_412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_414_, lean_object* v_i_415_, lean_object* v_bs_416_){
_start:
{
size_t v_sz_boxed_417_; size_t v_i_boxed_418_; lean_object* v_res_419_; 
v_sz_boxed_417_ = lean_unbox_usize(v_sz_414_);
lean_dec(v_sz_414_);
v_i_boxed_418_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_res_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_417_, v_i_boxed_418_, v_bs_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
return v_x_420_;
}
else
{
lean_object* v_key_422_; lean_object* v_value_423_; lean_object* v_tail_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_447_; 
v_key_422_ = lean_ctor_get(v_x_421_, 0);
v_value_423_ = lean_ctor_get(v_x_421_, 1);
v_tail_424_ = lean_ctor_get(v_x_421_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_421_);
if (v_isSharedCheck_447_ == 0)
{
v___x_426_ = v_x_421_;
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_tail_424_);
lean_inc(v_value_423_);
lean_inc(v_key_422_);
lean_dec(v_x_421_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_428_ = lean_array_get_size(v_x_420_);
v___x_429_ = lean_uint64_of_nat(v_key_422_);
v___x_430_ = 32ULL;
v___x_431_ = lean_uint64_shift_right(v___x_429_, v___x_430_);
v_fold_432_ = lean_uint64_xor(v___x_429_, v___x_431_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_428_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v___x_441_ = lean_array_uget_borrowed(v_x_420_, v___x_440_);
lean_inc(v___x_441_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 2, v___x_441_);
v___x_443_ = v___x_426_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_key_422_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_value_423_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v___x_441_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_array_uset(v_x_420_, v___x_440_, v___x_443_);
v_x_420_ = v___x_444_;
v_x_421_ = v_tail_424_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_448_, lean_object* v_source_449_, lean_object* v_target_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_array_get_size(v_source_449_);
v___x_452_ = lean_nat_dec_lt(v_i_448_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec_ref(v_source_449_);
lean_dec(v_i_448_);
return v_target_450_;
}
else
{
lean_object* v_es_453_; lean_object* v___x_454_; lean_object* v_source_455_; lean_object* v_target_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_es_453_ = lean_array_fget(v_source_449_, v_i_448_);
v___x_454_ = lean_box(0);
v_source_455_ = lean_array_fset(v_source_449_, v_i_448_, v___x_454_);
v_target_456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_450_, v_es_453_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_i_448_, v___x_457_);
lean_dec(v_i_448_);
v_i_448_ = v___x_458_;
v_source_449_ = v_source_455_;
v_target_450_ = v_target_456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_nbuckets_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_461_ = lean_array_get_size(v_data_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v_nbuckets_463_ = lean_nat_mul(v___x_461_, v___x_462_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_box(0);
v___x_466_ = lean_mk_array(v_nbuckets_463_, v___x_465_);
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_464_, v_data_460_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
else
{
lean_object* v_key_471_; lean_object* v_tail_472_; uint8_t v___x_473_; 
v_key_471_ = lean_ctor_get(v_x_469_, 0);
v_tail_472_ = lean_ctor_get(v_x_469_, 2);
v___x_473_ = lean_nat_dec_eq(v_key_471_, v_a_468_);
if (v___x_473_ == 0)
{
v_x_469_ = v_tail_472_;
goto _start;
}
else
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_475_, v_x_476_);
lean_dec(v_x_476_);
lean_dec(v_a_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_479_, lean_object* v_b_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_dec(v_b_480_);
lean_dec(v_a_479_);
return v_x_481_;
}
else
{
lean_object* v_key_482_; lean_object* v_value_483_; lean_object* v_tail_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_496_; 
v_key_482_ = lean_ctor_get(v_x_481_, 0);
v_value_483_ = lean_ctor_get(v_x_481_, 1);
v_tail_484_ = lean_ctor_get(v_x_481_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_496_ == 0)
{
v___x_486_ = v_x_481_;
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_tail_484_);
lean_inc(v_value_483_);
lean_inc(v_key_482_);
lean_dec(v_x_481_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; 
v___x_488_ = lean_nat_dec_eq(v_key_482_, v_a_479_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_479_, v_b_480_, v_tail_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 2, v___x_489_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_value_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v_value_483_);
lean_dec(v_key_482_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_b_480_);
lean_ctor_set(v___x_486_, 0, v_a_479_);
v___x_494_ = v___x_486_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_479_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_b_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_tail_484_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
lean_object* v_size_500_; lean_object* v_buckets_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_544_; 
v_size_500_ = lean_ctor_get(v_m_497_, 0);
v_buckets_501_ = lean_ctor_get(v_m_497_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_m_497_);
if (v_isSharedCheck_544_ == 0)
{
v___x_503_ = v_m_497_;
v_isShared_504_ = v_isSharedCheck_544_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_buckets_501_);
lean_inc(v_size_500_);
lean_dec(v_m_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_544_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v_fold_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v_bkt_518_; uint8_t v___x_519_; 
v___x_505_ = lean_array_get_size(v_buckets_501_);
v___x_506_ = lean_uint64_of_nat(v_a_498_);
v___x_507_ = 32ULL;
v___x_508_ = lean_uint64_shift_right(v___x_506_, v___x_507_);
v_fold_509_ = lean_uint64_xor(v___x_506_, v___x_508_);
v___x_510_ = 16ULL;
v___x_511_ = lean_uint64_shift_right(v_fold_509_, v___x_510_);
v___x_512_ = lean_uint64_xor(v_fold_509_, v___x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = lean_usize_of_nat(v___x_505_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_sub(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_land(v___x_513_, v___x_516_);
v_bkt_518_ = lean_array_uget_borrowed(v_buckets_501_, v___x_517_);
v___x_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_498_, v_bkt_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v_size_x27_521_; lean_object* v___x_522_; lean_object* v_buckets_x27_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v_size_x27_521_ = lean_nat_add(v_size_500_, v___x_520_);
lean_dec(v_size_500_);
lean_inc(v_bkt_518_);
v___x_522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_522_, 0, v_a_498_);
lean_ctor_set(v___x_522_, 1, v_b_499_);
lean_ctor_set(v___x_522_, 2, v_bkt_518_);
v_buckets_x27_523_ = lean_array_uset(v_buckets_501_, v___x_517_, v___x_522_);
v___x_524_ = lean_unsigned_to_nat(4u);
v___x_525_ = lean_nat_mul(v_size_x27_521_, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(3u);
v___x_527_ = lean_nat_div(v___x_525_, v___x_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_array_get_size(v_buckets_x27_523_);
v___x_529_ = lean_nat_dec_le(v___x_527_, v___x_528_);
lean_dec(v___x_527_);
if (v___x_529_ == 0)
{
lean_object* v_val_530_; lean_object* v___x_532_; 
v_val_530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_523_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_val_530_);
lean_ctor_set(v___x_503_, 0, v_size_x27_521_);
v___x_532_ = v___x_503_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_size_x27_521_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_val_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v___x_535_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_buckets_x27_523_);
lean_ctor_set(v___x_503_, 0, v_size_x27_521_);
v___x_535_ = v___x_503_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_size_x27_521_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_buckets_x27_523_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v___x_537_; lean_object* v_buckets_x27_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc(v_bkt_518_);
v___x_537_ = lean_box(0);
v_buckets_x27_538_ = lean_array_uset(v_buckets_501_, v___x_517_, v___x_537_);
v___x_539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_498_, v_b_499_, v_bkt_518_);
v___x_540_ = lean_array_uset(v_buckets_x27_538_, v___x_517_, v___x_539_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_540_);
v___x_542_ = v___x_503_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_500_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_545_, lean_object* v_as_546_, size_t v_i_547_, size_t v_stop_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_eq(v_i_547_, v_stop_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_array_uget_borrowed(v_as_546_, v_i_547_);
v___x_551_ = lean_name_eq(v_a_545_, v___x_550_);
if (v___x_551_ == 0)
{
size_t v___x_552_; size_t v___x_553_; 
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_547_, v___x_552_);
v_i_547_ = v___x_553_;
goto _start;
}
else
{
return v___x_551_;
}
}
else
{
uint8_t v___x_555_; 
v___x_555_ = 0;
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_556_, lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_stop_559_){
_start:
{
size_t v_i_boxed_560_; size_t v_stop_boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_i_boxed_560_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_559_);
lean_dec(v_stop_559_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_556_, v_as_557_, v_i_boxed_560_, v_stop_boxed_561_);
lean_dec_ref(v_as_557_);
lean_dec(v_a_556_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_array_get_size(v_as_564_);
v___x_568_ = lean_nat_dec_lt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
return v___x_568_;
}
else
{
if (v___x_568_ == 0)
{
return v___x_568_;
}
else
{
size_t v___x_569_; size_t v___x_570_; uint8_t v___x_571_; 
v___x_569_ = ((size_t)0ULL);
v___x_570_ = lean_usize_of_nat(v___x_567_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_565_, v_as_564_, v___x_569_, v___x_570_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_572_, lean_object* v_a_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_as_572_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_576_, lean_object* v_fallback_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_inc(v_fallback_577_);
return v_fallback_577_;
}
else
{
lean_object* v_key_579_; lean_object* v_value_580_; lean_object* v_tail_581_; uint8_t v___x_582_; 
v_key_579_ = lean_ctor_get(v_x_578_, 0);
v_value_580_ = lean_ctor_get(v_x_578_, 1);
v_tail_581_ = lean_ctor_get(v_x_578_, 2);
v___x_582_ = lean_nat_dec_eq(v_key_579_, v_a_576_);
if (v___x_582_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
lean_inc(v_value_580_);
return v_value_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_584_, lean_object* v_fallback_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_584_, v_fallback_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v_fallback_585_);
lean_dec(v_a_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_588_, lean_object* v_a_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_buckets_591_; lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v_fold_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_buckets_591_ = lean_ctor_get(v_m_588_, 1);
v___x_592_ = lean_array_get_size(v_buckets_591_);
v___x_593_ = lean_uint64_of_nat(v_a_589_);
v___x_594_ = 32ULL;
v___x_595_ = lean_uint64_shift_right(v___x_593_, v___x_594_);
v_fold_596_ = lean_uint64_xor(v___x_593_, v___x_595_);
v___x_597_ = 16ULL;
v___x_598_ = lean_uint64_shift_right(v_fold_596_, v___x_597_);
v___x_599_ = lean_uint64_xor(v_fold_596_, v___x_598_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = lean_usize_of_nat(v___x_592_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_sub(v___x_601_, v___x_602_);
v___x_604_ = lean_usize_land(v___x_600_, v___x_603_);
v___x_605_ = lean_array_uget_borrowed(v_buckets_591_, v___x_604_);
v___x_606_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_589_, v_fallback_590_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_607_, lean_object* v_a_608_, lean_object* v_fallback_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_607_, v_a_608_, v_fallback_609_);
lean_dec(v_fallback_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_m_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_a_619_; uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_616_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_a_625_ = lean_array_uget_borrowed(v_as_613_, v_i_615_);
v_fst_626_ = lean_ctor_get(v_a_625_, 0);
v_snd_627_ = lean_ctor_get(v_a_625_, 1);
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_616_, v_fst_626_, v___x_628_);
v___x_630_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_629_, v_snd_627_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_inc(v_snd_627_);
v___x_631_ = lean_array_push(v___x_629_, v_snd_627_);
lean_inc(v_fst_626_);
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_616_, v_fst_626_, v___x_631_);
v_a_619_ = v___x_632_;
goto v___jp_618_;
}
else
{
lean_dec(v___x_629_);
v_a_619_ = v_b_616_;
goto v___jp_618_;
}
}
v___jp_618_:
{
size_t v___x_620_; size_t v___x_621_; 
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_615_, v___x_620_);
v_i_615_ = v___x_621_;
v_b_616_ = v_a_619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_){
_start:
{
size_t v_sz_boxed_638_; size_t v_i_boxed_639_; lean_object* v_res_640_; 
v_sz_boxed_638_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_639_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_633_, v_sz_boxed_638_, v_i_boxed_639_, v_b_636_);
lean_dec_ref(v_as_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_putStr_644_; lean_object* v___x_645_; 
v___x_643_ = lean_get_stdout();
v_putStr_644_ = lean_ctor_get(v___x_643_, 4);
lean_inc_ref(v_putStr_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_apply_2(v_putStr_644_, v_s_641_, lean_box(0));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_649_){
_start:
{
uint32_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = 10;
v___x_652_ = lean_string_push(v_s_649_, v___x_651_);
v___x_653_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_654_);
return v_res_656_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_657_, lean_object* v_a_658_, lean_object* v_b_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_658_, v___x_657_);
v___x_661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_659_, v___x_657_);
v___x_662_ = lean_string_dec_lt(v___x_660_, v___x_661_);
lean_dec_ref(v___x_661_);
lean_dec_ref(v___x_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_663_, lean_object* v_a_664_, lean_object* v_b_665_){
_start:
{
uint8_t v___x_11634__boxed_666_; uint8_t v_res_667_; lean_object* v_r_668_; 
v___x_11634__boxed_666_ = lean_unbox(v___x_663_);
v_res_667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11634__boxed_666_, v_a_664_, v_b_665_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v_hi_669_, lean_object* v_pivot_670_, lean_object* v_as_671_, lean_object* v_i_672_, lean_object* v_k_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_lt(v_k_673_, v_hi_669_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_k_673_);
lean_dec(v_pivot_670_);
v___x_675_ = lean_array_fswap(v_as_671_, v_i_672_, v_hi_669_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_i_672_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_677_ = lean_array_fget_borrowed(v_as_671_, v_k_673_);
lean_inc(v___x_677_);
v___x_678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_677_, v___x_674_);
lean_inc(v_pivot_670_);
v___x_679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_670_, v___x_674_);
v___x_680_ = lean_string_dec_lt(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v___x_678_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_k_673_, v___x_681_);
lean_dec(v_k_673_);
v_k_673_ = v___x_682_;
goto _start;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_array_fswap(v_as_671_, v_i_672_, v_k_673_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_i_672_, v___x_685_);
lean_dec(v_i_672_);
v___x_687_ = lean_nat_add(v_k_673_, v___x_685_);
lean_dec(v_k_673_);
v_as_671_ = v___x_684_;
v_i_672_ = v___x_686_;
v_k_673_ = v___x_687_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v_hi_689_, lean_object* v_pivot_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_689_, v_pivot_690_, v_as_691_, v_i_692_, v_k_693_);
lean_dec(v_hi_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v_n_695_, lean_object* v_as_696_, lean_object* v_lo_697_, lean_object* v_hi_698_){
_start:
{
lean_object* v___y_700_; uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_lt(v_lo_697_, v_hi_698_);
if (v___x_710_ == 0)
{
lean_dec(v_lo_697_);
return v_as_696_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_mid_713_; lean_object* v___y_715_; lean_object* v___y_721_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_711_ = lean_nat_add(v_lo_697_, v_hi_698_);
v___x_712_ = lean_unsigned_to_nat(1u);
v_mid_713_ = lean_nat_shiftr(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
v___x_726_ = lean_array_fget_borrowed(v_as_696_, v_mid_713_);
v___x_727_ = lean_array_fget_borrowed(v_as_696_, v_lo_697_);
lean_inc(v___x_727_);
lean_inc(v___x_726_);
v___x_728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_710_, v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
v___y_721_ = v_as_696_;
goto v___jp_720_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = lean_array_fswap(v_as_696_, v_lo_697_, v_mid_713_);
v___y_721_ = v___x_729_;
goto v___jp_720_;
}
v___jp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_array_fget_borrowed(v___y_715_, v_mid_713_);
v___x_717_ = lean_array_fget_borrowed(v___y_715_, v_hi_698_);
lean_inc(v___x_717_);
lean_inc(v___x_716_);
v___x_718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_710_, v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_mid_713_);
v___y_700_ = v___y_715_;
goto v___jp_699_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_array_fswap(v___y_715_, v_mid_713_, v_hi_698_);
lean_dec(v_mid_713_);
v___y_700_ = v___x_719_;
goto v___jp_699_;
}
}
v___jp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_array_fget_borrowed(v___y_721_, v_hi_698_);
v___x_723_ = lean_array_fget_borrowed(v___y_721_, v_lo_697_);
lean_inc(v___x_723_);
lean_inc(v___x_722_);
v___x_724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_710_, v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
v___y_715_ = v___y_721_;
goto v___jp_714_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_array_fswap(v___y_721_, v_lo_697_, v_hi_698_);
v___y_715_ = v___x_725_;
goto v___jp_714_;
}
}
}
v___jp_699_:
{
lean_object* v_pivot_701_; lean_object* v___x_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; uint8_t v___x_705_; 
v_pivot_701_ = lean_array_fget(v___y_700_, v_hi_698_);
lean_inc_n(v_lo_697_, 2);
v___x_702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_698_, v_pivot_701_, v___y_700_, v_lo_697_, v_lo_697_);
v_fst_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_fst_703_);
v_snd_704_ = lean_ctor_get(v___x_702_, 1);
lean_inc(v_snd_704_);
lean_dec_ref(v___x_702_);
v___x_705_ = lean_nat_dec_le(v_hi_698_, v_fst_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_695_, v_snd_704_, v_lo_697_, v_fst_703_);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_fst_703_, v___x_707_);
lean_dec(v_fst_703_);
v_as_696_ = v___x_706_;
v_lo_697_ = v___x_708_;
goto _start;
}
else
{
lean_dec(v_fst_703_);
lean_dec(v_lo_697_);
return v_snd_704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v_n_730_, lean_object* v_as_731_, lean_object* v_lo_732_, lean_object* v_hi_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_730_, v_as_731_, v_lo_732_, v_hi_733_);
lean_dec(v_hi_733_);
lean_dec(v_n_730_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_737_, size_t v_sz_738_, size_t v_i_739_, lean_object* v_bs_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = lean_usize_dec_lt(v_i_739_, v_sz_738_);
if (v___x_741_ == 0)
{
lean_dec_ref(v___x_737_);
return v_bs_740_;
}
else
{
lean_object* v_v_742_; lean_object* v___x_743_; lean_object* v_bs_x27_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_v_742_ = lean_array_uget(v_bs_740_, v_i_739_);
v___x_743_ = lean_unsigned_to_nat(0u);
v_bs_x27_744_ = lean_array_uset(v_bs_740_, v_i_739_, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_737_);
v___x_746_ = lean_string_append(v___x_737_, v___x_745_);
v___x_747_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_742_, v___x_741_);
v___x_748_ = lean_string_append(v___x_746_, v___x_747_);
lean_dec_ref(v___x_747_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_750_ = lean_string_append(v___x_748_, v___x_749_);
v___x_751_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_739_, v___x_753_);
v___x_755_ = lean_array_uset(v_bs_x27_744_, v_i_739_, v___x_752_);
v_i_739_ = v___x_754_;
v_bs_740_ = v___x_755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_bs_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_757_, v_sz_boxed_761_, v_i_boxed_762_, v_bs_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_764_, size_t v_sz_765_, size_t v_i_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_a_770_; uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_766_, v_sz_765_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_767_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_819_; 
v_a_776_ = lean_array_uget_borrowed(v_as_764_, v_i_766_);
v_fst_777_ = lean_ctor_get(v_a_776_, 0);
v_snd_778_ = lean_ctor_get(v_a_776_, 1);
v_fst_779_ = lean_ctor_get(v_b_767_, 0);
v_snd_780_ = lean_ctor_get(v_b_767_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_b_767_);
if (v_isSharedCheck_819_ == 0)
{
v___x_782_ = v_b_767_;
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v_b_767_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_819_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_sub(v_fst_777_, v___x_784_);
v___x_786_ = lean_array_get_size(v_fst_779_);
v___x_787_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v___x_785_);
if (v_isShared_783_ == 0)
{
v___x_789_ = v___x_782_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_779_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_snd_780_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v_a_770_ = v___x_789_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___y_795_; lean_object* v___x_808_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___x_813_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_array_fget_borrowed(v_fst_779_, v___x_785_);
v___x_793_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_792_);
v___x_808_ = lean_array_get_size(v_snd_778_);
v___x_813_ = lean_nat_dec_eq(v___x_808_, v___x_791_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___y_816_; uint8_t v___x_818_; 
v___x_814_ = lean_nat_sub(v___x_808_, v___x_784_);
v___x_818_ = lean_nat_dec_le(v___x_791_, v___x_814_);
if (v___x_818_ == 0)
{
lean_inc(v___x_814_);
v___y_816_ = v___x_814_;
goto v___jp_815_;
}
else
{
v___y_816_ = v___x_791_;
goto v___jp_815_;
}
v___jp_815_:
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_le(v___y_816_, v___x_814_);
if (v___x_817_ == 0)
{
lean_dec(v___x_814_);
lean_inc(v___y_816_);
v___y_810_ = v___y_816_;
v___y_811_ = v___y_816_;
goto v___jp_809_;
}
else
{
v___y_810_ = v___y_816_;
v___y_811_ = v___x_814_;
goto v___jp_809_;
}
}
}
else
{
lean_inc(v_snd_778_);
v___y_795_ = v_snd_778_;
goto v___jp_794_;
}
v___jp_794_:
{
size_t v_sz_796_; size_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v_sz_796_ = lean_array_size(v___y_795_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_793_, v_sz_796_, v___x_797_, v___y_795_);
lean_inc(v___x_785_);
v___x_799_ = l_Array_extract___redArg(v_fst_779_, v___x_791_, v___x_785_);
v___x_800_ = l_Array_append___redArg(v___x_799_, v___x_798_);
v___x_801_ = l_Array_extract___redArg(v_fst_779_, v___x_785_, v___x_786_);
lean_dec(v_fst_779_);
v___x_802_ = l_Array_append___redArg(v___x_800_, v___x_801_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_array_get_size(v___x_798_);
lean_dec_ref(v___x_798_);
v___x_804_ = lean_nat_add(v_snd_780_, v___x_803_);
lean_dec(v_snd_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_804_);
lean_ctor_set(v___x_782_, 0, v___x_802_);
v___x_806_ = v___x_782_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v_a_770_ = v___x_806_;
goto v___jp_769_;
}
}
v___jp_809_:
{
lean_object* v___x_812_; 
lean_inc(v_snd_778_);
v___x_812_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_808_, v_snd_778_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
v___y_795_ = v___x_812_;
goto v___jp_794_;
}
}
}
}
v___jp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_766_, v___x_771_);
v_i_766_ = v___x_772_;
v_b_767_ = v_a_770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_){
_start:
{
size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v_sz_boxed_825_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_826_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_820_, v_sz_boxed_825_, v_i_boxed_826_, v_b_823_);
lean_dec_ref(v_as_820_);
return v_res_827_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_unsigned_to_nat(16u);
v___x_830_ = lean_mk_array(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_){
_start:
{
lean_object* v_a_850_; uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_847_);
return v___x_855_;
}
else
{
lean_object* v_a_856_; lean_object* v_snd_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_969_; 
v_a_856_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
v_snd_857_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_857_);
v_fst_858_ = lean_ctor_get(v_snd_857_, 0);
v_snd_859_ = lean_ctor_get(v_snd_857_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_snd_857_);
if (v_isSharedCheck_969_ == 0)
{
v___x_861_ = v_snd_857_;
v_isShared_862_ = v_isSharedCheck_969_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_inc(v_fst_858_);
lean_dec(v_snd_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_969_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_865_ = lean_array_size(v_snd_859_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_859_, v_sz_865_, v___x_866_, v___x_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___x_883_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_box(0);
v___x_883_ = l_IO_FS_readFile(v_fst_858_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_size_888_; lean_object* v_buckets_889_; lean_object* v___x_890_; lean_object* v___x_891_; size_t v_sz_892_; lean_object* v___x_893_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_937_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec(v_snd_859_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_n(v_a_884_, 2);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = lean_string_utf8_byte_size(v_a_884_);
v___x_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_886_, 0, v_a_884_);
lean_ctor_set(v___x_886_, 1, v___x_863_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
v___x_887_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_886_);
v_size_888_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_size_888_);
v_buckets_889_ = lean_ctor_get(v_a_868_, 1);
lean_inc_ref(v_buckets_889_);
lean_dec(v_a_868_);
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_891_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_884_, v___x_886_, v___x_885_, v___x_887_, v___x_890_);
lean_dec_ref_known(v___x_886_, 3);
v_sz_892_ = lean_array_size(v___x_891_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_892_, v___x_866_, v___x_891_);
v___x_943_ = lean_mk_empty_array_with_capacity(v_size_888_);
lean_dec(v_size_888_);
v___x_944_ = lean_array_get_size(v_buckets_889_);
v___x_945_ = lean_nat_dec_lt(v___x_863_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_buckets_889_);
v___y_937_ = v___x_943_;
goto v___jp_936_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_le(v___x_944_, v___x_944_);
if (v___x_946_ == 0)
{
if (v___x_945_ == 0)
{
lean_dec_ref(v_buckets_889_);
v___y_937_ = v___x_943_;
goto v___jp_936_;
}
else
{
size_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_usize_of_nat(v___x_944_);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_889_, v___x_866_, v___x_947_, v___x_943_);
lean_dec_ref(v_buckets_889_);
v___y_937_ = v___x_948_;
goto v___jp_936_;
}
}
else
{
size_t v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_usize_of_nat(v___x_944_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_889_, v___x_866_, v___x_949_, v___x_943_);
lean_dec_ref(v_buckets_889_);
v___y_937_ = v___x_950_;
goto v___jp_936_;
}
}
v___jp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_863_);
lean_ctor_set(v___x_861_, 0, v___x_893_);
v___x_898_ = v___x_861_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_863_);
v___x_898_ = v_reuseFailAlloc_921_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
size_t v_sz_899_; lean_object* v___x_900_; 
v_sz_899_ = lean_array_size(v___y_896_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_896_, v_sz_899_, v___x_866_, v___x_898_);
lean_dec_ref(v___y_896_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_fst_902_; lean_object* v_snd_903_; uint8_t v___x_904_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v_fst_902_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_fst_902_);
v_snd_903_ = lean_ctor_get(v_a_901_, 1);
lean_inc(v_snd_903_);
lean_dec(v_a_901_);
v___x_904_ = lean_nat_dec_lt(v___x_863_, v_snd_903_);
if (v___x_904_ == 0)
{
lean_dec(v_snd_903_);
lean_dec(v_fst_902_);
lean_dec(v_fst_858_);
v_a_850_ = v___x_869_;
goto v___jp_849_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_903_);
v___x_906_ = l_Nat_reprFast(v_snd_903_);
v___x_907_ = lean_string_append(v___x_905_, v___x_906_);
lean_dec_ref(v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_909_ = lean_string_append(v___x_907_, v___x_908_);
v___x_910_ = lean_nat_dec_eq(v_snd_903_, v___y_895_);
lean_dec(v_snd_903_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_871_ = v_fst_902_;
v___y_872_ = v___x_909_;
v___y_873_ = v___x_911_;
goto v___jp_870_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_871_ = v_fst_902_;
v___y_872_ = v___x_909_;
v___y_873_ = v___x_912_;
goto v___jp_870_;
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_fst_858_);
v_a_913_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_900_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_900_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
v___jp_922_:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_925_, v___y_924_, v___y_923_, v___y_927_);
lean_dec(v___y_927_);
lean_dec(v___y_925_);
v___y_895_ = v___y_926_;
v___y_896_ = v___x_928_;
goto v___jp_894_;
}
v___jp_929_:
{
uint8_t v___x_935_; 
v___x_935_ = lean_nat_dec_le(v___y_934_, v___y_931_);
if (v___x_935_ == 0)
{
lean_dec(v___y_931_);
lean_inc(v___y_934_);
v___y_923_ = v___y_934_;
v___y_924_ = v___y_930_;
v___y_925_ = v___y_932_;
v___y_926_ = v___y_933_;
v___y_927_ = v___y_934_;
goto v___jp_922_;
}
else
{
v___y_923_ = v___y_934_;
v___y_924_ = v___y_930_;
v___y_925_ = v___y_932_;
v___y_926_ = v___y_933_;
v___y_927_ = v___y_931_;
goto v___jp_922_;
}
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_array_get_size(v___y_937_);
v___x_940_ = lean_nat_dec_eq(v___x_939_, v___x_863_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_nat_sub(v___x_939_, v___x_938_);
v___x_942_ = lean_nat_dec_le(v___x_863_, v___x_941_);
if (v___x_942_ == 0)
{
lean_inc(v___x_941_);
v___y_930_ = v___y_937_;
v___y_931_ = v___x_941_;
v___y_932_ = v___x_939_;
v___y_933_ = v___x_938_;
v___y_934_ = v___x_941_;
goto v___jp_929_;
}
else
{
v___y_930_ = v___y_937_;
v___y_931_ = v___x_941_;
v___y_932_ = v___x_939_;
v___y_933_ = v___x_938_;
v___y_934_ = v___x_863_;
goto v___jp_929_;
}
}
else
{
v___y_895_ = v___x_938_;
v___y_896_ = v___y_937_;
goto v___jp_894_;
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref_known(v___x_883_, 1);
lean_dec(v_a_868_);
lean_del_object(v___x_861_);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_952_ = lean_string_append(v___x_951_, v_fst_858_);
lean_dec(v_fst_858_);
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = lean_array_get_size(v_snd_859_);
lean_dec(v_snd_859_);
v___x_956_ = l_Nat_reprFast(v___x_955_);
v___x_957_ = lean_string_append(v___x_954_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
v___x_960_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_dec_ref_known(v___x_960_, 1);
v_a_850_ = v___x_869_;
goto v___jp_849_;
}
else
{
return v___x_960_;
}
}
v___jp_870_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_874_ = lean_string_append(v___y_872_, v___y_873_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_876_ = lean_string_append(v___x_874_, v___x_875_);
v___x_877_ = lean_string_append(v___x_876_, v_fst_858_);
v___x_878_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_880_ = lean_array_to_list(v___y_871_);
v___x_881_ = l_String_intercalate(v___x_879_, v___x_880_);
v___x_882_ = l_IO_FS_writeFile(v_fst_858_, v___x_881_);
lean_dec_ref(v___x_881_);
lean_dec(v_fst_858_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_dec_ref_known(v___x_882_, 1);
v_a_850_ = v___x_869_;
goto v___jp_849_;
}
else
{
return v___x_882_;
}
}
else
{
lean_dec(v___y_871_);
lean_dec(v_fst_858_);
return v___x_878_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_del_object(v___x_861_);
lean_dec(v_snd_859_);
lean_dec(v_fst_858_);
v_a_961_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_867_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_867_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
v___jp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_846_, v___x_851_);
v_i_846_ = v___x_852_;
v_b_847_ = v_a_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_976_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_970_, v_sz_boxed_975_, v_i_boxed_976_, v_b_973_);
lean_dec_ref(v_as_970_);
return v_res_977_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_979_) == 0)
{
uint8_t v___x_980_; 
v___x_980_ = 0;
return v___x_980_;
}
else
{
lean_object* v_key_981_; lean_object* v_tail_982_; uint8_t v___x_983_; 
v_key_981_ = lean_ctor_get(v_x_979_, 0);
v_tail_982_ = lean_ctor_get(v_x_979_, 2);
v___x_983_ = lean_string_dec_eq(v_key_981_, v_a_978_);
if (v___x_983_ == 0)
{
v_x_979_ = v_tail_982_;
goto _start;
}
else
{
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec_ref(v_a_985_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_dec(v_b_990_);
lean_dec_ref(v_a_989_);
return v_x_991_;
}
else
{
lean_object* v_key_992_; lean_object* v_value_993_; lean_object* v_tail_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1006_; 
v_key_992_ = lean_ctor_get(v_x_991_, 0);
v_value_993_ = lean_ctor_get(v_x_991_, 1);
v_tail_994_ = lean_ctor_get(v_x_991_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_996_ = v_x_991_;
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_tail_994_);
lean_inc(v_value_993_);
lean_inc(v_key_992_);
lean_dec(v_x_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_string_dec_eq(v_key_992_, v_a_989_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_989_, v_b_990_, v_tail_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 2, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_key_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_value_993_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1004_; 
lean_dec(v_value_993_);
lean_dec(v_key_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v_b_990_);
lean_ctor_set(v___x_996_, 0, v_a_989_);
v___x_1004_ = v___x_996_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_989_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_b_990_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_tail_994_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
return v_x_1007_;
}
else
{
lean_object* v_key_1009_; lean_object* v_value_1010_; lean_object* v_tail_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1034_; 
v_key_1009_ = lean_ctor_get(v_x_1008_, 0);
v_value_1010_ = lean_ctor_get(v_x_1008_, 1);
v_tail_1011_ = lean_ctor_get(v_x_1008_, 2);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1013_ = v_x_1008_;
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_tail_1011_);
lean_inc(v_value_1010_);
lean_inc(v_key_1009_);
lean_dec(v_x_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v_fold_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1015_ = lean_array_get_size(v_x_1007_);
v___x_1016_ = lean_string_hash(v_key_1009_);
v___x_1017_ = 32ULL;
v___x_1018_ = lean_uint64_shift_right(v___x_1016_, v___x_1017_);
v_fold_1019_ = lean_uint64_xor(v___x_1016_, v___x_1018_);
v___x_1020_ = 16ULL;
v___x_1021_ = lean_uint64_shift_right(v_fold_1019_, v___x_1020_);
v___x_1022_ = lean_uint64_xor(v_fold_1019_, v___x_1021_);
v___x_1023_ = lean_uint64_to_usize(v___x_1022_);
v___x_1024_ = lean_usize_of_nat(v___x_1015_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_sub(v___x_1024_, v___x_1025_);
v___x_1027_ = lean_usize_land(v___x_1023_, v___x_1026_);
v___x_1028_ = lean_array_uget_borrowed(v_x_1007_, v___x_1027_);
lean_inc(v___x_1028_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 2, v___x_1028_);
v___x_1030_ = v___x_1013_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_key_1009_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_value_1010_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_array_uset(v_x_1007_, v___x_1027_, v___x_1030_);
v_x_1007_ = v___x_1031_;
v_x_1008_ = v_tail_1011_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1035_, lean_object* v_source_1036_, lean_object* v_target_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_array_get_size(v_source_1036_);
v___x_1039_ = lean_nat_dec_lt(v_i_1035_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec_ref(v_source_1036_);
lean_dec(v_i_1035_);
return v_target_1037_;
}
else
{
lean_object* v_es_1040_; lean_object* v___x_1041_; lean_object* v_source_1042_; lean_object* v_target_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_es_1040_ = lean_array_fget(v_source_1036_, v_i_1035_);
v___x_1041_ = lean_box(0);
v_source_1042_ = lean_array_fset(v_source_1036_, v_i_1035_, v___x_1041_);
v_target_1043_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1037_, v_es_1040_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_add(v_i_1035_, v___x_1044_);
lean_dec(v_i_1035_);
v_i_1035_ = v___x_1045_;
v_source_1036_ = v_source_1042_;
v_target_1037_ = v_target_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_nbuckets_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1048_ = lean_array_get_size(v_data_1047_);
v___x_1049_ = lean_unsigned_to_nat(2u);
v_nbuckets_1050_ = lean_nat_mul(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_mk_array(v_nbuckets_1050_, v___x_1052_);
v___x_1054_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1051_, v_data_1047_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v_size_1058_; lean_object* v_buckets_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1102_; 
v_size_1058_ = lean_ctor_get(v_m_1055_, 0);
v_buckets_1059_ = lean_ctor_get(v_m_1055_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_m_1055_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1061_ = v_m_1055_;
v_isShared_1062_ = v_isSharedCheck_1102_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_buckets_1059_);
lean_inc(v_size_1058_);
lean_dec(v_m_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1102_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; uint64_t v_fold_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v_bkt_1076_; uint8_t v___x_1077_; 
v___x_1063_ = lean_array_get_size(v_buckets_1059_);
v___x_1064_ = lean_string_hash(v_a_1056_);
v___x_1065_ = 32ULL;
v___x_1066_ = lean_uint64_shift_right(v___x_1064_, v___x_1065_);
v_fold_1067_ = lean_uint64_xor(v___x_1064_, v___x_1066_);
v___x_1068_ = 16ULL;
v___x_1069_ = lean_uint64_shift_right(v_fold_1067_, v___x_1068_);
v___x_1070_ = lean_uint64_xor(v_fold_1067_, v___x_1069_);
v___x_1071_ = lean_uint64_to_usize(v___x_1070_);
v___x_1072_ = lean_usize_of_nat(v___x_1063_);
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_sub(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_usize_land(v___x_1071_, v___x_1074_);
v_bkt_1076_ = lean_array_uget_borrowed(v_buckets_1059_, v___x_1075_);
v___x_1077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1056_, v_bkt_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v_size_x27_1079_; lean_object* v___x_1080_; lean_object* v_buckets_x27_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v_size_x27_1079_ = lean_nat_add(v_size_1058_, v___x_1078_);
lean_dec(v_size_1058_);
lean_inc(v_bkt_1076_);
v___x_1080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1056_);
lean_ctor_set(v___x_1080_, 1, v_b_1057_);
lean_ctor_set(v___x_1080_, 2, v_bkt_1076_);
v_buckets_x27_1081_ = lean_array_uset(v_buckets_1059_, v___x_1075_, v___x_1080_);
v___x_1082_ = lean_unsigned_to_nat(4u);
v___x_1083_ = lean_nat_mul(v_size_x27_1079_, v___x_1082_);
v___x_1084_ = lean_unsigned_to_nat(3u);
v___x_1085_ = lean_nat_div(v___x_1083_, v___x_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_array_get_size(v_buckets_x27_1081_);
v___x_1087_ = lean_nat_dec_le(v___x_1085_, v___x_1086_);
lean_dec(v___x_1085_);
if (v___x_1087_ == 0)
{
lean_object* v_val_1088_; lean_object* v___x_1090_; 
v_val_1088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1081_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_val_1088_);
lean_ctor_set(v___x_1061_, 0, v_size_x27_1079_);
v___x_1090_ = v___x_1061_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_size_x27_1079_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_val_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
lean_object* v___x_1093_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_buckets_x27_1081_);
lean_ctor_set(v___x_1061_, 0, v_size_x27_1079_);
v___x_1093_ = v___x_1061_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_size_x27_1079_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_buckets_x27_1081_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v_buckets_x27_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_inc(v_bkt_1076_);
v___x_1095_ = lean_box(0);
v_buckets_x27_1096_ = lean_array_uset(v_buckets_1059_, v___x_1075_, v___x_1095_);
v___x_1097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1056_, v_b_1057_, v_bkt_1076_);
v___x_1098_ = lean_array_uset(v_buckets_x27_1096_, v___x_1075_, v___x_1097_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1098_);
v___x_1100_ = v___x_1061_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_size_1058_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1103_, lean_object* v_fallback_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
lean_inc(v_fallback_1104_);
return v_fallback_1104_;
}
else
{
lean_object* v_key_1106_; lean_object* v_value_1107_; lean_object* v_tail_1108_; uint8_t v___x_1109_; 
v_key_1106_ = lean_ctor_get(v_x_1105_, 0);
v_value_1107_ = lean_ctor_get(v_x_1105_, 1);
v_tail_1108_ = lean_ctor_get(v_x_1105_, 2);
v___x_1109_ = lean_string_dec_eq(v_key_1106_, v_a_1103_);
if (v___x_1109_ == 0)
{
v_x_1105_ = v_tail_1108_;
goto _start;
}
else
{
lean_inc(v_value_1107_);
return v_value_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1111_, lean_object* v_fallback_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1111_, v_fallback_1112_, v_x_1113_);
lean_dec(v_x_1113_);
lean_dec(v_fallback_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1115_, lean_object* v_a_1116_, lean_object* v_fallback_1117_){
_start:
{
lean_object* v_buckets_1118_; lean_object* v___x_1119_; uint64_t v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v_fold_1123_; uint64_t v___x_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_buckets_1118_ = lean_ctor_get(v_m_1115_, 1);
v___x_1119_ = lean_array_get_size(v_buckets_1118_);
v___x_1120_ = lean_string_hash(v_a_1116_);
v___x_1121_ = 32ULL;
v___x_1122_ = lean_uint64_shift_right(v___x_1120_, v___x_1121_);
v_fold_1123_ = lean_uint64_xor(v___x_1120_, v___x_1122_);
v___x_1124_ = 16ULL;
v___x_1125_ = lean_uint64_shift_right(v_fold_1123_, v___x_1124_);
v___x_1126_ = lean_uint64_xor(v_fold_1123_, v___x_1125_);
v___x_1127_ = lean_uint64_to_usize(v___x_1126_);
v___x_1128_ = lean_usize_of_nat(v___x_1119_);
v___x_1129_ = ((size_t)1ULL);
v___x_1130_ = lean_usize_sub(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_usize_land(v___x_1127_, v___x_1130_);
v___x_1132_ = lean_array_uget_borrowed(v_buckets_1118_, v___x_1131_);
v___x_1133_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1116_, v_fallback_1117_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1134_, lean_object* v_a_1135_, lean_object* v_fallback_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1134_, v_a_1135_, v_fallback_1136_);
lean_dec(v_fallback_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v_m_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_b_1143_);
return v___x_1146_;
}
else
{
lean_object* v_a_1147_; lean_object* v_file_1148_; lean_object* v_pos_1149_; lean_object* v_option_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1176_; 
v_a_1147_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
v_file_1148_ = lean_ctor_get(v_a_1147_, 0);
v_pos_1149_ = lean_ctor_get(v_a_1147_, 1);
lean_inc_ref(v_pos_1149_);
v_option_1150_ = lean_ctor_get(v_a_1147_, 2);
v___x_1151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1148_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_file_1148_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1143_, v_file_1148_, v___x_1152_);
lean_dec_ref_known(v___x_1152_, 2);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1176_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snd_1155_);
lean_inc(v_fst_1154_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1176_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_line_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1174_; 
v_line_1159_ = lean_ctor_get(v_pos_1149_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_pos_1149_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_pos_1149_, 1);
lean_dec(v_unused_1175_);
v___x_1161_ = v_pos_1149_;
v_isShared_1162_ = v_isSharedCheck_1174_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_line_1159_);
lean_dec(v_pos_1149_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1174_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
lean_inc(v_option_1150_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_option_1150_);
lean_ctor_set(v___x_1157_, 0, v_line_1159_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_line_1159_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_option_1150_);
v___x_1164_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_array_push(v_snd_1155_, v___x_1164_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1165_);
lean_ctor_set(v___x_1161_, 0, v_fst_1154_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_fst_1154_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; 
lean_inc_ref(v_file_1148_);
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1143_, v_file_1148_, v___x_1167_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1142_, v___x_1169_);
v_i_1142_ = v___x_1170_;
v_b_1143_ = v___x_1168_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1177_, lean_object* v_sz_1178_, lean_object* v_i_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_){
_start:
{
size_t v_sz_boxed_1182_; size_t v_i_boxed_1183_; lean_object* v_res_1184_; 
v_sz_boxed_1182_ = lean_unbox_usize(v_sz_1178_);
lean_dec(v_sz_1178_);
v_i_boxed_1183_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1177_, v_sz_boxed_1182_, v_i_boxed_1183_, v_b_1180_);
lean_dec_ref(v_as_1177_);
return v_res_1184_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_unsigned_to_nat(16u);
v___x_1187_ = lean_mk_array(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_byFile_1190_; 
v___x_1188_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1189_ = lean_unsigned_to_nat(0u);
v_byFile_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1190_, 0, v___x_1189_);
lean_ctor_set(v_byFile_1190_, 1, v___x_1188_);
return v_byFile_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v_byFile_1194_; size_t v_sz_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v_byFile_1194_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1195_ = lean_array_size(v_records_1191_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1191_, v_sz_1195_, v___x_1196_, v_byFile_1194_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___y_1200_; lean_object* v_size_1212_; lean_object* v_buckets_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v_size_1212_ = lean_ctor_get(v_a_1198_, 0);
lean_inc(v_size_1212_);
v_buckets_1213_ = lean_ctor_get(v_a_1198_, 1);
lean_inc_ref(v_buckets_1213_);
lean_dec(v_a_1198_);
v___x_1214_ = lean_mk_empty_array_with_capacity(v_size_1212_);
lean_dec(v_size_1212_);
v___x_1215_ = lean_array_get_size(v_buckets_1213_);
v___x_1216_ = lean_nat_dec_lt(v___x_1193_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_buckets_1213_);
v___y_1200_ = v___x_1214_;
goto v___jp_1199_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_nat_dec_le(v___x_1215_, v___x_1215_);
if (v___x_1217_ == 0)
{
if (v___x_1216_ == 0)
{
lean_dec_ref(v_buckets_1213_);
v___y_1200_ = v___x_1214_;
goto v___jp_1199_;
}
else
{
size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_usize_of_nat(v___x_1215_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1213_, v___x_1196_, v___x_1218_, v___x_1214_);
lean_dec_ref(v_buckets_1213_);
v___y_1200_ = v___x_1219_;
goto v___jp_1199_;
}
}
else
{
size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_usize_of_nat(v___x_1215_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1213_, v___x_1196_, v___x_1220_, v___x_1214_);
lean_dec_ref(v_buckets_1213_);
v___y_1200_ = v___x_1221_;
goto v___jp_1199_;
}
}
v___jp_1199_:
{
lean_object* v___x_1201_; size_t v_sz_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
v_sz_1202_ = lean_array_size(v___y_1200_);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1200_, v_sz_1202_, v___x_1196_, v___x_1201_);
lean_dec_ref(v___y_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1211_);
v___x_1205_ = v___x_1203_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_dec(v___x_1203_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1201_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1201_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1197_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1197_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1230_);
lean_dec_ref(v_records_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1233_, lean_object* v_m_1234_, lean_object* v_a_1235_, lean_object* v_fallback_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1234_, v_a_1235_, v_fallback_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_, lean_object* v_fallback_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1238_, v_m_1239_, v_a_1240_, v_fallback_1241_);
lean_dec(v_fallback_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_m_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1244_, v_a_1245_, v_b_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_, lean_object* v_fallback_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1249_, v_a_1250_, v_fallback_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_, lean_object* v_fallback_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1253_, v_m_1254_, v_a_1255_, v_fallback_1256_);
lean_dec(v_fallback_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_m_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1258_, lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1259_, v_a_1260_, v_b_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1263_, lean_object* v___x_1264_, lean_object* v___x_1265_, lean_object* v_inst_1266_, lean_object* v_R_1267_, lean_object* v_a_1268_, lean_object* v_b_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1263_, v___x_1264_, v___x_1265_, v_a_1268_, v_b_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1271_, lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v_inst_1274_, lean_object* v_R_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1271_, v___x_1272_, v___x_1273_, v_inst_1274_, v_R_1275_, v_a_1276_, v_b_1277_);
lean_dec_ref(v___x_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v_n_1279_, lean_object* v_as_1280_, lean_object* v_lo_1281_, lean_object* v_hi_1282_, lean_object* v_w_1283_, lean_object* v_hlo_1284_, lean_object* v_hhi_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_1279_, v_as_1280_, v_lo_1281_, v_hi_1282_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v_n_1287_, lean_object* v_as_1288_, lean_object* v_lo_1289_, lean_object* v_hi_1290_, lean_object* v_w_1291_, lean_object* v_hlo_1292_, lean_object* v_hhi_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v_n_1287_, v_as_1288_, v_lo_1289_, v_hi_1290_, v_w_1291_, v_hlo_1292_, v_hhi_1293_);
lean_dec(v_hi_1290_);
lean_dec(v_n_1287_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1295_, lean_object* v_as_1296_, lean_object* v_lo_1297_, lean_object* v_hi_1298_, lean_object* v_w_1299_, lean_object* v_hlo_1300_, lean_object* v_hhi_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1295_, v_as_1296_, v_lo_1297_, v_hi_1298_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1303_, lean_object* v_as_1304_, lean_object* v_lo_1305_, lean_object* v_hi_1306_, lean_object* v_w_1307_, lean_object* v_hlo_1308_, lean_object* v_hhi_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1303_, v_as_1304_, v_lo_1305_, v_hi_1306_, v_w_1307_, v_hlo_1308_, v_hhi_1309_);
lean_dec(v_hi_1306_);
lean_dec(v_n_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1311_, lean_object* v_a_1312_, lean_object* v_fallback_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1312_, v_fallback_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_a_1317_, lean_object* v_fallback_1318_, lean_object* v_x_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1316_, v_a_1317_, v_fallback_1318_, v_x_1319_);
lean_dec(v_x_1319_);
lean_dec(v_fallback_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1321_, lean_object* v_a_1322_, lean_object* v_x_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1322_, v_x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1325_, lean_object* v_a_1326_, lean_object* v_x_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1325_, v_a_1326_, v_x_1327_);
lean_dec(v_x_1327_);
lean_dec_ref(v_a_1326_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1330_, lean_object* v_data_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1334_, v_b_1335_, v_x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1338_, lean_object* v_a_1339_, lean_object* v_fallback_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1339_, v_fallback_1340_, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1343_, lean_object* v_a_1344_, lean_object* v_fallback_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1343_, v_a_1344_, v_fallback_1345_, v_x_1346_);
lean_dec(v_x_1346_);
lean_dec(v_fallback_1345_);
lean_dec(v_a_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1348_, lean_object* v_a_1349_, lean_object* v_x_1350_){
_start:
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1349_, v_x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1352_, lean_object* v_a_1353_, lean_object* v_x_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1352_, v_a_1353_, v_x_1354_);
lean_dec(v_x_1354_);
lean_dec(v_a_1353_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1357_, lean_object* v_data_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1360_, lean_object* v_a_1361_, lean_object* v_b_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1361_, v_b_1362_, v_x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v_n_1365_, lean_object* v_lo_1366_, lean_object* v_hi_1367_, lean_object* v_hhi_1368_, lean_object* v_pivot_1369_, lean_object* v_as_1370_, lean_object* v_i_1371_, lean_object* v_k_1372_, lean_object* v_ilo_1373_, lean_object* v_ik_1374_, lean_object* v_w_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_1367_, v_pivot_1369_, v_as_1370_, v_i_1371_, v_k_1372_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v_n_1377_, lean_object* v_lo_1378_, lean_object* v_hi_1379_, lean_object* v_hhi_1380_, lean_object* v_pivot_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_k_1384_, lean_object* v_ilo_1385_, lean_object* v_ik_1386_, lean_object* v_w_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v_n_1377_, v_lo_1378_, v_hi_1379_, v_hhi_1380_, v_pivot_1381_, v_as_1382_, v_i_1383_, v_k_1384_, v_ilo_1385_, v_ik_1386_, v_w_1387_);
lean_dec(v_hi_1379_);
lean_dec(v_lo_1378_);
lean_dec(v_n_1377_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1389_, lean_object* v_lo_1390_, lean_object* v_hi_1391_, lean_object* v_hhi_1392_, lean_object* v_pivot_1393_, lean_object* v_as_1394_, lean_object* v_i_1395_, lean_object* v_k_1396_, lean_object* v_ilo_1397_, lean_object* v_ik_1398_, lean_object* v_w_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1391_, v_pivot_1393_, v_as_1394_, v_i_1395_, v_k_1396_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1401_, lean_object* v_lo_1402_, lean_object* v_hi_1403_, lean_object* v_hhi_1404_, lean_object* v_pivot_1405_, lean_object* v_as_1406_, lean_object* v_i_1407_, lean_object* v_k_1408_, lean_object* v_ilo_1409_, lean_object* v_ik_1410_, lean_object* v_w_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1401_, v_lo_1402_, v_hi_1403_, v_hhi_1404_, v_pivot_1405_, v_as_1406_, v_i_1407_, v_k_1408_, v_ilo_1409_, v_ik_1410_, v_w_1411_);
lean_dec_ref(v_pivot_1405_);
lean_dec(v_hi_1403_);
lean_dec(v_lo_1402_);
lean_dec(v_n_1401_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1413_, lean_object* v_i_1414_, lean_object* v_source_1415_, lean_object* v_target_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1414_, v_source_1415_, v_target_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1418_, lean_object* v_i_1419_, lean_object* v_source_1420_, lean_object* v_target_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1419_, v_source_1420_, v_target_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1424_, v_x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1428_, v_x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_enable_initializer_execution();
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_compacted_region_free(v_region_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_1444_, lean_object* v_k_1445_, uint8_t v_v_1446_){
_start:
{
lean_object* v_map_1447_; uint8_t v_hasTrace_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1462_; 
v_map_1447_ = lean_ctor_get(v_o_1444_, 0);
v_hasTrace_1448_ = lean_ctor_get_uint8(v_o_1444_, sizeof(void*)*1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_o_1444_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1450_ = v_o_1444_;
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_map_1447_);
lean_dec(v_o_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1452_, 0, v_v_1446_);
lean_inc(v_k_1445_);
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1445_, v___x_1452_, v_map_1447_);
if (v_hasTrace_1448_ == 0)
{
lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_1455_ = l_Lean_Name_isPrefixOf(v___x_1454_, v_k_1445_);
lean_dec(v_k_1445_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1457_ = v___x_1450_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1453_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*1, v___x_1455_);
return v___x_1457_;
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_k_1445_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*1, v_hasTrace_1448_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_1463_, lean_object* v_k_1464_, lean_object* v_v_1465_){
_start:
{
uint8_t v_v_boxed_1466_; lean_object* v_res_1467_; 
v_v_boxed_1466_ = lean_unbox(v_v_1465_);
v_res_1467_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_1463_, v_k_1464_, v_v_boxed_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_opts_1468_, lean_object* v_opt_1469_){
_start:
{
lean_object* v_name_1470_; lean_object* v_defValue_1471_; lean_object* v_map_1472_; lean_object* v___x_1473_; 
v_name_1470_ = lean_ctor_get(v_opt_1469_, 0);
v_defValue_1471_ = lean_ctor_get(v_opt_1469_, 1);
v_map_1472_ = lean_ctor_get(v_opts_1468_, 0);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1472_, v_name_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_unbox(v_defValue_1471_);
return v___x_1474_;
}
else
{
lean_object* v_val_1475_; 
v_val_1475_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___x_1473_, 1);
if (lean_obj_tag(v_val_1475_) == 1)
{
uint8_t v_v_1476_; 
v_v_1476_ = lean_ctor_get_uint8(v_val_1475_, 0);
lean_dec_ref_known(v_val_1475_, 0);
return v_v_1476_;
}
else
{
uint8_t v___x_1477_; 
lean_dec(v_val_1475_);
v___x_1477_ = lean_unbox(v_defValue_1471_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_opts_1478_, lean_object* v_opt_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2(v_opts_1478_, v_opt_1479_);
lean_dec_ref(v_opt_1479_);
lean_dec_ref(v_opts_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_opts_1482_, lean_object* v_opt_1483_){
_start:
{
lean_object* v_name_1484_; lean_object* v_defValue_1485_; lean_object* v_map_1486_; lean_object* v___x_1487_; 
v_name_1484_ = lean_ctor_get(v_opt_1483_, 0);
v_defValue_1485_ = lean_ctor_get(v_opt_1483_, 1);
v_map_1486_ = lean_ctor_get(v_opts_1482_, 0);
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1486_, v_name_1484_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_inc(v_defValue_1485_);
return v_defValue_1485_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1487_, 1);
if (lean_obj_tag(v_val_1488_) == 3)
{
lean_object* v_v_1489_; 
v_v_1489_ = lean_ctor_get(v_val_1488_, 0);
lean_inc(v_v_1489_);
lean_dec_ref_known(v_val_1488_, 1);
return v_v_1489_;
}
else
{
lean_dec(v_val_1488_);
lean_inc(v_defValue_1485_);
return v_defValue_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_opts_1490_, lean_object* v_opt_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3(v_opts_1490_, v_opt_1491_);
lean_dec_ref(v_opt_1491_);
lean_dec_ref(v_opts_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16(lean_object* v_as_1493_, size_t v_i_1494_, size_t v_stop_1495_, lean_object* v_b_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_eq(v_i_1494_, v_stop_1495_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v_fst_1499_; lean_object* v_snd_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; 
v___x_1498_ = lean_array_uget_borrowed(v_as_1493_, v_i_1494_);
v_fst_1499_ = lean_ctor_get(v___x_1498_, 0);
v_snd_1500_ = lean_ctor_get(v___x_1498_, 1);
v___x_1501_ = lean_unbox(v_snd_1500_);
lean_inc(v_fst_1499_);
v___x_1502_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_1496_, v_fst_1499_, v___x_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1494_, v___x_1503_);
v_i_1494_ = v___x_1504_;
v_b_1496_ = v___x_1502_;
goto _start;
}
else
{
return v_b_1496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16___boxed(lean_object* v_as_1506_, lean_object* v_i_1507_, lean_object* v_stop_1508_, lean_object* v_b_1509_){
_start:
{
size_t v_i_boxed_1510_; size_t v_stop_boxed_1511_; lean_object* v_res_1512_; 
v_i_boxed_1510_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_stop_boxed_1511_ = lean_unbox_usize(v_stop_1508_);
lean_dec(v_stop_1508_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16(v_as_1506_, v_i_boxed_1510_, v_stop_boxed_1511_, v_b_1509_);
lean_dec_ref(v_as_1506_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0(uint8_t v_anyFailed_1513_, lean_object* v___x_1514_, lean_object* v_____r_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(v_anyFailed_1513_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1514_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0___boxed(lean_object* v_anyFailed_1522_, lean_object* v___x_1523_, lean_object* v_____r_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v_anyFailed_boxed_1528_; lean_object* v_res_1529_; 
v_anyFailed_boxed_1528_ = lean_unbox(v_anyFailed_1522_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0(v_anyFailed_boxed_1528_, v___x_1523_, v_____r_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12(lean_object* v___x_1530_, lean_object* v_as_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_b_1534_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_b_1534_);
return v___x_1537_;
}
else
{
lean_object* v_a_1538_; lean_object* v_message_1539_; lean_object* v___x_1540_; uint8_t v_anyFailed_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_a_1538_ = lean_array_uget_borrowed(v_as_1531_, v_i_1533_);
v_message_1539_ = lean_ctor_get(v_a_1538_, 1);
v___x_1540_ = lean_unsigned_to_nat(0u);
v_anyFailed_1541_ = lean_nat_dec_eq(v___x_1530_, v___x_1540_);
lean_inc_ref(v_message_1539_);
v___x_1542_ = l_Lean_SerialMessage_toString(v_message_1539_, v_anyFailed_1541_);
v___x_1543_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_1542_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; 
lean_dec_ref_known(v___x_1543_, 1);
v___x_1544_ = lean_box(0);
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1533_, v___x_1545_);
v_i_1533_ = v___x_1546_;
v_b_1534_ = v___x_1544_;
goto _start;
}
else
{
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object* v___x_1548_, lean_object* v_as_1549_, lean_object* v_sz_1550_, lean_object* v_i_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_){
_start:
{
size_t v_sz_boxed_1554_; size_t v_i_boxed_1555_; lean_object* v_res_1556_; 
v_sz_boxed_1554_ = lean_unbox_usize(v_sz_1550_);
lean_dec(v_sz_1550_);
v_i_boxed_1555_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12(v___x_1548_, v_as_1549_, v_sz_boxed_1554_, v_i_boxed_1555_, v_b_1552_);
lean_dec_ref(v_as_1549_);
lean_dec(v___x_1548_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13(lean_object* v___x_1559_, lean_object* v_as_1560_, size_t v_sz_1561_, size_t v_i_1562_, lean_object* v_b_1563_){
_start:
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_usize_dec_lt(v_i_1562_, v_sz_1561_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_b_1563_);
return v___x_1566_;
}
else
{
lean_object* v_a_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1567_ = lean_array_uget_borrowed(v_as_1560_, v_i_1562_);
v_fst_1568_ = lean_ctor_get(v_a_1567_, 0);
v_snd_1569_ = lean_ctor_get(v_a_1567_, 1);
v___x_1570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__0));
lean_inc(v_fst_1568_);
v___x_1571_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1568_, v___x_1565_);
v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___closed__1));
v___x_1574_ = lean_string_append(v___x_1572_, v___x_1573_);
v___x_1575_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1575_, 1);
v___x_1576_ = lean_box(0);
v_sz_1577_ = lean_array_size(v_snd_1569_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__12(v___x_1559_, v_snd_1569_, v_sz_1577_, v___x_1578_, v___x_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
size_t v___x_1580_; size_t v___x_1581_; 
lean_dec_ref_known(v___x_1579_, 1);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_add(v_i_1562_, v___x_1580_);
v_i_1562_ = v___x_1581_;
v_b_1563_ = v___x_1576_;
goto _start;
}
else
{
return v___x_1579_;
}
}
else
{
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13___boxed(lean_object* v___x_1583_, lean_object* v_as_1584_, lean_object* v_sz_1585_, lean_object* v_i_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_){
_start:
{
size_t v_sz_boxed_1589_; size_t v_i_boxed_1590_; lean_object* v_res_1591_; 
v_sz_boxed_1589_ = lean_unbox_usize(v_sz_1585_);
lean_dec(v_sz_1585_);
v_i_boxed_1590_ = lean_unbox_usize(v_i_1586_);
lean_dec(v_i_1586_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13(v___x_1583_, v_as_1584_, v_sz_boxed_1589_, v_i_boxed_1590_, v_b_1587_);
lean_dec_ref(v_as_1584_);
lean_dec(v___x_1583_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7(lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
return v_x_1592_;
}
else
{
lean_object* v_key_1594_; lean_object* v_value_1595_; lean_object* v_tail_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_key_1594_ = lean_ctor_get(v_x_1593_, 0);
v_value_1595_ = lean_ctor_get(v_x_1593_, 1);
v_tail_1596_ = lean_ctor_get(v_x_1593_, 2);
lean_inc(v_value_1595_);
lean_inc(v_key_1594_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_key_1594_);
lean_ctor_set(v___x_1597_, 1, v_value_1595_);
v___x_1598_ = lean_array_push(v_x_1592_, v___x_1597_);
v_x_1592_ = v___x_1598_;
v_x_1593_ = v_tail_1596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7(v_x_1600_, v_x_1601_);
lean_dec(v_x_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8(lean_object* v_as_1603_, size_t v_i_1604_, size_t v_stop_1605_, lean_object* v_b_1606_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_eq(v_i_1604_, v_stop_1605_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; 
v___x_1608_ = lean_array_uget_borrowed(v_as_1603_, v_i_1604_);
v___x_1609_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__7(v_b_1606_, v___x_1608_);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1604_, v___x_1610_);
v_i_1604_ = v___x_1611_;
v_b_1606_ = v___x_1609_;
goto _start;
}
else
{
return v_b_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object* v_as_1613_, lean_object* v_i_1614_, lean_object* v_stop_1615_, lean_object* v_b_1616_){
_start:
{
size_t v_i_boxed_1617_; size_t v_stop_boxed_1618_; lean_object* v_res_1619_; 
v_i_boxed_1617_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v_stop_boxed_1618_ = lean_unbox_usize(v_stop_1615_);
lean_dec(v_stop_1615_);
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8(v_as_1613_, v_i_boxed_1617_, v_stop_boxed_1618_, v_b_1616_);
lean_dec_ref(v_as_1613_);
return v_res_1619_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0(void){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
lean_ctor_set(v___x_1625_, 3, v___x_1624_);
lean_ctor_set(v___x_1625_, 4, v___x_1623_);
lean_ctor_set(v___x_1625_, 5, v___x_1623_);
lean_ctor_set(v___x_1625_, 6, v___x_1623_);
lean_ctor_set(v___x_1625_, 7, v___x_1623_);
lean_ctor_set(v___x_1625_, 8, v___x_1623_);
lean_ctor_set(v___x_1625_, 9, v___x_1623_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_unsigned_to_nat(32u);
v___x_1627_ = lean_mk_empty_array_with_capacity(v___x_1626_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4(void){
_start:
{
size_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1629_ = ((size_t)5ULL);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_unsigned_to_nat(32u);
v___x_1632_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___x_1633_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__3);
v___x_1634_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v___x_1632_);
lean_ctor_set(v___x_1634_, 2, v___x_1630_);
lean_ctor_set(v___x_1634_, 3, v___x_1630_);
lean_ctor_set_usize(v___x_1634_, 4, v___x_1629_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1635_ = lean_box(1);
v___x_1636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__4);
v___x_1637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__1);
v___x_1638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
lean_ctor_set(v___x_1638_, 2, v___x_1635_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28(lean_object* v_msgData_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v_env_1644_; lean_object* v_options_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1643_ = lean_st_ref_get(v___y_1641_);
v_env_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_ref(v_env_1644_);
lean_dec(v___x_1643_);
v_options_1645_ = lean_ctor_get(v___y_1640_, 2);
v___x_1646_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2);
v___x_1647_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5);
lean_inc_ref(v_options_1645_);
v___x_1648_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1648_, 0, v_env_1644_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
lean_ctor_set(v___x_1648_, 2, v___x_1647_);
lean_ctor_set(v___x_1648_, 3, v_options_1645_);
v___x_1649_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_msgData_1639_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___boxed(lean_object* v_msgData_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28(v_msgData_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg(lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_ref_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
v_ref_1660_ = lean_ctor_get(v___y_1657_, 5);
v___x_1661_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28(v_msg_1656_, v___y_1657_, v___y_1658_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_inc(v_ref_1660_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_ref_1660_);
lean_ctor_set(v___x_1666_, 1, v_a_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 0, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg___boxed(lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg(v_msg_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg(lean_object* v_ref_1676_, lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_fileName_1681_; lean_object* v_fileMap_1682_; lean_object* v_options_1683_; lean_object* v_currRecDepth_1684_; lean_object* v_maxRecDepth_1685_; lean_object* v_ref_1686_; lean_object* v_currNamespace_1687_; lean_object* v_openDecls_1688_; lean_object* v_initHeartbeats_1689_; lean_object* v_maxHeartbeats_1690_; lean_object* v_quotContext_1691_; lean_object* v_currMacroScope_1692_; uint8_t v_diag_1693_; lean_object* v_cancelTk_x3f_1694_; uint8_t v_suppressElabErrors_1695_; lean_object* v_inheritedTraceOptions_1696_; lean_object* v_ref_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_fileName_1681_ = lean_ctor_get(v___y_1678_, 0);
v_fileMap_1682_ = lean_ctor_get(v___y_1678_, 1);
v_options_1683_ = lean_ctor_get(v___y_1678_, 2);
v_currRecDepth_1684_ = lean_ctor_get(v___y_1678_, 3);
v_maxRecDepth_1685_ = lean_ctor_get(v___y_1678_, 4);
v_ref_1686_ = lean_ctor_get(v___y_1678_, 5);
v_currNamespace_1687_ = lean_ctor_get(v___y_1678_, 6);
v_openDecls_1688_ = lean_ctor_get(v___y_1678_, 7);
v_initHeartbeats_1689_ = lean_ctor_get(v___y_1678_, 8);
v_maxHeartbeats_1690_ = lean_ctor_get(v___y_1678_, 9);
v_quotContext_1691_ = lean_ctor_get(v___y_1678_, 10);
v_currMacroScope_1692_ = lean_ctor_get(v___y_1678_, 11);
v_diag_1693_ = lean_ctor_get_uint8(v___y_1678_, sizeof(void*)*14);
v_cancelTk_x3f_1694_ = lean_ctor_get(v___y_1678_, 12);
v_suppressElabErrors_1695_ = lean_ctor_get_uint8(v___y_1678_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1696_ = lean_ctor_get(v___y_1678_, 13);
v_ref_1697_ = l_Lean_replaceRef(v_ref_1676_, v_ref_1686_);
lean_inc_ref(v_inheritedTraceOptions_1696_);
lean_inc(v_cancelTk_x3f_1694_);
lean_inc(v_currMacroScope_1692_);
lean_inc(v_quotContext_1691_);
lean_inc(v_maxHeartbeats_1690_);
lean_inc(v_initHeartbeats_1689_);
lean_inc(v_openDecls_1688_);
lean_inc(v_currNamespace_1687_);
lean_inc(v_maxRecDepth_1685_);
lean_inc(v_currRecDepth_1684_);
lean_inc_ref(v_options_1683_);
lean_inc_ref(v_fileMap_1682_);
lean_inc_ref(v_fileName_1681_);
v___x_1698_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1698_, 0, v_fileName_1681_);
lean_ctor_set(v___x_1698_, 1, v_fileMap_1682_);
lean_ctor_set(v___x_1698_, 2, v_options_1683_);
lean_ctor_set(v___x_1698_, 3, v_currRecDepth_1684_);
lean_ctor_set(v___x_1698_, 4, v_maxRecDepth_1685_);
lean_ctor_set(v___x_1698_, 5, v_ref_1697_);
lean_ctor_set(v___x_1698_, 6, v_currNamespace_1687_);
lean_ctor_set(v___x_1698_, 7, v_openDecls_1688_);
lean_ctor_set(v___x_1698_, 8, v_initHeartbeats_1689_);
lean_ctor_set(v___x_1698_, 9, v_maxHeartbeats_1690_);
lean_ctor_set(v___x_1698_, 10, v_quotContext_1691_);
lean_ctor_set(v___x_1698_, 11, v_currMacroScope_1692_);
lean_ctor_set(v___x_1698_, 12, v_cancelTk_x3f_1694_);
lean_ctor_set(v___x_1698_, 13, v_inheritedTraceOptions_1696_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*14, v_diag_1693_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*14 + 1, v_suppressElabErrors_1695_);
v___x_1699_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg(v_msg_1677_, v___x_1698_, v___y_1679_);
lean_dec_ref_known(v___x_1698_, 14);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg___boxed(lean_object* v_ref_1700_, lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg(v_ref_1700_, v_msg_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v_ref_1700_);
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__0));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__2));
v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__4));
v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__6));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__8));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__10));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__12));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg(lean_object* v_msg_1727_, lean_object* v_declHint_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_env_1732_; uint8_t v___x_1733_; 
v___x_1731_ = lean_st_ref_get(v___y_1729_);
v_env_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc_ref(v_env_1732_);
lean_dec(v___x_1731_);
v___x_1733_ = l_Lean_Name_isAnonymous(v_declHint_1728_);
if (v___x_1733_ == 0)
{
uint8_t v_isExporting_1734_; 
v_isExporting_1734_ = lean_ctor_get_uint8(v_env_1732_, sizeof(void*)*8);
if (v_isExporting_1734_ == 0)
{
lean_object* v___x_1735_; 
lean_dec_ref(v_env_1732_);
lean_dec(v_declHint_1728_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_msg_1727_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
lean_inc_ref(v_env_1732_);
v___x_1736_ = l_Lean_Environment_setExporting(v_env_1732_, v___x_1733_);
lean_inc(v_declHint_1728_);
lean_inc_ref(v___x_1736_);
v___x_1737_ = l_Lean_Environment_contains(v___x_1736_, v_declHint_1728_, v_isExporting_1734_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref(v___x_1736_);
lean_dec_ref(v_env_1732_);
lean_dec(v_declHint_1728_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_msg_1727_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_c_1744_; lean_object* v___x_1745_; 
v___x_1739_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__2);
v___x_1740_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27_spec__28___closed__5);
v___x_1741_ = l_Lean_Options_empty;
v___x_1742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1736_);
lean_ctor_set(v___x_1742_, 1, v___x_1739_);
lean_ctor_set(v___x_1742_, 2, v___x_1740_);
lean_ctor_set(v___x_1742_, 3, v___x_1741_);
lean_inc(v_declHint_1728_);
v___x_1743_ = l_Lean_MessageData_ofConstName(v_declHint_1728_, v___x_1733_);
v_c_1744_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1744_, 0, v___x_1742_);
lean_ctor_set(v_c_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1732_, v_declHint_1728_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v_env_1732_);
lean_dec(v_declHint_1728_);
v___x_1746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v_c_1744_);
v___x_1748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__3);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_MessageData_note(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_msg_1727_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v_val_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1788_; 
v_val_1753_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1755_ = v___x_1745_;
v_isShared_1756_ = v_isSharedCheck_1788_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_val_1753_);
lean_dec(v___x_1745_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1788_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_mod_1760_; uint8_t v___x_1761_; 
v___x_1757_ = lean_box(0);
v___x_1758_ = l_Lean_Environment_header(v_env_1732_);
lean_dec_ref(v_env_1732_);
v___x_1759_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1758_);
v_mod_1760_ = lean_array_get(v___x_1757_, v___x_1759_, v_val_1753_);
lean_dec(v_val_1753_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Lean_isPrivateName(v_declHint_1728_);
lean_dec(v_declHint_1728_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__5);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_c_1744_);
v___x_1764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__7);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_MessageData_ofName(v_mod_1760_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__9);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_note(v___x_1769_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_msg_1727_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1771_);
v___x_1773_ = v___x_1755_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__1);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_c_1744_);
v___x_1777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__11);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_MessageData_ofName(v_mod_1760_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___closed__13);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_MessageData_note(v___x_1782_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_msg_1727_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1784_);
v___x_1786_ = v___x_1755_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref(v_env_1732_);
lean_dec(v_declHint_1728_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_msg_1727_);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg___boxed(lean_object* v_msg_1790_, lean_object* v_declHint_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg(v_msg_1790_, v_declHint_1791_, v___y_1792_);
lean_dec(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24(lean_object* v_msg_1795_, lean_object* v_declHint_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1810_; 
v___x_1800_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg(v_msg_1795_, v_declHint_1796_, v___y_1798_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1810_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1810_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1805_ = l_Lean_unknownIdentifierMessageTag;
v___x_1806_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_a_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1806_);
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24___boxed(lean_object* v_msg_1811_, lean_object* v_declHint_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24(v_msg_1811_, v_declHint_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg(lean_object* v_ref_1817_, lean_object* v_msg_1818_, lean_object* v_declHint_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v_a_1824_; lean_object* v___x_1825_; 
v___x_1823_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24(v_msg_1818_, v_declHint_1819_, v___y_1820_, v___y_1821_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg(v_ref_1817_, v_a_1824_, v___y_1820_, v___y_1821_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg___boxed(lean_object* v_ref_1826_, lean_object* v_msg_1827_, lean_object* v_declHint_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg(v_ref_1826_, v_msg_1827_, v_declHint_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v_ref_1826_);
return v_res_1832_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__0));
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__2));
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg(lean_object* v_ref_1839_, lean_object* v_constName_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1844_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__1);
v___x_1845_ = 0;
lean_inc(v_constName_1840_);
v___x_1846_ = l_Lean_MessageData_ofConstName(v_constName_1840_, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1844_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___closed__3);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg(v_ref_1839_, v___x_1849_, v_constName_1840_, v___y_1841_, v___y_1842_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg___boxed(lean_object* v_ref_1851_, lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg(v_ref_1851_, v_constName_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v_ref_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg(lean_object* v_constName_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_ref_1861_; lean_object* v___x_1862_; 
v_ref_1861_ = lean_ctor_get(v___y_1858_, 5);
v___x_1862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg(v_ref_1861_, v_constName_1857_, v___y_1858_, v___y_1859_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_constName_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg(v_constName_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7(lean_object* v_constName_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_env_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_st_ref_get(v___y_1870_);
v_env_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_env_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = 0;
lean_inc(v_constName_1868_);
v___x_1875_ = l_Lean_Environment_find_x3f(v_env_1873_, v_constName_1868_, v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg(v_constName_1868_, v___y_1869_, v___y_1870_);
return v___x_1876_;
}
else
{
lean_object* v_val_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_constName_1868_);
v_val_1877_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_val_1877_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 0);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_val_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7___boxed(lean_object* v_constName_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7(v_constName_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_declName_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
lean_inc(v_declName_1890_);
v___x_1894_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7(v_declName_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1922_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1921_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1921_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v_env_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_st_ref_get(v___y_1892_);
v_env_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc_ref(v_env_1899_);
lean_dec(v___x_1898_);
v___x_1900_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1899_, v_declName_1890_);
lean_dec(v_declName_1890_);
lean_dec_ref(v_env_1899_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1901_);
v___x_1903_ = v___x_1896_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
else
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1920_; 
v_val_1905_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1907_ = v___x_1900_;
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v___x_1900_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v_env_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1909_ = lean_st_ref_get(v___y_1892_);
v_env_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_env_1910_);
lean_dec(v___x_1909_);
v___x_1911_ = lean_box(0);
v___x_1912_ = l_Lean_Environment_allImportedModuleNames(v_env_1910_);
lean_dec_ref(v_env_1910_);
v___x_1913_ = lean_array_get(v___x_1911_, v___x_1912_, v_val_1905_);
lean_dec(v_val_1905_);
lean_dec_ref(v___x_1912_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1913_);
v___x_1915_ = v___x_1907_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1915_);
v___x_1917_ = v___x_1896_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_declName_1890_);
v_a_1923_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1894_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1894_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_declName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5(v_declName_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(lean_object* v_declName_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; lean_object* v_env_1940_; lean_object* v___x_1941_; lean_object* v_env_1942_; lean_object* v___x_1943_; lean_object* v_toEnvExtension_1944_; lean_object* v_asyncMode_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1939_ = lean_st_ref_get(v___y_1937_);
v_env_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_ref(v_env_1940_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_st_ref_get(v___y_1937_);
v_env_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref(v_env_1942_);
lean_dec(v___x_1941_);
v___x_1943_ = l_Lean_declRangeExt;
v_toEnvExtension_1944_ = lean_ctor_get(v___x_1943_, 0);
v_asyncMode_1945_ = lean_ctor_get(v_toEnvExtension_1944_, 2);
v___x_1946_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1947_ = 0;
lean_inc(v_declName_1936_);
v___x_1948_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1946_, v___x_1943_, v_env_1940_, v_declName_1936_, v_asyncMode_1945_, v___x_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = 1;
v___x_1950_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1946_, v___x_1943_, v_env_1942_, v_declName_1936_, v_asyncMode_1945_, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; 
lean_dec_ref(v_env_1942_);
lean_dec(v_declName_1936_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1948_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg___boxed(lean_object* v_declName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(v_declName_1953_, v___y_1954_);
lean_dec(v___y_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg(lean_object* v_declName_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v_env_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1960_ = lean_st_ref_get(v___y_1958_);
v_env_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc_ref(v_env_1961_);
lean_dec(v___x_1960_);
v___x_1962_ = l_Lean_isRecCore(v_env_1961_, v_declName_1957_);
v___x_1963_ = lean_box(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg___boxed(lean_object* v_declName_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg(v_declName_1965_, v___y_1966_);
lean_dec(v___y_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_declName_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_ranges_1974_; lean_object* v___x_1980_; lean_object* v_env_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; uint8_t v___y_1989_; uint8_t v___x_1993_; 
v___x_1980_ = lean_st_ref_get(v___y_1971_);
v_env_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref_n(v_env_1981_, 2);
lean_dec(v___x_1980_);
lean_inc_n(v_declName_1969_, 2);
v___x_1982_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg(v_declName_1969_, v___y_1971_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
v___x_1993_ = l_Lean_isAuxRecursor(v_env_1981_, v_declName_1969_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
lean_inc(v_declName_1969_);
v___x_1994_ = l_Lean_isNoConfusion(v_env_1981_, v_declName_1969_);
v___y_1989_ = v___x_1994_;
goto v___jp_1988_;
}
else
{
lean_dec_ref(v_env_1981_);
v___y_1989_ = v___x_1993_;
goto v___jp_1988_;
}
v___jp_1973_:
{
if (lean_obj_tag(v_ranges_1974_) == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = l_Lean_builtinDeclRanges;
v___x_1976_ = lean_st_ref_get(v___x_1975_);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1976_, v_declName_1969_);
lean_dec(v_declName_1969_);
lean_dec(v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; 
lean_dec(v_declName_1969_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_ranges_1974_);
return v___x_1979_;
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; 
v___x_1985_ = l_Lean_Name_getPrefix(v_declName_1969_);
v___x_1986_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(v___x_1985_, v___y_1971_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v_ranges_1974_ = v_a_1987_;
goto v___jp_1973_;
}
v___jp_1988_:
{
if (v___y_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v_a_1992_; 
lean_inc(v_declName_1969_);
v___x_1991_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(v_declName_1969_, v___y_1971_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v_ranges_1974_ = v_a_1992_;
goto v___jp_1973_;
}
else
{
goto v___jp_1984_;
}
}
else
{
lean_dec(v_a_1983_);
goto v___jp_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_declName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4(v_declName_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(uint8_t v___x_2006_, lean_object* v_fst_2007_, lean_object* v___x_2008_, lean_object* v___x_2009_, lean_object* v_as_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_a_2018_; uint8_t v_anyUnlocated_2022_; 
v_anyUnlocated_2022_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v_anyUnlocated_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_b_2013_);
return v___x_2023_;
}
else
{
lean_object* v_a_2024_; lean_object* v_fst_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2160_; 
v_a_2024_ = lean_array_uget(v_as_2010_, v_i_2012_);
v_fst_2025_ = lean_ctor_get(v_a_2024_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_a_2024_, 1);
lean_dec(v_unused_2161_);
v___x_2027_ = v_a_2024_;
v_isShared_2028_ = v_isSharedCheck_2160_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_fst_2025_);
lean_dec(v_a_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2160_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; 
lean_inc(v_fst_2025_);
v___x_2029_ = l_Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4(v_fst_2025_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
if (lean_obj_tag(v_a_2030_) == 0)
{
lean_object* v_fst_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2065_; 
v_fst_2031_ = lean_ctor_get(v_b_2013_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_b_2013_, 1);
lean_dec(v_unused_2066_);
v___x_2033_ = v_b_2013_;
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_fst_2031_);
lean_dec(v_b_2013_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_optName_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_optName_2035_ = lean_ctor_get(v_fst_2007_, 1);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0));
v___x_2037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2025_, v___x_2006_);
v___x_2038_ = lean_string_append(v___x_2036_, v___x_2037_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1));
v___x_2040_ = lean_string_append(v___x_2038_, v___x_2039_);
lean_inc(v_optName_2035_);
v___x_2041_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_2035_, v___x_2006_);
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2));
v___x_2044_ = lean_string_append(v___x_2042_, v___x_2043_);
v___x_2045_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_2045_, 1);
lean_del_object(v___x_2027_);
v___x_2046_ = lean_box(v_anyUnlocated_2022_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2046_);
v___x_2048_ = v___x_2033_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_fst_2031_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
v_a_2018_ = v___x_2048_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2064_; 
lean_del_object(v___x_2033_);
lean_dec(v_fst_2031_);
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v_a_2050_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2052_ = v___x_2045_;
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2045_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_ref_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v_ref_2054_ = lean_ctor_get(v___y_2014_, 5);
v___x_2055_ = lean_io_error_to_string(v_a_2050_);
v___x_2056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
v___x_2057_ = l_Lean_MessageData_ofFormat(v___x_2056_);
lean_inc(v_ref_2054_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2057_);
lean_ctor_set(v___x_2027_, 0, v_ref_2054_);
v___x_2059_ = v___x_2027_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_ref_2054_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2059_);
v___x_2061_ = v___x_2052_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2151_; 
v_fst_2067_ = lean_ctor_get(v_b_2013_, 0);
v_snd_2068_ = lean_ctor_get(v_b_2013_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2070_ = v_b_2013_;
v_isShared_2071_ = v_isSharedCheck_2151_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_b_2013_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2151_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2150_; 
v_val_2072_ = lean_ctor_get(v_a_2030_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2030_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2074_ = v_a_2030_;
v_isShared_2075_ = v_isSharedCheck_2150_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v_a_2030_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2150_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5(v_fst_2025_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___y_2079_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
if (lean_obj_tag(v_a_2077_) == 0)
{
lean_inc(v___x_2009_);
v___y_2079_ = v___x_2009_;
goto v___jp_2078_;
}
else
{
lean_object* v_val_2141_; 
v_val_2141_ = lean_ctor_get(v_a_2077_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v_a_2077_, 1);
v___y_2079_ = v_val_2141_;
goto v___jp_2078_;
}
v___jp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3));
lean_inc(v___y_2079_);
lean_inc(v___x_2008_);
v___x_2081_ = l_Lean_SearchPath_findWithExt(v___x_2008_, v___x_2080_, v___y_2079_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v_a_2082_) == 0)
{
lean_object* v_optName_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v_val_2072_);
lean_dec(v_snd_2068_);
v_optName_2083_ = lean_ctor_get(v_fst_2007_, 1);
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4));
v___x_2085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2079_, v___x_2006_);
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5));
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
lean_inc(v_optName_2083_);
v___x_2089_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_2083_, v___x_2006_);
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2));
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
v___x_2093_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_dec_ref_known(v___x_2093_, 1);
lean_del_object(v___x_2074_);
lean_del_object(v___x_2027_);
v___x_2094_ = lean_box(v_anyUnlocated_2022_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2094_);
v___x_2096_ = v___x_2070_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_fst_2067_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v_a_2018_ = v___x_2096_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_2070_);
lean_dec(v_fst_2067_);
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v_a_2098_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2100_ = v___x_2093_;
v_isShared_2101_ = v_isSharedCheck_2114_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2114_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_ref_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_ref_2102_ = lean_ctor_get(v___y_2014_, 5);
v___x_2103_ = lean_io_error_to_string(v_a_2098_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 3);
lean_ctor_set(v___x_2074_, 0, v___x_2103_);
v___x_2105_ = v___x_2074_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = l_Lean_MessageData_ofFormat(v___x_2105_);
lean_inc(v_ref_2102_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2106_);
lean_ctor_set(v___x_2027_, 0, v_ref_2102_);
v___x_2108_ = v___x_2027_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_ref_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2108_);
v___x_2110_ = v___x_2100_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
else
{
lean_object* v_range_2115_; lean_object* v_val_2116_; lean_object* v_pos_2117_; lean_object* v_optName_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v___y_2079_);
lean_del_object(v___x_2074_);
lean_del_object(v___x_2027_);
v_range_2115_ = lean_ctor_get(v_val_2072_, 0);
lean_inc_ref(v_range_2115_);
lean_dec(v_val_2072_);
v_val_2116_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_a_2082_, 1);
v_pos_2117_ = lean_ctor_get(v_range_2115_, 0);
lean_inc_ref(v_pos_2117_);
lean_dec_ref(v_range_2115_);
v_optName_2118_ = lean_ctor_get(v_fst_2007_, 1);
lean_inc(v_optName_2118_);
v___x_2119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2119_, 0, v_val_2116_);
lean_ctor_set(v___x_2119_, 1, v_pos_2117_);
lean_ctor_set(v___x_2119_, 2, v_optName_2118_);
v___x_2120_ = lean_array_push(v_fst_2067_, v___x_2119_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2120_);
v___x_2122_ = v___x_2070_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2068_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
v_a_2018_ = v___x_2122_;
goto v___jp_2017_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v___y_2079_);
lean_dec(v_val_2072_);
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v_a_2124_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2126_ = v___x_2081_;
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2081_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_ref_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v_ref_2128_ = lean_ctor_get(v___y_2014_, 5);
v___x_2129_ = lean_io_error_to_string(v_a_2124_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 3);
lean_ctor_set(v___x_2074_, 0, v___x_2129_);
v___x_2131_ = v___x_2074_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_MessageData_ofFormat(v___x_2131_);
lean_inc(v_ref_2128_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v___x_2132_);
lean_ctor_set(v___x_2027_, 0, v_ref_2128_);
v___x_2134_ = v___x_2027_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_ref_2128_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2134_);
v___x_2136_ = v___x_2126_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2074_);
lean_dec(v_val_2072_);
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_del_object(v___x_2027_);
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v_a_2142_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2076_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2076_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_del_object(v___x_2027_);
lean_dec(v_fst_2025_);
lean_dec_ref(v_b_2013_);
lean_dec(v___x_2009_);
lean_dec(v___x_2008_);
lean_dec_ref(v_fst_2007_);
v_a_2152_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2029_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2029_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
v___jp_2017_:
{
size_t v___x_2019_; size_t v___x_2020_; 
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_2012_, v___x_2019_);
v_i_2012_ = v___x_2020_;
v_b_2013_ = v_a_2018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_2162_, lean_object* v_fst_2163_, lean_object* v___x_2164_, lean_object* v___x_2165_, lean_object* v_as_2166_, lean_object* v_sz_2167_, lean_object* v_i_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_32128__boxed_2173_; size_t v_sz_boxed_2174_; size_t v_i_boxed_2175_; lean_object* v_res_2176_; 
v___x_32128__boxed_2173_ = lean_unbox(v___x_2162_);
v_sz_boxed_2174_ = lean_unbox_usize(v_sz_2167_);
lean_dec(v_sz_2167_);
v_i_boxed_2175_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_32128__boxed_2173_, v_fst_2163_, v___x_2164_, v___x_2165_, v_as_2166_, v_sz_boxed_2174_, v_i_boxed_2175_, v_b_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec_ref(v_as_2166_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(uint8_t v___x_2177_, lean_object* v___x_2178_, lean_object* v___x_2179_, lean_object* v_as_2180_, size_t v_sz_2181_, size_t v_i_2182_, lean_object* v_b_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_lt(v_i_2182_, v_sz_2181_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v___x_2179_);
lean_dec(v___x_2178_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_b_2183_);
return v___x_2188_;
}
else
{
lean_object* v_a_2189_; lean_object* v_fst_2190_; lean_object* v_snd_2191_; lean_object* v_fst_2192_; lean_object* v_snd_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2231_; 
v_a_2189_ = lean_array_uget_borrowed(v_as_2180_, v_i_2182_);
v_fst_2190_ = lean_ctor_get(v_a_2189_, 0);
v_snd_2191_ = lean_ctor_get(v_a_2189_, 1);
v_fst_2192_ = lean_ctor_get(v_b_2183_, 0);
v_snd_2193_ = lean_ctor_get(v_b_2183_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_b_2183_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2195_ = v_b_2183_;
v_isShared_2196_ = v_isSharedCheck_2231_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snd_2193_);
lean_inc(v_fst_2192_);
lean_dec(v_b_2183_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2231_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___y_2198_; lean_object* v_size_2218_; lean_object* v_buckets_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_size_2218_ = lean_ctor_get(v_snd_2191_, 0);
v_buckets_2219_ = lean_ctor_get(v_snd_2191_, 1);
v___x_2220_ = lean_mk_empty_array_with_capacity(v_size_2218_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_array_get_size(v_buckets_2219_);
v___x_2223_ = lean_nat_dec_lt(v___x_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
v___y_2198_ = v___x_2220_;
goto v___jp_2197_;
}
else
{
uint8_t v___x_2224_; 
v___x_2224_ = lean_nat_dec_le(v___x_2222_, v___x_2222_);
if (v___x_2224_ == 0)
{
if (v___x_2223_ == 0)
{
v___y_2198_ = v___x_2220_;
goto v___jp_2197_;
}
else
{
size_t v___x_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = lean_usize_of_nat(v___x_2222_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8(v_buckets_2219_, v___x_2225_, v___x_2226_, v___x_2220_);
v___y_2198_ = v___x_2227_;
goto v___jp_2197_;
}
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2222_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__8(v_buckets_2219_, v___x_2228_, v___x_2229_, v___x_2220_);
v___y_2198_ = v___x_2230_;
goto v___jp_2197_;
}
}
v___jp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2196_ == 0)
{
v___x_2200_ = v___x_2195_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_fst_2192_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_snd_2193_);
v___x_2200_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
size_t v_sz_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v_sz_2201_ = lean_array_size(v___y_2198_);
v___x_2202_ = ((size_t)0ULL);
lean_inc(v___x_2179_);
lean_inc(v___x_2178_);
lean_inc(v_fst_2190_);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_2177_, v_fst_2190_, v___x_2178_, v___x_2179_, v___y_2198_, v_sz_2201_, v___x_2202_, v___x_2200_, v___y_2184_, v___y_2185_);
lean_dec_ref(v___y_2198_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2216_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v_fst_2205_ = lean_ctor_get(v_a_2204_, 0);
v_snd_2206_ = lean_ctor_get(v_a_2204_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2208_ = v_a_2204_;
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_snd_2206_);
lean_inc(v_fst_2205_);
lean_dec(v_a_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_fst_2205_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_snd_2206_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
size_t v___x_2212_; size_t v___x_2213_; 
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_add(v_i_2182_, v___x_2212_);
v_i_2182_ = v___x_2213_;
v_b_2183_ = v___x_2211_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2179_);
lean_dec(v___x_2178_);
return v___x_2203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object* v___x_2232_, lean_object* v___x_2233_, lean_object* v___x_2234_, lean_object* v_as_2235_, lean_object* v_sz_2236_, lean_object* v_i_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v___x_32422__boxed_2242_; size_t v_sz_boxed_2243_; size_t v_i_boxed_2244_; lean_object* v_res_2245_; 
v___x_32422__boxed_2242_ = lean_unbox(v___x_2232_);
v_sz_boxed_2243_ = lean_unbox_usize(v_sz_2236_);
lean_dec(v_sz_2236_);
v_i_boxed_2244_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_res_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___x_32422__boxed_2242_, v___x_2233_, v___x_2234_, v_as_2235_, v_sz_boxed_2243_, v_i_boxed_2244_, v_b_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_as_2235_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(uint8_t v___x_2249_, lean_object* v_fst_2250_, lean_object* v_as_2251_, size_t v_sz_2252_, size_t v_i_2253_, lean_object* v_b_2254_){
_start:
{
lean_object* v_a_2257_; uint8_t v_anyUnlocated_2261_; 
v_anyUnlocated_2261_ = lean_usize_dec_lt(v_i_2253_, v_sz_2252_);
if (v_anyUnlocated_2261_ == 0)
{
lean_object* v___x_2262_; 
lean_dec(v_fst_2250_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_b_2254_);
return v___x_2262_;
}
else
{
lean_object* v_fst_2263_; lean_object* v_snd_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2301_; 
v_fst_2263_ = lean_ctor_get(v_b_2254_, 0);
v_snd_2264_ = lean_ctor_get(v_b_2254_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_b_2254_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2266_ = v_b_2254_;
v_isShared_2267_ = v_isSharedCheck_2301_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snd_2264_);
lean_inc(v_fst_2263_);
lean_dec(v_b_2254_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2301_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_a_2268_; lean_object* v_position_x3f_2269_; 
v_a_2268_ = lean_array_uget_borrowed(v_as_2251_, v_i_2253_);
v_position_x3f_2269_ = lean_ctor_get(v_a_2268_, 2);
if (lean_obj_tag(v_position_x3f_2269_) == 0)
{
lean_object* v_linter_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v_snd_2264_);
v_linter_2270_ = lean_ctor_get(v_a_2268_, 0);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0));
lean_inc(v_linter_2270_);
v___x_2272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2270_, v___x_2249_);
v___x_2273_ = lean_string_append(v___x_2271_, v___x_2272_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1));
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
lean_inc(v_fst_2250_);
v___x_2276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2250_, v___x_2249_);
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2));
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
v___x_2280_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
lean_dec_ref_known(v___x_2280_, 1);
v___x_2281_ = lean_box(v_anyUnlocated_2261_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 1, v___x_2281_);
v___x_2283_ = v___x_2266_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_fst_2263_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
v_a_2257_ = v___x_2283_;
goto v___jp_2256_;
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2266_);
lean_dec(v_fst_2263_);
lean_dec(v_fst_2250_);
v_a_2285_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2280_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2280_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_linter_2293_; lean_object* v_file_2294_; lean_object* v_val_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v_linter_2293_ = lean_ctor_get(v_a_2268_, 0);
v_file_2294_ = lean_ctor_get(v_a_2268_, 3);
v_val_2295_ = lean_ctor_get(v_position_x3f_2269_, 0);
lean_inc(v_linter_2293_);
lean_inc(v_val_2295_);
lean_inc_ref(v_file_2294_);
v___x_2296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2296_, 0, v_file_2294_);
lean_ctor_set(v___x_2296_, 1, v_val_2295_);
lean_ctor_set(v___x_2296_, 2, v_linter_2293_);
v___x_2297_ = lean_array_push(v_fst_2263_, v___x_2296_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2297_);
v___x_2299_ = v___x_2266_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_snd_2264_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
v_a_2257_ = v___x_2299_;
goto v___jp_2256_;
}
}
}
}
v___jp_2256_:
{
size_t v___x_2258_; size_t v___x_2259_; 
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2253_, v___x_2258_);
v_i_2253_ = v___x_2259_;
v_b_2254_ = v_a_2257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object* v___x_2302_, lean_object* v_fst_2303_, lean_object* v_as_2304_, lean_object* v_sz_2305_, lean_object* v_i_2306_, lean_object* v_b_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v___x_32521__boxed_2309_; size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v___x_32521__boxed_2309_ = lean_unbox(v___x_2302_);
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2305_);
lean_dec(v_sz_2305_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_32521__boxed_2309_, v_fst_2303_, v_as_2304_, v_sz_boxed_2310_, v_i_boxed_2311_, v_b_2307_);
lean_dec_ref(v_as_2304_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(uint8_t v___x_2313_, lean_object* v_as_2314_, size_t v_sz_2315_, size_t v_i_2316_, lean_object* v_b_2317_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_lt(v_i_2316_, v_sz_2315_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_b_2317_);
return v___x_2320_;
}
else
{
lean_object* v_a_2321_; lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v_fst_2324_; lean_object* v_snd_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2348_; 
v_a_2321_ = lean_array_uget_borrowed(v_as_2314_, v_i_2316_);
v_fst_2322_ = lean_ctor_get(v_a_2321_, 0);
v_snd_2323_ = lean_ctor_get(v_a_2321_, 1);
v_fst_2324_ = lean_ctor_get(v_b_2317_, 0);
v_snd_2325_ = lean_ctor_get(v_b_2317_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_b_2317_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2327_ = v_b_2317_;
v_isShared_2328_ = v_isSharedCheck_2348_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_snd_2325_);
lean_inc(v_fst_2324_);
lean_dec(v_b_2317_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2348_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_fst_2324_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_snd_2325_);
v___x_2330_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
size_t v_sz_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v_sz_2331_ = lean_array_size(v_snd_2323_);
v___x_2332_ = ((size_t)0ULL);
lean_inc(v_fst_2322_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_2313_, v_fst_2322_, v_snd_2323_, v_sz_2331_, v___x_2332_, v___x_2330_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2346_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_fst_2335_ = lean_ctor_get(v_a_2334_, 0);
v_snd_2336_ = lean_ctor_get(v_a_2334_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_a_2334_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2338_ = v_a_2334_;
v_isShared_2339_ = v_isSharedCheck_2346_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snd_2336_);
lean_inc(v_fst_2335_);
lean_dec(v_a_2334_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2346_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_fst_2335_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_snd_2336_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
size_t v___x_2342_; size_t v___x_2343_; 
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_add(v_i_2316_, v___x_2342_);
v_i_2316_ = v___x_2343_;
v_b_2317_ = v___x_2341_;
goto _start;
}
}
}
else
{
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___boxed(lean_object* v___x_2349_, lean_object* v_as_2350_, lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_32610__boxed_2355_; size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v___x_32610__boxed_2355_ = lean_unbox(v___x_2349_);
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___x_32610__boxed_2355_, v_as_2350_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2353_);
lean_dec_ref(v_as_2350_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_2359_, lean_object* v_as_2360_, size_t v_i_2361_, size_t v_stop_2362_, lean_object* v_b_2363_){
_start:
{
lean_object* v___y_2365_; uint8_t v___x_2369_; 
v___x_2369_ = lean_usize_dec_eq(v_i_2361_, v_stop_2362_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; lean_object* v_linter_2371_; uint8_t v___x_2372_; 
v___x_2370_ = lean_array_uget_borrowed(v_as_2360_, v_i_2361_);
v_linter_2371_ = lean_ctor_get(v___x_2370_, 0);
v___x_2372_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2371_, v___x_2359_);
if (v___x_2372_ == 0)
{
v___y_2365_ = v_b_2363_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2373_; 
lean_inc(v___x_2370_);
v___x_2373_ = lean_array_push(v_b_2363_, v___x_2370_);
v___y_2365_ = v___x_2373_;
goto v___jp_2364_;
}
}
else
{
return v_b_2363_;
}
v___jp_2364_:
{
size_t v___x_2366_; size_t v___x_2367_; 
v___x_2366_ = ((size_t)1ULL);
v___x_2367_ = lean_usize_add(v_i_2361_, v___x_2366_);
v_i_2361_ = v___x_2367_;
v_b_2363_ = v___y_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_2374_, lean_object* v_as_2375_, lean_object* v_i_2376_, lean_object* v_stop_2377_, lean_object* v_b_2378_){
_start:
{
size_t v_i_boxed_2379_; size_t v_stop_boxed_2380_; lean_object* v_res_2381_; 
v_i_boxed_2379_ = lean_unbox_usize(v_i_2376_);
lean_dec(v_i_2376_);
v_stop_boxed_2380_ = lean_unbox_usize(v_stop_2377_);
lean_dec(v_stop_2377_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2374_, v_as_2375_, v_i_boxed_2379_, v_stop_boxed_2380_, v_b_2378_);
lean_dec_ref(v_as_2375_);
lean_dec_ref(v___x_2374_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18(lean_object* v___x_2384_, lean_object* v_as_2385_, size_t v_i_2386_, size_t v_stop_2387_, lean_object* v_b_2388_){
_start:
{
lean_object* v___y_2390_; uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_eq(v_i_2386_, v_stop_2387_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2420_; 
v___x_2395_ = lean_array_uget(v_as_2385_, v_i_2386_);
v_fst_2396_ = lean_ctor_get(v___x_2395_, 0);
v_snd_2397_ = lean_ctor_get(v___x_2395_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2399_ = v___x_2395_;
v_isShared_2400_ = v_isSharedCheck_2420_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v___x_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2420_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___y_2403_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2410_ = lean_array_get_size(v_snd_2397_);
v___x_2411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___closed__0));
v___x_2412_ = lean_nat_dec_lt(v___x_2401_, v___x_2410_);
if (v___x_2412_ == 0)
{
lean_dec(v_snd_2397_);
v___y_2403_ = v___x_2411_;
goto v___jp_2402_;
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = lean_nat_dec_le(v___x_2410_, v___x_2410_);
if (v___x_2413_ == 0)
{
if (v___x_2412_ == 0)
{
lean_dec(v_snd_2397_);
v___y_2403_ = v___x_2411_;
goto v___jp_2402_;
}
else
{
size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((size_t)0ULL);
v___x_2415_ = lean_usize_of_nat(v___x_2410_);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2384_, v_snd_2397_, v___x_2414_, v___x_2415_, v___x_2411_);
lean_dec(v_snd_2397_);
v___y_2403_ = v___x_2416_;
goto v___jp_2402_;
}
}
else
{
size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = ((size_t)0ULL);
v___x_2418_ = lean_usize_of_nat(v___x_2410_);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2384_, v_snd_2397_, v___x_2417_, v___x_2418_, v___x_2411_);
lean_dec(v_snd_2397_);
v___y_2403_ = v___x_2419_;
goto v___jp_2402_;
}
}
v___jp_2402_:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = lean_array_get_size(v___y_2403_);
v___x_2405_ = lean_nat_dec_eq(v___x_2404_, v___x_2401_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2407_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v___y_2403_);
v___x_2407_ = v___x_2399_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_fst_2396_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___y_2403_);
v___x_2407_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_array_push(v_b_2388_, v___x_2407_);
v___y_2390_ = v___x_2408_;
goto v___jp_2389_;
}
}
else
{
lean_dec_ref(v___y_2403_);
lean_del_object(v___x_2399_);
lean_dec(v_fst_2396_);
v___y_2390_ = v_b_2388_;
goto v___jp_2389_;
}
}
}
}
else
{
return v_b_2388_;
}
v___jp_2389_:
{
size_t v___x_2391_; size_t v___x_2392_; 
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2386_, v___x_2391_);
v_i_2386_ = v___x_2392_;
v_b_2388_ = v___y_2390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18___boxed(lean_object* v___x_2421_, lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_, lean_object* v_b_2425_){
_start:
{
size_t v_i_boxed_2426_; size_t v_stop_boxed_2427_; lean_object* v_res_2428_; 
v_i_boxed_2426_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2427_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18(v___x_2421_, v_as_2422_, v_i_boxed_2426_, v_stop_boxed_2427_, v_b_2425_);
lean_dec_ref(v_as_2422_);
lean_dec_ref(v___x_2421_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15(lean_object* v___x_2429_, lean_object* v_as_2430_, lean_object* v_start_2431_, lean_object* v_stop_2432_){
_start:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2434_ = lean_nat_dec_lt(v_start_2431_, v_stop_2432_);
if (v___x_2434_ == 0)
{
return v___x_2433_;
}
else
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = lean_array_get_size(v_as_2430_);
v___x_2436_ = lean_nat_dec_le(v_stop_2432_, v___x_2435_);
if (v___x_2436_ == 0)
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_nat_dec_lt(v_start_2431_, v___x_2435_);
if (v___x_2437_ == 0)
{
return v___x_2433_;
}
else
{
size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_usize_of_nat(v_start_2431_);
v___x_2439_ = lean_usize_of_nat(v___x_2435_);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18(v___x_2429_, v_as_2430_, v___x_2438_, v___x_2439_, v___x_2433_);
return v___x_2440_;
}
}
else
{
size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_usize_of_nat(v_start_2431_);
v___x_2442_ = lean_usize_of_nat(v_stop_2432_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15_spec__18(v___x_2429_, v_as_2430_, v___x_2441_, v___x_2442_, v___x_2433_);
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15___boxed(lean_object* v___x_2444_, lean_object* v_as_2445_, lean_object* v_start_2446_, lean_object* v_stop_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15(v___x_2444_, v_as_2445_, v_start_2446_, v_stop_2447_);
lean_dec(v_stop_2447_);
lean_dec(v_start_2446_);
lean_dec_ref(v_as_2445_);
lean_dec_ref(v___x_2444_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10(lean_object* v___x_2449_, lean_object* v_as_2450_, size_t v_i_2451_, size_t v_stop_2452_){
_start:
{
uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_eq(v_i_2451_, v_stop_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v_snd_2455_; lean_object* v_size_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; uint8_t v___x_2459_; 
v___x_2454_ = lean_array_uget_borrowed(v_as_2450_, v_i_2451_);
v_snd_2455_ = lean_ctor_get(v___x_2454_, 1);
v_size_2456_ = lean_ctor_get(v_snd_2455_, 0);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = 1;
v___x_2459_ = lean_nat_dec_eq(v_size_2456_, v___x_2457_);
if (v___x_2459_ == 0)
{
return v___x_2458_;
}
else
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_nat_dec_eq(v___x_2449_, v___x_2457_);
if (v___x_2460_ == 0)
{
size_t v___x_2461_; size_t v___x_2462_; 
v___x_2461_ = ((size_t)1ULL);
v___x_2462_ = lean_usize_add(v_i_2451_, v___x_2461_);
v_i_2451_ = v___x_2462_;
goto _start;
}
else
{
return v___x_2458_;
}
}
}
else
{
uint8_t v___x_2464_; 
v___x_2464_ = 0;
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object* v___x_2465_, lean_object* v_as_2466_, lean_object* v_i_2467_, lean_object* v_stop_2468_){
_start:
{
size_t v_i_boxed_2469_; size_t v_stop_boxed_2470_; uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_i_boxed_2469_ = lean_unbox_usize(v_i_2467_);
lean_dec(v_i_2467_);
v_stop_boxed_2470_ = lean_unbox_usize(v_stop_2468_);
lean_dec(v_stop_2468_);
v_res_2471_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10(v___x_2465_, v_as_2466_, v_i_boxed_2469_, v_stop_boxed_2470_);
lean_dec_ref(v_as_2466_);
lean_dec(v___x_2465_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(uint8_t v___y_2473_, lean_object* v___x_2474_, lean_object* v_____r_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_box(v___y_2473_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2474_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1___boxed(lean_object* v___y_2482_, lean_object* v___x_2483_, lean_object* v_____r_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v___y_32810__boxed_2488_; lean_object* v_res_2489_; 
v___y_32810__boxed_2488_ = lean_unbox(v___y_2482_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(v___y_32810__boxed_2488_, v___x_2483_, v_____r_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2489_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_unsigned_to_nat(32u);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13(void){
_start:
{
size_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2509_ = ((size_t)5ULL);
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_unsigned_to_nat(32u);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
v___x_2513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__12);
v___x_2514_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2512_);
lean_ctor_set(v___x_2514_, 2, v___x_2510_);
lean_ctor_set(v___x_2514_, 3, v___x_2510_);
lean_ctor_set_usize(v___x_2514_, 4, v___x_2509_);
return v___x_2514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14(void){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2515_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__14);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = l_Lean_NameSet_empty;
v___x_2521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
lean_ctor_set(v___x_2522_, 2, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = l_Lean_firstFrontendMacroScope;
v___x_2525_ = lean_nat_add(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22(void){
_start:
{
lean_object* v___x_2532_; uint64_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13);
v___x_2533_ = 0ULL;
v___x_2534_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set_uint64(v___x_2534_, sizeof(void*)*1, v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v_anyUnlocated_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__13);
v___x_2536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__15);
v_anyUnlocated_2537_ = 1;
v___x_2538_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2536_);
lean_ctor_set(v___x_2538_, 2, v___x_2535_);
lean_ctor_set_uint8(v___x_2538_, sizeof(void*)*3, v_anyUnlocated_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17(lean_object* v___x_2539_, lean_object* v_args_2540_, lean_object* v___x_2541_, lean_object* v_as_2542_, size_t v_sz_2543_, size_t v_i_2544_, lean_object* v_b_2545_){
_start:
{
lean_object* v_a_2548_; lean_object* v_a_2553_; lean_object* v_msg_2557_; lean_object* v___x_2561_; uint8_t v_anyFailed_2562_; uint8_t v_anyUnlocated_2563_; lean_object* v_a_2565_; uint8_t v___y_2579_; lean_object* v___y_2580_; lean_object* v___x_2585_; lean_object* v_envLinterModule_2586_; uint8_t v___x_2587_; 
v___x_2561_ = lean_unsigned_to_nat(0u);
v_anyFailed_2562_ = lean_nat_dec_eq(v___x_2539_, v___x_2561_);
v_anyUnlocated_2563_ = 1;
v___x_2585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__6));
v_envLinterModule_2586_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_2586_, 0, v___x_2585_);
lean_ctor_set_uint8(v_envLinterModule_2586_, sizeof(void*)*1, v_anyFailed_2562_);
lean_ctor_set_uint8(v_envLinterModule_2586_, sizeof(void*)*1 + 1, v_anyUnlocated_2563_);
lean_ctor_set_uint8(v_envLinterModule_2586_, sizeof(void*)*1 + 2, v_anyFailed_2562_);
v___x_2587_ = lean_usize_dec_lt(v_i_2544_, v_sz_2543_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref_known(v_envLinterModule_2586_, 1);
lean_dec(v___x_2541_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_b_2545_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
lean_dec_ref_known(v___x_2589_, 1);
v_a_2590_ = lean_array_uget_borrowed(v_as_2542_, v_i_2544_);
lean_inc(v_a_2590_);
v___x_2591_ = l_Lean_findOLean(v_a_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_readModuleData(v_a_2592_);
lean_dec(v_a_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_3007_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v_fst_2595_ = lean_ctor_get(v_a_2594_, 0);
v_snd_2596_ = lean_ctor_get(v_a_2594_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2598_ = v_a_2594_;
v_isShared_2599_ = v_isSharedCheck_3007_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snd_2596_);
lean_inc(v_fst_2595_);
lean_dec(v_a_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_3007_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
uint8_t v___x_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_3006_; 
v___x_2600_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_2595_);
lean_dec(v_fst_2595_);
v_fst_2601_ = lean_ctor_get(v_b_2545_, 0);
v_snd_2602_ = lean_ctor_get(v_b_2545_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_b_2545_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2604_ = v_b_2545_;
v_isShared_2605_ = v_isSharedCheck_3006_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_b_2545_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_3006_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
uint8_t v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; uint8_t v_anyUnlocated_2610_; uint8_t v___y_2619_; uint8_t v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v_a_2623_; uint8_t v___y_2634_; uint8_t v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_3005_; 
v_fst_2641_ = lean_ctor_get(v_snd_2602_, 0);
v_snd_2642_ = lean_ctor_get(v_snd_2602_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_snd_2602_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2644_ = v_snd_2602_;
v_isShared_2645_ = v_isSharedCheck_3005_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_snd_2642_);
lean_inc(v_fst_2641_);
lean_dec(v_snd_2602_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_3005_;
goto v_resetjp_2643_;
}
v___jp_2606_:
{
if (v___y_2608_ == 0)
{
if (v___y_2607_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(v_anyUnlocated_2610_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2611_);
lean_ctor_set(v___x_2604_, 0, v___y_2609_);
v___x_2613_ = v___x_2604_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___y_2609_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2613_);
lean_ctor_set(v___x_2598_, 0, v_fst_2601_);
v___x_2615_ = v___x_2598_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2601_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
v_a_2548_ = v___x_2615_;
goto v___jp_2547_;
}
}
}
else
{
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
v___y_2579_ = v_anyUnlocated_2610_;
v___y_2580_ = v___y_2609_;
goto v___jp_2578_;
}
}
else
{
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
v___y_2579_ = v_anyUnlocated_2610_;
v___y_2580_ = v___y_2609_;
goto v___jp_2578_;
}
}
v___jp_2618_:
{
lean_object* v___x_2624_; lean_object* v_snd_2625_; lean_object* v_fst_2626_; lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2624_ = lean_st_ref_get(v___y_2622_);
lean_dec(v___y_2622_);
lean_dec(v___x_2624_);
v_snd_2625_ = lean_ctor_get(v_a_2623_, 1);
lean_inc(v_snd_2625_);
v_fst_2626_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_fst_2626_);
lean_dec_ref(v_a_2623_);
v_fst_2627_ = lean_ctor_get(v_snd_2625_, 0);
lean_inc(v_fst_2627_);
v_snd_2628_ = lean_ctor_get(v_snd_2625_, 1);
lean_inc(v_snd_2628_);
lean_dec(v_snd_2625_);
v___x_2629_ = l_Array_append___redArg(v___y_2621_, v_fst_2627_);
lean_dec(v_fst_2627_);
v___x_2630_ = lean_unbox(v_snd_2628_);
lean_dec(v_snd_2628_);
if (v___x_2630_ == 0)
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_unbox(v_fst_2626_);
lean_dec(v_fst_2626_);
v___y_2607_ = v___x_2631_;
v___y_2608_ = v___y_2619_;
v___y_2609_ = v___x_2629_;
v_anyUnlocated_2610_ = v___y_2620_;
goto v___jp_2606_;
}
else
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_unbox(v_fst_2626_);
lean_dec(v_fst_2626_);
v___y_2607_ = v___x_2632_;
v___y_2608_ = v___y_2619_;
v___y_2609_ = v___x_2629_;
v_anyUnlocated_2610_ = v_anyUnlocated_2563_;
goto v___jp_2606_;
}
}
v___jp_2633_:
{
if (lean_obj_tag(v___y_2638_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___y_2638_, 1);
v___y_2619_ = v___y_2634_;
v___y_2620_ = v___y_2635_;
v___y_2621_ = v___y_2636_;
v___y_2622_ = v___y_2637_;
v_a_2623_ = v_a_2639_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2640_; 
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2640_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___y_2638_, 1);
v_a_2565_ = v_a_2640_;
goto v___jp_2564_;
}
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__7));
v___x_2647_ = lean_box(v_anyFailed_2562_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2647_);
lean_ctor_set(v___x_2644_, 0, v___x_2646_);
v___x_2649_ = v___x_2644_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
uint8_t v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; uint8_t v___y_2659_; lean_object* v___y_2660_; uint8_t v___y_2661_; uint8_t v___y_2723_; uint8_t v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; uint8_t v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; uint8_t v___y_2766_; uint8_t v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; uint8_t v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; uint8_t v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; lean_object* v___y_2818_; uint8_t v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; uint8_t v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; uint8_t v___y_2826_; uint8_t v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; uint8_t v___y_2851_; uint8_t v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v_records_2855_; uint8_t v_anyUnlocated_2856_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; uint8_t v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2935_; uint8_t v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2960_; 
if (v___x_2600_ == 0)
{
uint8_t v___x_3000_; 
v___x_3000_ = 2;
v___y_2960_ = v___x_3000_;
goto v___jp_2959_;
}
else
{
uint8_t v_recordExceptions_3001_; 
v_recordExceptions_3001_ = lean_ctor_get_uint8(v_args_2540_, sizeof(void*)*3 + 1);
if (v_recordExceptions_3001_ == 0)
{
uint8_t v___x_3002_; 
v___x_3002_ = 0;
v___y_2960_ = v___x_3002_;
goto v___jp_2959_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = 1;
v___y_2960_ = v___x_3003_;
goto v___jp_2959_;
}
}
v___jp_2650_:
{
if (v___y_2659_ == 0)
{
if (v___y_2661_ == 0)
{
lean_dec_ref(v___y_2658_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
if (v___y_2651_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__8));
lean_inc(v_a_2590_);
v___x_2663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_2590_, v_anyUnlocated_2563_);
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__9));
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
v___x_2667_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(v___y_2661_, v___x_2649_, v_a_2668_, v___y_2657_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2657_);
v___y_2634_ = v___y_2651_;
v___y_2635_ = v___y_2652_;
v___y_2636_ = v___y_2655_;
v___y_2637_ = v___y_2660_;
v___y_2638_ = v___x_2669_;
goto v___jp_2633_;
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2670_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v___x_2667_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2667_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_io_error_to_string(v_a_2670_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 3);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_MessageData_ofFormat(v___x_2676_);
v_msg_2557_ = v___x_2677_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_box(0);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(v___y_2661_, v___x_2649_, v___x_2680_, v___y_2657_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2657_);
v___y_2634_ = v___y_2651_;
v___y_2635_ = v___y_2652_;
v___y_2636_ = v___y_2655_;
v___y_2637_ = v___y_2660_;
v___y_2638_ = v___x_2681_;
goto v___jp_2633_;
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__10));
lean_inc(v_a_2590_);
v___x_2683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_2590_, v___y_2661_);
v___x_2684_ = lean_string_append(v___x_2682_, v___x_2683_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = 1;
v___x_2686_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_2658_, v___y_2654_, v_anyUnlocated_2563_, v___x_2684_, v___x_2685_, v___y_2653_, v_anyUnlocated_2563_, v___y_2657_, v___y_2656_);
lean_dec_ref(v___y_2654_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = l_Lean_MessageData_toString(v_a_2687_);
v___x_2689_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__1(v___y_2661_, v___x_2649_, v_a_2690_, v___y_2657_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2657_);
v___y_2634_ = v___y_2651_;
v___y_2635_ = v___y_2652_;
v___y_2636_ = v___y_2655_;
v___y_2637_ = v___y_2660_;
v___y_2638_ = v___x_2691_;
goto v___jp_2633_;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2692_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2694_ = v___x_2689_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2689_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_io_error_to_string(v_a_2692_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 3);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_MessageData_ofFormat(v___x_2698_);
v_msg_2557_ = v___x_2699_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v_a_2702_; 
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2702_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2686_, 1);
v_a_2565_ = v_a_2702_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v___x_2703_; lean_object* v_env_2704_; lean_object* v___x_2705_; size_t v_sz_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
v___x_2703_ = lean_st_ref_get(v___y_2656_);
v_env_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2704_);
lean_dec(v___x_2703_);
v___x_2705_ = l_Lean_Environment_mainModule(v_env_2704_);
lean_dec_ref(v_env_2704_);
v_sz_2706_ = lean_array_size(v___y_2658_);
v___x_2707_ = ((size_t)0ULL);
lean_inc(v___x_2541_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___y_2659_, v___x_2541_, v___x_2705_, v___y_2658_, v_sz_2706_, v___x_2707_, v___x_2649_, v___y_2657_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v___y_2658_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2720_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v_fst_2710_ = lean_ctor_get(v_a_2709_, 0);
v_snd_2711_ = lean_ctor_get(v_a_2709_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_a_2709_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2713_ = v_a_2709_;
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_snd_2711_);
lean_inc(v_fst_2710_);
lean_dec(v_a_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_fst_2710_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_snd_2711_);
v___x_2716_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_box(v___y_2661_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2716_);
v___y_2619_ = v___y_2651_;
v___y_2620_ = v___y_2652_;
v___y_2621_ = v___y_2655_;
v___y_2622_ = v___y_2660_;
v_a_2623_ = v___x_2718_;
goto v___jp_2618_;
}
}
}
else
{
lean_object* v_a_2721_; 
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2655_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2721_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2708_, 1);
v_a_2565_ = v_a_2721_;
goto v___jp_2564_;
}
}
}
v___jp_2722_:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_2731_, v___y_2728_, v___y_2727_);
lean_dec(v___y_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_array_get_size(v_a_2733_);
v___x_2735_ = lean_nat_dec_eq(v___x_2734_, v___x_2561_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Linter_EnvLinter_lintCore(v___y_2726_, v_a_2733_, v___y_2728_, v___y_2727_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_array_get_size(v_a_2737_);
v___x_2739_ = lean_nat_dec_lt(v___x_2561_, v___x_2738_);
if (v___x_2739_ == 0)
{
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___x_2734_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2725_;
v___y_2656_ = v___y_2727_;
v___y_2657_ = v___y_2728_;
v___y_2658_ = v_a_2737_;
v___y_2659_ = v___y_2729_;
v___y_2660_ = v___y_2730_;
v___y_2661_ = v___x_2735_;
goto v___jp_2650_;
}
else
{
if (v___x_2739_ == 0)
{
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___x_2734_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2725_;
v___y_2656_ = v___y_2727_;
v___y_2657_ = v___y_2728_;
v___y_2658_ = v_a_2737_;
v___y_2659_ = v___y_2729_;
v___y_2660_ = v___y_2730_;
v___y_2661_ = v___x_2735_;
goto v___jp_2650_;
}
else
{
size_t v___x_2740_; size_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = lean_usize_of_nat(v___x_2738_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__10(v___x_2734_, v_a_2737_, v___x_2740_, v___x_2741_);
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___x_2734_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2725_;
v___y_2656_ = v___y_2727_;
v___y_2657_ = v___y_2728_;
v___y_2658_ = v_a_2737_;
v___y_2659_ = v___y_2729_;
v___y_2660_ = v___y_2730_;
v___y_2661_ = v___x_2742_;
goto v___jp_2650_;
}
}
}
else
{
lean_object* v_a_2743_; 
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2743_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2736_, 1);
v_a_2565_ = v_a_2743_;
goto v___jp_2564_;
}
}
else
{
lean_dec(v_a_2733_);
lean_dec_ref(v___y_2726_);
if (v___y_2729_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__11));
lean_inc(v_a_2590_);
v___x_2745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_2590_, v___x_2735_);
v___x_2746_ = lean_string_append(v___x_2744_, v___x_2745_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__9));
v___x_2748_ = lean_string_append(v___x_2746_, v___x_2747_);
v___x_2749_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0(v_anyFailed_2562_, v___x_2649_, v_a_2750_, v___y_2728_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2728_);
v___y_2634_ = v___y_2723_;
v___y_2635_ = v___y_2724_;
v___y_2636_ = v___y_2725_;
v___y_2637_ = v___y_2730_;
v___y_2638_ = v___x_2751_;
goto v___jp_2633_;
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2752_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2754_ = v___x_2749_;
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2749_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_io_error_to_string(v_a_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 3);
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_MessageData_ofFormat(v___x_2758_);
v_msg_2557_ = v___x_2759_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___lam__0(v_anyFailed_2562_, v___x_2649_, v___x_2762_, v___y_2728_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2728_);
v___y_2634_ = v___y_2723_;
v___y_2635_ = v___y_2724_;
v___y_2636_ = v___y_2725_;
v___y_2637_ = v___y_2730_;
v___y_2638_ = v___x_2763_;
goto v___jp_2633_;
}
}
}
else
{
lean_object* v_a_2764_; 
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2764_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2732_, 1);
v_a_2565_ = v_a_2764_;
goto v___jp_2564_;
}
}
v___jp_2765_:
{
lean_object* v_fileName_2778_; lean_object* v_fileMap_2779_; lean_object* v_currRecDepth_2780_; lean_object* v_ref_2781_; lean_object* v_currNamespace_2782_; lean_object* v_openDecls_2783_; lean_object* v_initHeartbeats_2784_; lean_object* v_maxHeartbeats_2785_; lean_object* v_quotContext_2786_; lean_object* v_currMacroScope_2787_; lean_object* v_cancelTk_x3f_2788_; uint8_t v_suppressElabErrors_2789_; lean_object* v_inheritedTraceOptions_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2810_; 
v_fileName_2778_ = lean_ctor_get(v___y_2776_, 0);
v_fileMap_2779_ = lean_ctor_get(v___y_2776_, 1);
v_currRecDepth_2780_ = lean_ctor_get(v___y_2776_, 3);
v_ref_2781_ = lean_ctor_get(v___y_2776_, 5);
v_currNamespace_2782_ = lean_ctor_get(v___y_2776_, 6);
v_openDecls_2783_ = lean_ctor_get(v___y_2776_, 7);
v_initHeartbeats_2784_ = lean_ctor_get(v___y_2776_, 8);
v_maxHeartbeats_2785_ = lean_ctor_get(v___y_2776_, 9);
v_quotContext_2786_ = lean_ctor_get(v___y_2776_, 10);
v_currMacroScope_2787_ = lean_ctor_get(v___y_2776_, 11);
v_cancelTk_x3f_2788_ = lean_ctor_get(v___y_2776_, 12);
v_suppressElabErrors_2789_ = lean_ctor_get_uint8(v___y_2776_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2790_ = lean_ctor_get(v___y_2776_, 13);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___y_2776_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; lean_object* v_unused_2812_; 
v_unused_2811_ = lean_ctor_get(v___y_2776_, 4);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v___y_2776_, 2);
lean_dec(v_unused_2812_);
v___x_2792_ = v___y_2776_;
v_isShared_2793_ = v_isSharedCheck_2810_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_inheritedTraceOptions_2790_);
lean_inc(v_cancelTk_x3f_2788_);
lean_inc(v_currMacroScope_2787_);
lean_inc(v_quotContext_2786_);
lean_inc(v_maxHeartbeats_2785_);
lean_inc(v_initHeartbeats_2784_);
lean_inc(v_openDecls_2783_);
lean_inc(v_currNamespace_2782_);
lean_inc(v_ref_2781_);
lean_inc(v_currRecDepth_2780_);
lean_inc(v_fileMap_2779_);
lean_inc(v_fileName_2778_);
lean_dec(v___y_2776_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2810_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_2775_, v___y_2777_);
lean_dec(v___y_2775_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2808_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2808_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2808_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2799_ = l_Lean_maxRecDepth;
v___x_2800_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__3(v___y_2768_, v___x_2799_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 4, v___x_2800_);
lean_ctor_set(v___x_2792_, 2, v___y_2768_);
v___x_2802_ = v___x_2792_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_fileName_2778_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_fileMap_2779_);
lean_ctor_set(v_reuseFailAlloc_2807_, 2, v___y_2768_);
lean_ctor_set(v_reuseFailAlloc_2807_, 3, v_currRecDepth_2780_);
lean_ctor_set(v_reuseFailAlloc_2807_, 4, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2807_, 5, v_ref_2781_);
lean_ctor_set(v_reuseFailAlloc_2807_, 6, v_currNamespace_2782_);
lean_ctor_set(v_reuseFailAlloc_2807_, 7, v_openDecls_2783_);
lean_ctor_set(v_reuseFailAlloc_2807_, 8, v_initHeartbeats_2784_);
lean_ctor_set(v_reuseFailAlloc_2807_, 9, v_maxHeartbeats_2785_);
lean_ctor_set(v_reuseFailAlloc_2807_, 10, v_quotContext_2786_);
lean_ctor_set(v_reuseFailAlloc_2807_, 11, v_currMacroScope_2787_);
lean_ctor_set(v_reuseFailAlloc_2807_, 12, v_cancelTk_x3f_2788_);
lean_ctor_set(v_reuseFailAlloc_2807_, 13, v_inheritedTraceOptions_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2807_, sizeof(void*)*14 + 1, v_suppressElabErrors_2789_);
v___x_2802_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*14, v___y_2767_);
if (v___y_2772_ == 0)
{
lean_object* v___x_2803_; 
lean_del_object(v___x_2797_);
lean_dec_ref(v___y_2770_);
v___x_2803_ = lean_box(0);
v___y_2723_ = v___y_2766_;
v___y_2724_ = v___y_2769_;
v___y_2725_ = v___y_2771_;
v___y_2726_ = v_a_2795_;
v___y_2727_ = v___y_2777_;
v___y_2728_ = v___x_2802_;
v___y_2729_ = v___y_2773_;
v___y_2730_ = v___y_2774_;
v___y_2731_ = v___x_2803_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2805_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 1);
lean_ctor_set(v___x_2797_, 0, v___y_2770_);
v___x_2805_ = v___x_2797_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___y_2770_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
v___y_2723_ = v___y_2766_;
v___y_2724_ = v___y_2769_;
v___y_2725_ = v___y_2771_;
v___y_2726_ = v_a_2795_;
v___y_2727_ = v___y_2777_;
v___y_2728_ = v___x_2802_;
v___y_2729_ = v___y_2773_;
v___y_2730_ = v___y_2774_;
v___y_2731_ = v___x_2805_;
goto v___jp_2722_;
}
}
}
}
}
else
{
lean_object* v_a_2809_; 
lean_del_object(v___x_2792_);
lean_dec_ref(v_inheritedTraceOptions_2790_);
lean_dec(v_cancelTk_x3f_2788_);
lean_dec(v_currMacroScope_2787_);
lean_dec(v_quotContext_2786_);
lean_dec(v_maxHeartbeats_2785_);
lean_dec(v_initHeartbeats_2784_);
lean_dec(v_openDecls_2783_);
lean_dec(v_currNamespace_2782_);
lean_dec(v_ref_2781_);
lean_dec(v_currRecDepth_2780_);
lean_dec_ref(v_fileMap_2779_);
lean_dec_ref(v_fileName_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec_ref(v___y_2768_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2809_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2794_, 1);
v_a_2565_ = v_a_2809_;
goto v___jp_2564_;
}
}
}
v___jp_2813_:
{
if (v___y_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v_env_2828_; lean_object* v_nextMacroScope_2829_; lean_object* v_ngen_2830_; lean_object* v_auxDeclNGen_2831_; lean_object* v_traceState_2832_; lean_object* v_messages_2833_; lean_object* v_infoState_2834_; lean_object* v_snapshotTasks_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2844_; 
v___x_2827_ = lean_st_ref_take(v___y_2824_);
v_env_2828_ = lean_ctor_get(v___x_2827_, 0);
v_nextMacroScope_2829_ = lean_ctor_get(v___x_2827_, 1);
v_ngen_2830_ = lean_ctor_get(v___x_2827_, 2);
v_auxDeclNGen_2831_ = lean_ctor_get(v___x_2827_, 3);
v_traceState_2832_ = lean_ctor_get(v___x_2827_, 4);
v_messages_2833_ = lean_ctor_get(v___x_2827_, 6);
v_infoState_2834_ = lean_ctor_get(v___x_2827_, 7);
v_snapshotTasks_2835_ = lean_ctor_get(v___x_2827_, 8);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2827_, 5);
lean_dec(v_unused_2845_);
v___x_2837_ = v___x_2827_;
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snapshotTasks_2835_);
lean_inc(v_infoState_2834_);
lean_inc(v_messages_2833_);
lean_inc(v_traceState_2832_);
lean_inc(v_auxDeclNGen_2831_);
lean_inc(v_ngen_2830_);
lean_inc(v_nextMacroScope_2829_);
lean_inc(v_env_2828_);
lean_dec(v___x_2827_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = l_Lean_Kernel_enableDiag(v_env_2828_, v___y_2814_);
lean_inc_ref(v___y_2816_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 5, v___y_2816_);
lean_ctor_set(v___x_2837_, 0, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_nextMacroScope_2829_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_ngen_2830_);
lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_auxDeclNGen_2831_);
lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_traceState_2832_);
lean_ctor_set(v_reuseFailAlloc_2843_, 5, v___y_2816_);
lean_ctor_set(v_reuseFailAlloc_2843_, 6, v_messages_2833_);
lean_ctor_set(v_reuseFailAlloc_2843_, 7, v_infoState_2834_);
lean_ctor_set(v_reuseFailAlloc_2843_, 8, v_snapshotTasks_2835_);
v___x_2841_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_st_ref_set(v___y_2824_, v___x_2841_);
lean_inc(v___y_2824_);
v___y_2766_ = v___y_2815_;
v___y_2767_ = v___y_2814_;
v___y_2768_ = v___y_2821_;
v___y_2769_ = v___y_2817_;
v___y_2770_ = v___y_2822_;
v___y_2771_ = v___y_2818_;
v___y_2772_ = v___y_2819_;
v___y_2773_ = v___y_2823_;
v___y_2774_ = v___y_2824_;
v___y_2775_ = v___y_2820_;
v___y_2776_ = v___y_2825_;
v___y_2777_ = v___y_2824_;
goto v___jp_2765_;
}
}
}
else
{
lean_inc(v___y_2824_);
v___y_2766_ = v___y_2815_;
v___y_2767_ = v___y_2814_;
v___y_2768_ = v___y_2821_;
v___y_2769_ = v___y_2817_;
v___y_2770_ = v___y_2822_;
v___y_2771_ = v___y_2818_;
v___y_2772_ = v___y_2819_;
v___y_2773_ = v___y_2823_;
v___y_2774_ = v___y_2824_;
v___y_2775_ = v___y_2820_;
v___y_2776_ = v___y_2825_;
v___y_2777_ = v___y_2824_;
goto v___jp_2765_;
}
}
v___jp_2846_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v_env_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; uint8_t v___x_2883_; 
v___x_2857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__16);
v___x_2858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__17);
v___x_2859_ = lean_io_get_num_heartbeats();
v___x_2860_ = l_Lean_firstFrontendMacroScope;
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__18);
v___x_2863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__21));
v___x_2864_ = lean_box(0);
lean_inc_n(v___y_2850_, 2);
v___x_2865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2865_, 0, v___y_2850_);
lean_ctor_set(v___x_2865_, 1, v___x_2861_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
v___x_2866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__22);
v___x_2867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__23);
v___x_2868_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2868_, 0, v___y_2853_);
lean_ctor_set(v___x_2868_, 1, v___x_2862_);
lean_ctor_set(v___x_2868_, 2, v___x_2863_);
lean_ctor_set(v___x_2868_, 3, v___x_2865_);
lean_ctor_set(v___x_2868_, 4, v___x_2866_);
lean_ctor_set(v___x_2868_, 5, v___x_2857_);
lean_ctor_set(v___x_2868_, 6, v___x_2858_);
lean_ctor_set(v___x_2868_, 7, v___x_2867_);
lean_ctor_set(v___x_2868_, 8, v___x_2646_);
v___x_2869_ = lean_st_mk_ref(v___x_2868_);
v___x_2870_ = l_Lean_inheritedTraceOptions;
v___x_2871_ = lean_st_ref_get(v___x_2870_);
v___x_2872_ = lean_st_ref_get(v___x_2869_);
v___x_2873_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2874_ = l_Lean_instInhabitedFileMap_default;
v___x_2875_ = lean_unsigned_to_nat(1000u);
v___x_2876_ = lean_box(0);
v___x_2877_ = l_Lean_Core_getMaxHeartbeats(v___y_2848_);
v___x_2878_ = lean_box(0);
lean_inc_ref(v___y_2848_);
v___x_2879_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2879_, 0, v___x_2873_);
lean_ctor_set(v___x_2879_, 1, v___x_2874_);
lean_ctor_set(v___x_2879_, 2, v___y_2848_);
lean_ctor_set(v___x_2879_, 3, v___x_2561_);
lean_ctor_set(v___x_2879_, 4, v___x_2875_);
lean_ctor_set(v___x_2879_, 5, v___x_2876_);
lean_ctor_set(v___x_2879_, 6, v___y_2850_);
lean_ctor_set(v___x_2879_, 7, v___x_2864_);
lean_ctor_set(v___x_2879_, 8, v___x_2859_);
lean_ctor_set(v___x_2879_, 9, v___x_2877_);
lean_ctor_set(v___x_2879_, 10, v___y_2850_);
lean_ctor_set(v___x_2879_, 11, v___x_2860_);
lean_ctor_set(v___x_2879_, 12, v___x_2878_);
lean_ctor_set(v___x_2879_, 13, v___x_2871_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*14, v_anyFailed_2562_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*14 + 1, v_anyFailed_2562_);
v_env_2880_ = lean_ctor_get(v___x_2872_, 0);
lean_inc_ref(v_env_2880_);
lean_dec(v___x_2872_);
v___x_2881_ = l_Lean_diagnostics;
v___x_2882_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__2(v___y_2848_, v___x_2881_);
v___x_2883_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2880_);
lean_dec_ref(v_env_2880_);
if (v___x_2883_ == 0)
{
if (v___x_2882_ == 0)
{
v___y_2814_ = v___x_2882_;
v___y_2815_ = v___y_2847_;
v___y_2816_ = v___x_2857_;
v___y_2817_ = v_anyUnlocated_2856_;
v___y_2818_ = v_records_2855_;
v___y_2819_ = v___y_2851_;
v___y_2820_ = v___y_2854_;
v___y_2821_ = v___y_2848_;
v___y_2822_ = v___y_2849_;
v___y_2823_ = v___y_2852_;
v___y_2824_ = v___x_2869_;
v___y_2825_ = v___x_2879_;
v___y_2826_ = v___x_2587_;
goto v___jp_2813_;
}
else
{
v___y_2814_ = v___x_2882_;
v___y_2815_ = v___y_2847_;
v___y_2816_ = v___x_2857_;
v___y_2817_ = v_anyUnlocated_2856_;
v___y_2818_ = v_records_2855_;
v___y_2819_ = v___y_2851_;
v___y_2820_ = v___y_2854_;
v___y_2821_ = v___y_2848_;
v___y_2822_ = v___y_2849_;
v___y_2823_ = v___y_2852_;
v___y_2824_ = v___x_2869_;
v___y_2825_ = v___x_2879_;
v___y_2826_ = v___x_2883_;
goto v___jp_2813_;
}
}
else
{
v___y_2814_ = v___x_2882_;
v___y_2815_ = v___y_2847_;
v___y_2816_ = v___x_2857_;
v___y_2817_ = v_anyUnlocated_2856_;
v___y_2818_ = v_records_2855_;
v___y_2819_ = v___y_2851_;
v___y_2820_ = v___y_2854_;
v___y_2821_ = v___y_2848_;
v___y_2822_ = v___y_2849_;
v___y_2823_ = v___y_2852_;
v___y_2824_ = v___x_2869_;
v___y_2825_ = v___x_2879_;
v___y_2826_ = v___x_2882_;
goto v___jp_2813_;
}
}
v___jp_2884_:
{
if (v___y_2890_ == 0)
{
lean_object* v___x_2894_; size_t v_sz_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
v___x_2894_ = lean_box(0);
v_sz_2895_ = lean_array_size(v___y_2886_);
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__13(v___x_2539_, v___y_2886_, v_sz_2895_, v___x_2896_, v___x_2894_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2897_) == 0)
{
uint8_t v___x_2898_; 
lean_dec_ref_known(v___x_2897_, 1);
v___x_2898_ = lean_unbox(v_snd_2642_);
lean_dec(v_snd_2642_);
v___y_2847_ = v___y_2893_;
v___y_2848_ = v___y_2885_;
v___y_2849_ = v___y_2888_;
v___y_2850_ = v___y_2887_;
v___y_2851_ = v___y_2889_;
v___y_2852_ = v___y_2890_;
v___y_2853_ = v___y_2891_;
v___y_2854_ = v___y_2892_;
v_records_2855_ = v_fst_2641_;
v_anyUnlocated_2856_ = v___x_2898_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___x_2649_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2899_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2897_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2897_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v___x_2907_; size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v_fst_2641_);
lean_ctor_set(v___x_2907_, 1, v_snd_2642_);
v_sz_2908_ = lean_array_size(v___y_2886_);
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___y_2890_, v___y_2886_, v_sz_2908_, v___x_2909_, v___x_2907_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v_fst_2912_; lean_object* v_snd_2913_; uint8_t v___x_2914_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v_fst_2912_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_fst_2912_);
v_snd_2913_ = lean_ctor_get(v_a_2911_, 1);
lean_inc(v_snd_2913_);
lean_dec(v_a_2911_);
v___x_2914_ = lean_unbox(v_snd_2913_);
lean_dec(v_snd_2913_);
v___y_2847_ = v___y_2893_;
v___y_2848_ = v___y_2885_;
v___y_2849_ = v___y_2888_;
v___y_2850_ = v___y_2887_;
v___y_2851_ = v___y_2889_;
v___y_2852_ = v___y_2890_;
v___y_2853_ = v___y_2891_;
v___y_2854_ = v___y_2892_;
v_records_2855_ = v_fst_2912_;
v_anyUnlocated_2856_ = v___x_2914_;
goto v___jp_2846_;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2915_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2910_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2910_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
v___jp_2923_:
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_array_get_size(v___y_2931_);
v___x_2933_ = lean_nat_dec_eq(v___x_2932_, v___x_2561_);
if (v___x_2933_ == 0)
{
v___y_2885_ = v___y_2924_;
v___y_2886_ = v___y_2931_;
v___y_2887_ = v___y_2926_;
v___y_2888_ = v___y_2925_;
v___y_2889_ = v___y_2927_;
v___y_2890_ = v___y_2928_;
v___y_2891_ = v___y_2929_;
v___y_2892_ = v___y_2930_;
v___y_2893_ = v_anyUnlocated_2563_;
goto v___jp_2884_;
}
else
{
v___y_2885_ = v___y_2924_;
v___y_2886_ = v___y_2931_;
v___y_2887_ = v___y_2926_;
v___y_2888_ = v___y_2925_;
v___y_2889_ = v___y_2927_;
v___y_2890_ = v___y_2928_;
v___y_2891_ = v___y_2929_;
v___y_2892_ = v___y_2930_;
v___y_2893_ = v_anyFailed_2562_;
goto v___jp_2884_;
}
}
v___jp_2934_:
{
lean_object* v___x_2940_; lean_object* v_toEnvExtension_2941_; lean_object* v_asyncMode_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v_merged_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2957_; 
v___x_2940_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2941_ = lean_ctor_get(v___x_2940_, 0);
v_asyncMode_2942_ = lean_ctor_get(v_toEnvExtension_2941_, 2);
v___x_2943_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2944_ = lean_box(0);
lean_inc_ref(v___y_2938_);
v___x_2945_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2943_, v___x_2940_, v___y_2938_, v_asyncMode_2942_, v___x_2944_);
v_merged_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2945_, 1);
lean_dec(v_unused_2958_);
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_merged_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2957_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v_merged_2946_);
lean_ctor_set(v___x_2948_, 0, v___y_2939_);
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___y_2939_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_merged_2946_);
v___x_2951_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = l_Lean_Name_getRoot(v_a_2590_);
v___x_2953_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v___y_2938_, v___x_2952_);
if (v___y_2936_ == 0)
{
v___y_2924_ = v___y_2935_;
v___y_2925_ = v___x_2951_;
v___y_2926_ = v___x_2944_;
v___y_2927_ = v___y_2936_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v___y_2938_;
v___y_2930_ = v___x_2952_;
v___y_2931_ = v___x_2953_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_array_get_size(v___x_2953_);
v___x_2955_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__15(v___x_2951_, v___x_2953_, v___x_2561_, v___x_2954_);
lean_dec_ref(v___x_2953_);
v___y_2924_ = v___y_2935_;
v___y_2925_ = v___x_2951_;
v___y_2926_ = v___x_2944_;
v___y_2927_ = v___y_2936_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v___y_2938_;
v___y_2930_ = v___x_2952_;
v___y_2931_ = v___x_2955_;
goto v___jp_2923_;
}
}
}
}
v___jp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_compacted_region_free(v_snd_2596_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint32_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2961_, 1);
lean_inc(v_a_2590_);
v___x_2962_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2962_, 0, v_a_2590_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*1, v_anyFailed_2562_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*1 + 1, v_anyUnlocated_2563_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*1 + 2, v_anyFailed_2562_);
v___x_2963_ = lean_unsigned_to_nat(2u);
v___x_2964_ = lean_mk_empty_array_with_capacity(v___x_2963_);
v___x_2965_ = lean_array_push(v___x_2964_, v___x_2962_);
v___x_2966_ = lean_array_push(v___x_2965_, v_envLinterModule_2586_);
v___x_2967_ = l_Lean_Options_empty;
v___x_2968_ = 1024;
v___x_2969_ = lean_box(1);
v___x_2970_ = l_Lean_importModules(v___x_2966_, v___x_2967_, v___x_2968_, v___x_2646_, v_anyFailed_2562_, v_anyUnlocated_2563_, v___y_2960_, v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v_linterOverrides_2972_; uint8_t v_lintOnly_2973_; uint8_t v_recordExceptions_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v_linterOverrides_2972_ = lean_ctor_get(v_args_2540_, 0);
v_lintOnly_2973_ = lean_ctor_get_uint8(v_args_2540_, sizeof(void*)*3);
v_recordExceptions_2974_ = lean_ctor_get_uint8(v_args_2540_, sizeof(void*)*3 + 1);
v___x_2975_ = lean_array_get_size(v_linterOverrides_2972_);
v___x_2976_ = lean_nat_dec_lt(v___x_2561_, v___x_2975_);
if (v___x_2976_ == 0)
{
v___y_2935_ = v___x_2967_;
v___y_2936_ = v_lintOnly_2973_;
v___y_2937_ = v_recordExceptions_2974_;
v___y_2938_ = v_a_2971_;
v___y_2939_ = v___x_2967_;
goto v___jp_2934_;
}
else
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_nat_dec_le(v___x_2975_, v___x_2975_);
if (v___x_2977_ == 0)
{
if (v___x_2976_ == 0)
{
v___y_2935_ = v___x_2967_;
v___y_2936_ = v_lintOnly_2973_;
v___y_2937_ = v_recordExceptions_2974_;
v___y_2938_ = v_a_2971_;
v___y_2939_ = v___x_2967_;
goto v___jp_2934_;
}
else
{
size_t v___x_2978_; size_t v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = ((size_t)0ULL);
v___x_2979_ = lean_usize_of_nat(v___x_2975_);
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16(v_linterOverrides_2972_, v___x_2978_, v___x_2979_, v___x_2967_);
v___y_2935_ = v___x_2967_;
v___y_2936_ = v_lintOnly_2973_;
v___y_2937_ = v_recordExceptions_2974_;
v___y_2938_ = v_a_2971_;
v___y_2939_ = v___x_2980_;
goto v___jp_2934_;
}
}
else
{
size_t v___x_2981_; size_t v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = ((size_t)0ULL);
v___x_2982_ = lean_usize_of_nat(v___x_2975_);
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__16(v_linterOverrides_2972_, v___x_2981_, v___x_2982_, v___x_2967_);
v___y_2935_ = v___x_2967_;
v___y_2936_ = v_lintOnly_2973_;
v___y_2937_ = v_recordExceptions_2974_;
v___y_2938_ = v_a_2971_;
v___y_2939_ = v___x_2983_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___x_2649_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec(v___x_2541_);
v_a_2984_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2970_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2970_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v___x_2649_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_del_object(v___x_2604_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2598_);
lean_dec_ref_known(v_envLinterModule_2586_, 1);
lean_dec(v___x_2541_);
v_a_2992_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2961_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2961_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref_known(v_envLinterModule_2586_, 1);
lean_dec_ref(v_b_2545_);
lean_dec(v___x_2541_);
v_a_3008_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2593_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2593_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref_known(v_envLinterModule_2586_, 1);
lean_dec_ref(v_b_2545_);
lean_dec(v___x_2541_);
v_a_3016_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2591_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2591_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref_known(v_envLinterModule_2586_, 1);
lean_dec_ref(v_b_2545_);
lean_dec(v___x_2541_);
v_a_3024_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2589_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2589_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
v___jp_2547_:
{
size_t v___x_2549_; size_t v___x_2550_; 
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_add(v_i_2544_, v___x_2549_);
v_i_2544_ = v___x_2550_;
v_b_2545_ = v_a_2548_;
goto _start;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_mk_io_user_error(v_a_2553_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = l_Lean_MessageData_toString(v_msg_2557_);
v___x_2559_ = lean_mk_io_user_error(v___x_2558_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
v___jp_2564_:
{
if (lean_obj_tag(v_a_2565_) == 0)
{
lean_object* v_msg_2566_; 
v_msg_2566_ = lean_ctor_get(v_a_2565_, 1);
lean_inc_ref(v_msg_2566_);
lean_dec_ref_known(v_a_2565_, 2);
v_msg_2557_ = v_msg_2566_;
goto v___jp_2556_;
}
else
{
lean_object* v_id_2567_; lean_object* v___x_2568_; 
v_id_2567_ = lean_ctor_get(v_a_2565_, 0);
lean_inc(v_id_2567_);
lean_dec_ref_known(v_a_2565_, 2);
v___x_2568_ = l_Lean_InternalExceptionId_getName(v_id_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v_id_2567_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__0));
v___x_2571_ = l_Lean_Name_toString(v_a_2569_, v_anyUnlocated_2563_);
v___x_2572_ = lean_string_append(v___x_2570_, v___x_2571_);
lean_dec_ref(v___x_2571_);
v_a_2553_ = v___x_2572_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref_known(v___x_2568_, 1);
v___x_2573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__1));
v___x_2574_ = l_Nat_reprFast(v_id_2567_);
v___x_2575_ = lean_string_append(v___x_2573_, v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__2));
v___x_2577_ = lean_string_append(v___x_2575_, v___x_2576_);
v_a_2553_ = v___x_2577_;
goto v___jp_2552_;
}
}
}
v___jp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_box(v___y_2579_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___y_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_box(v_anyUnlocated_2563_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
v_a_2548_ = v___x_2584_;
goto v___jp_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___boxed(lean_object* v___x_3032_, lean_object* v_args_3033_, lean_object* v___x_3034_, lean_object* v_as_3035_, lean_object* v_sz_3036_, lean_object* v_i_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_){
_start:
{
size_t v_sz_boxed_3040_; size_t v_i_boxed_3041_; lean_object* v_res_3042_; 
v_sz_boxed_3040_ = lean_unbox_usize(v_sz_3036_);
lean_dec(v_sz_3036_);
v_i_boxed_3041_ = lean_unbox_usize(v_i_3037_);
lean_dec(v_i_3037_);
v_res_3042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17(v___x_3032_, v_args_3033_, v___x_3034_, v_as_3035_, v_sz_boxed_3040_, v_i_boxed_3041_, v_b_3038_);
lean_dec_ref(v_as_3035_);
lean_dec_ref(v_args_3033_);
lean_dec(v___x_3032_);
return v_res_3042_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = 0;
v___x_3045_ = lean_box_uint32(v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = 1;
v___x_3047_ = lean_box_uint32(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_3048_){
_start:
{
lean_object* v_mods_3050_; uint8_t v_recordExceptions_3051_; lean_object* v_srcSearchPath_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v_anyFailed_3055_; 
v_mods_3050_ = lean_ctor_get(v_args_3048_, 1);
lean_inc_ref(v_mods_3050_);
v_recordExceptions_3051_ = lean_ctor_get_uint8(v_args_3048_, sizeof(void*)*3 + 1);
v_srcSearchPath_3052_ = lean_ctor_get(v_args_3048_, 2);
v___x_3053_ = lean_array_get_size(v_mods_3050_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v_anyFailed_3055_ = lean_nat_dec_eq(v___x_3053_, v___x_3054_);
if (v_anyFailed_3055_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; size_t v_sz_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
lean_inc(v_srcSearchPath_3052_);
v___x_3058_ = l_List_appendTR___redArg(v_srcSearchPath_3052_, v_a_3057_);
v___x_3059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17___closed__7));
v___x_3060_ = lean_box(v_anyFailed_3055_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = lean_box(v_anyFailed_3055_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3061_);
v_sz_3064_ = lean_array_size(v_mods_3050_);
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__17(v___x_3053_, v_args_3048_, v___x_3058_, v_mods_3050_, v_sz_3064_, v___x_3065_, v___x_3063_);
lean_dec_ref(v_mods_3050_);
lean_dec_ref(v_args_3048_);
if (lean_obj_tag(v___x_3066_) == 0)
{
if (v_recordExceptions_3051_ == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3081_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3081_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3081_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_fst_3071_; uint8_t v___x_3072_; 
v_fst_3071_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_fst_3071_);
lean_dec(v_a_3067_);
v___x_3072_ = lean_unbox(v_fst_3071_);
lean_dec(v_fst_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3073_);
v___x_3075_ = v___x_3069_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3077_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3077_);
v___x_3079_ = v___x_3069_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v_snd_3083_; lean_object* v_fst_3084_; lean_object* v_snd_3085_; lean_object* v___x_3086_; 
v_a_3082_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3066_, 1);
v_snd_3083_ = lean_ctor_get(v_a_3082_, 1);
lean_inc(v_snd_3083_);
lean_dec(v_a_3082_);
v_fst_3084_ = lean_ctor_get(v_snd_3083_, 0);
lean_inc(v_fst_3084_);
v_snd_3085_ = lean_ctor_get(v_snd_3083_, 1);
lean_inc(v_snd_3085_);
lean_dec(v_snd_3083_);
v___x_3086_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_3084_);
lean_dec(v_fst_3084_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3099_; 
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3086_, 0);
lean_dec(v_unused_3100_);
v___x_3088_ = v___x_3086_;
v_isShared_3089_ = v_isSharedCheck_3099_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v___x_3086_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3099_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_unbox(v_snd_3085_);
lean_dec(v_snd_3085_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3091_);
v___x_3093_ = v___x_3088_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3095_);
v___x_3097_ = v___x_3088_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_snd_3085_);
v_a_3101_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3086_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3086_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3066_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3066_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_mods_3050_);
lean_dec_ref(v_args_3048_);
v_a_3117_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3056_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3056_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v_mods_3050_);
lean_dec_ref(v_args_3048_);
v___x_3125_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_3126_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3126_, 0);
lean_dec(v_unused_3135_);
v___x_3128_ = v___x_3126_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_dec(v___x_3126_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3126_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3126_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lake_BuiltinLint_run(v_args_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4(lean_object* v_declName_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___redArg(v_declName_3147_, v___y_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4___boxed(lean_object* v_declName_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__4(v_declName_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5(lean_object* v_declName_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___redArg(v_declName_3157_, v___y_3159_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5___boxed(lean_object* v_declName_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lake_BuiltinLint_run_spec__4_spec__5(v_declName_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8(lean_object* v_00_u03b1_3167_, lean_object* v_constName_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___redArg(v_constName_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_constName_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8(v_00_u03b1_3173_, v_constName_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21(lean_object* v_00_u03b1_3179_, lean_object* v_ref_3180_, lean_object* v_constName_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___redArg(v_ref_3180_, v_constName_3181_, v___y_3182_, v___y_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21___boxed(lean_object* v_00_u03b1_3186_, lean_object* v_ref_3187_, lean_object* v_constName_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21(v_00_u03b1_3186_, v_ref_3187_, v_constName_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v_ref_3187_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23(lean_object* v_00_u03b1_3193_, lean_object* v_ref_3194_, lean_object* v_msg_3195_, lean_object* v_declHint_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___redArg(v_ref_3194_, v_msg_3195_, v_declHint_3196_, v___y_3197_, v___y_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_ref_3202_, lean_object* v_msg_3203_, lean_object* v_declHint_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23(v_00_u03b1_3201_, v_ref_3202_, v_msg_3203_, v_declHint_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v_ref_3202_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25(lean_object* v_msg_3209_, lean_object* v_declHint_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___redArg(v_msg_3209_, v_declHint_3210_, v___y_3212_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25___boxed(lean_object* v_msg_3215_, lean_object* v_declHint_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__24_spec__25(v_msg_3215_, v_declHint_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25(lean_object* v_00_u03b1_3221_, lean_object* v_ref_3222_, lean_object* v_msg_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___redArg(v_ref_3222_, v_msg_3223_, v___y_3224_, v___y_3225_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_ref_3229_, lean_object* v_msg_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25(v_00_u03b1_3228_, v_ref_3229_, v_msg_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v_ref_3229_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27(lean_object* v_00_u03b1_3235_, lean_object* v_msg_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___redArg(v_msg_3236_, v___y_3237_, v___y_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27___boxed(lean_object* v_00_u03b1_3241_, lean_object* v_msg_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__5_spec__7_spec__8_spec__21_spec__23_spec__25_spec__27(v_00_u03b1_3241_, v_msg_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3246_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_EnvLinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuiltinLint_instInhabitedExceptionRecord_default = _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default();
lean_mark_persistent(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default);
l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord = _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord();
lean_mark_persistent(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord);
l_Lake_BuiltinLint_run___boxed__const__1 = _init_l_Lake_BuiltinLint_run___boxed__const__1();
lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__1);
l_Lake_BuiltinLint_run___boxed__const__2 = _init_l_Lake_BuiltinLint_run___boxed__const__2();
lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_EnvLinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_BuiltinLint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_BuiltinLint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_BuiltinLint(builtin);
}
#ifdef __cplusplus
}
#endif
