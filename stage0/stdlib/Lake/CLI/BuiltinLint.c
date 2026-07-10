// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter public import Lean.Linter.PersistentLintLog import Lean.CoreM import Lean.DocString.Extension import Lean.Elab.DocString.Builtin.Postponed import Lake.Config.Workspace
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
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* lean_get_stdout();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
extern lean_object* l_linter_doc_deferred;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Doc_DeferredCheck_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "the docstring of `"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "module docstring #"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "warning: could not determine the position of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "`; cannot record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "warning: could not locate source file for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` to record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "error: in module `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "`, in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": error: in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2_value;
static const lean_closure_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3_value;
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_value;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17;
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_value;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "warning: could not determine the command position of a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` text-linter warning in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; skipping its exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "warning: no declaration range for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "-- No environment linters were run for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; uint8_t v___x_139_; 
v___x_136_ = lean_array_get_size(v_snd_134_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
v___x_139_ = lean_bool_not(v___x_138_);
v___y_131_ = v___x_139_;
goto v___jp_130_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_140_, lean_object* v_as_141_, lean_object* v_i_142_, lean_object* v_stop_143_, lean_object* v_b_144_){
_start:
{
size_t v_i_boxed_145_; size_t v_stop_boxed_146_; lean_object* v_res_147_; 
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_143_);
lean_dec(v_stop_143_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_140_, v_as_141_, v_i_boxed_145_, v_stop_boxed_146_, v_b_144_);
lean_dec_ref(v_as_141_);
lean_dec(v_pkgRoot_140_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_150_, lean_object* v_pkgRoot_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_154_ = l_Lean_Linter_getAllLints(v_env_150_);
v___x_155_ = lean_array_get_size(v___x_154_);
v___x_156_ = lean_nat_dec_lt(v___x_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec_ref(v___x_154_);
return v___x_153_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_le(v___x_155_, v___x_155_);
if (v___x_157_ == 0)
{
if (v___x_156_ == 0)
{
lean_dec_ref(v___x_154_);
return v___x_153_;
}
else
{
size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((size_t)0ULL);
v___x_159_ = lean_usize_of_nat(v___x_155_);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_151_, v___x_154_, v___x_158_, v___x_159_, v___x_153_);
lean_dec_ref(v___x_154_);
return v___x_160_;
}
}
else
{
size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((size_t)0ULL);
v___x_162_ = lean_usize_of_nat(v___x_155_);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_151_, v___x_154_, v___x_161_, v___x_162_, v___x_153_);
lean_dec_ref(v___x_154_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_164_, lean_object* v_pkgRoot_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_164_, v_pkgRoot_165_);
lean_dec(v_pkgRoot_165_);
lean_dec_ref(v_env_164_);
return v_res_166_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_167_){
_start:
{
uint8_t v_isModule_169_; 
v_isModule_169_ = lean_ctor_get_uint8(v_modData_167_, sizeof(void*)*5);
return v_isModule_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_170_);
lean_dec_ref(v_modData_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_176_){
_start:
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 32;
v___x_178_ = lean_uint32_dec_eq(v_c_176_, v___x_177_);
if (v___x_178_ == 0)
{
uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 9;
v___x_180_ = lean_uint32_dec_eq(v_c_176_, v___x_179_);
return v___x_180_;
}
else
{
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_181_){
_start:
{
uint32_t v_c_boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_c_boxed_182_ = lean_unbox_uint32(v_c_181_);
lean_dec(v_c_181_);
v_res_183_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_185_, lean_object* v_stopPos_186_, lean_object* v_i_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_nat_dec_lt(v_i_187_, v_stopPos_186_);
if (v___x_188_ == 0)
{
return v_i_187_;
}
else
{
uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_string_utf8_get(v_s_185_, v_i_187_);
v___x_190_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_189_);
if (v___x_190_ == 0)
{
return v_i_187_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_string_utf8_next(v_s_185_, v_i_187_);
lean_dec(v_i_187_);
v_i_187_ = v___x_191_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_193_, lean_object* v_stopPos_194_, lean_object* v_i_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_193_, v_stopPos_194_, v_i_195_);
lean_dec(v_stopPos_194_);
lean_dec_ref(v_s_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_e_200_; lean_object* v___x_201_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_string_utf8_byte_size(v_line_197_);
v_e_200_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_197_, v___x_199_, v___x_198_);
v___x_201_ = lean_string_utf8_extract(v_line_197_, v___x_198_, v_e_200_);
lean_dec(v_e_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_202_);
lean_dec_ref(v_line_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_208_);
lean_dec_ref(v_s_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
return v_x_210_;
}
else
{
lean_object* v_key_212_; lean_object* v_value_213_; lean_object* v_tail_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_key_212_ = lean_ctor_get(v_x_211_, 0);
v_value_213_ = lean_ctor_get(v_x_211_, 1);
v_tail_214_ = lean_ctor_get(v_x_211_, 2);
lean_inc(v_value_213_);
lean_inc(v_key_212_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v_key_212_);
lean_ctor_set(v___x_215_, 1, v_value_213_);
v___x_216_ = lean_array_push(v_x_210_, v___x_215_);
v_x_210_ = v___x_216_;
v_x_211_ = v_tail_214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_218_, v_x_219_);
lean_dec(v_x_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_221_, size_t v_i_222_, size_t v_stop_223_, lean_object* v_b_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_usize_dec_eq(v_i_222_, v_stop_223_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; 
v___x_226_ = lean_array_uget_borrowed(v_as_221_, v_i_222_);
v___x_227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_224_, v___x_226_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_222_, v___x_228_);
v_i_222_ = v___x_229_;
v_b_224_ = v___x_227_;
goto _start;
}
else
{
return v_b_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_231_, lean_object* v_i_232_, lean_object* v_stop_233_, lean_object* v_b_234_){
_start:
{
size_t v_i_boxed_235_; size_t v_stop_boxed_236_; lean_object* v_res_237_; 
v_i_boxed_235_ = lean_unbox_usize(v_i_232_);
lean_dec(v_i_232_);
v_stop_boxed_236_ = lean_unbox_usize(v_stop_233_);
lean_dec(v_stop_233_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_231_, v_i_boxed_235_, v_stop_boxed_236_, v_b_234_);
lean_dec_ref(v_as_231_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_putStr_241_; lean_object* v___x_242_; 
v___x_240_ = lean_get_stderr();
v_putStr_241_ = lean_ctor_get(v___x_240_, 4);
lean_inc_ref(v_putStr_241_);
lean_dec_ref(v___x_240_);
v___x_242_ = lean_apply_2(v_putStr_241_, v_s_238_, lean_box(0));
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_246_){
_start:
{
uint32_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = 10;
v___x_249_ = lean_string_push(v_s_246_, v___x_248_);
v___x_250_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
return v_x_254_;
}
else
{
lean_object* v_key_256_; lean_object* v_value_257_; lean_object* v_tail_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_key_256_ = lean_ctor_get(v_x_255_, 0);
v_value_257_ = lean_ctor_get(v_x_255_, 1);
v_tail_258_ = lean_ctor_get(v_x_255_, 2);
lean_inc(v_value_257_);
lean_inc(v_key_256_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_key_256_);
lean_ctor_set(v___x_259_, 1, v_value_257_);
v___x_260_ = lean_array_push(v_x_254_, v___x_259_);
v_x_254_ = v___x_260_;
v_x_255_ = v_tail_258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_262_, v_x_263_);
lean_dec(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_, lean_object* v_b_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; size_t v___x_272_; size_t v___x_273_; 
v___x_270_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
v___x_271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_268_, v___x_270_);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_266_, v___x_272_);
v_i_266_ = v___x_273_;
v_b_268_ = v___x_271_;
goto _start;
}
else
{
return v_b_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_275_, lean_object* v_i_276_, lean_object* v_stop_277_, lean_object* v_b_278_){
_start:
{
size_t v_i_boxed_279_; size_t v_stop_boxed_280_; lean_object* v_res_281_; 
v_i_boxed_279_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_stop_boxed_280_ = lean_unbox_usize(v_stop_277_);
lean_dec(v_stop_277_);
v_res_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_275_, v_i_boxed_279_, v_stop_boxed_280_, v_b_278_);
lean_dec_ref(v_as_275_);
return v_res_281_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_fst_284_; lean_object* v_fst_285_; uint8_t v___x_286_; 
v_fst_284_ = lean_ctor_get(v_b_283_, 0);
v_fst_285_ = lean_ctor_get(v_a_282_, 0);
v___x_286_ = lean_nat_dec_lt(v_fst_284_, v_fst_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_287_, v_b_288_);
lean_dec_ref(v_b_288_);
lean_dec_ref(v_a_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_291_, lean_object* v_pivot_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_k_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_k_295_, v_hi_291_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_k_295_);
v___x_297_ = lean_array_fswap(v_as_293_, v_i_294_, v_hi_291_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_i_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v_fst_299_; lean_object* v___x_300_; lean_object* v_fst_301_; uint8_t v___x_302_; 
v_fst_299_ = lean_ctor_get(v_pivot_292_, 0);
v___x_300_ = lean_array_fget_borrowed(v_as_293_, v_k_295_);
v_fst_301_ = lean_ctor_get(v___x_300_, 0);
v___x_302_ = lean_nat_dec_lt(v_fst_299_, v_fst_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_k_295_, v___x_303_);
lean_dec(v_k_295_);
v_k_295_ = v___x_304_;
goto _start;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_array_fswap(v_as_293_, v_i_294_, v_k_295_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_294_, v___x_307_);
lean_dec(v_i_294_);
v___x_309_ = lean_nat_add(v_k_295_, v___x_307_);
lean_dec(v_k_295_);
v_as_293_ = v___x_306_;
v_i_294_ = v___x_308_;
v_k_295_ = v___x_309_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_311_, lean_object* v_pivot_312_, lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_311_, v_pivot_312_, v_as_313_, v_i_314_, v_k_315_);
lean_dec_ref(v_pivot_312_);
lean_dec(v_hi_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_317_, lean_object* v_as_318_, lean_object* v_lo_319_, lean_object* v_hi_320_){
_start:
{
lean_object* v___y_322_; uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_lt(v_lo_319_, v_hi_320_);
if (v___x_332_ == 0)
{
lean_dec(v_lo_319_);
return v_as_318_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_mid_335_; lean_object* v___y_337_; lean_object* v___y_343_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_333_ = lean_nat_add(v_lo_319_, v_hi_320_);
v___x_334_ = lean_unsigned_to_nat(1u);
v_mid_335_ = lean_nat_shiftr(v___x_333_, v___x_334_);
lean_dec(v___x_333_);
v___x_348_ = lean_array_fget_borrowed(v_as_318_, v_mid_335_);
v___x_349_ = lean_array_fget_borrowed(v_as_318_, v_lo_319_);
v___x_350_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
v___y_343_ = v_as_318_;
goto v___jp_342_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_array_fswap(v_as_318_, v_lo_319_, v_mid_335_);
v___y_343_ = v___x_351_;
goto v___jp_342_;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_array_fget_borrowed(v___y_337_, v_mid_335_);
v___x_339_ = lean_array_fget_borrowed(v___y_337_, v_hi_320_);
v___x_340_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_mid_335_);
v___y_322_ = v___y_337_;
goto v___jp_321_;
}
else
{
lean_object* v___x_341_; 
v___x_341_ = lean_array_fswap(v___y_337_, v_mid_335_, v_hi_320_);
lean_dec(v_mid_335_);
v___y_322_ = v___x_341_;
goto v___jp_321_;
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_fget_borrowed(v___y_343_, v_hi_320_);
v___x_345_ = lean_array_fget_borrowed(v___y_343_, v_lo_319_);
v___x_346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
v___y_337_ = v___y_343_;
goto v___jp_336_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_array_fswap(v___y_343_, v_lo_319_, v_hi_320_);
v___y_337_ = v___x_347_;
goto v___jp_336_;
}
}
}
v___jp_321_:
{
lean_object* v_pivot_323_; lean_object* v___x_324_; lean_object* v_fst_325_; lean_object* v_snd_326_; uint8_t v___x_327_; 
v_pivot_323_ = lean_array_fget(v___y_322_, v_hi_320_);
lean_inc_n(v_lo_319_, 2);
v___x_324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_320_, v_pivot_323_, v___y_322_, v_lo_319_, v_lo_319_);
lean_dec(v_pivot_323_);
v_fst_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_fst_325_);
v_snd_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v___x_324_);
v___x_327_ = lean_nat_dec_le(v_hi_320_, v_fst_325_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_317_, v_snd_326_, v_lo_319_, v_fst_325_);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v_fst_325_, v___x_329_);
lean_dec(v_fst_325_);
v_as_318_ = v___x_328_;
v_lo_319_ = v___x_330_;
goto _start;
}
else
{
lean_dec(v_fst_325_);
lean_dec(v_lo_319_);
return v_snd_326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_352_, lean_object* v_as_353_, lean_object* v_lo_354_, lean_object* v_hi_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_352_, v_as_353_, v_lo_354_, v_hi_355_);
lean_dec(v_hi_355_);
lean_dec(v_n_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v_it_363_; lean_object* v_startInclusive_364_; lean_object* v_endExclusive_365_; 
if (lean_obj_tag(v_a_360_) == 0)
{
lean_object* v_currPos_369_; lean_object* v_searcher_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_396_; 
v_currPos_369_ = lean_ctor_get(v_a_360_, 0);
v_searcher_370_ = lean_ctor_get(v_a_360_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_360_);
if (v_isSharedCheck_396_ == 0)
{
v___x_372_ = v_a_360_;
v_isShared_373_ = v_isSharedCheck_396_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_searcher_370_);
lean_inc(v_currPos_369_);
lean_dec(v_a_360_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_396_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_startInclusive_374_; lean_object* v_endExclusive_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_startInclusive_374_ = lean_ctor_get(v___x_358_, 1);
v_endExclusive_375_ = lean_ctor_get(v___x_358_, 2);
v___x_376_ = lean_nat_sub(v_endExclusive_375_, v_startInclusive_374_);
v___x_377_ = lean_nat_dec_eq(v_searcher_370_, v___x_376_);
lean_dec(v___x_376_);
if (v___x_377_ == 0)
{
uint32_t v___x_378_; uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = 10;
v___x_379_ = lean_string_utf8_get_fast(v_a_357_, v_searcher_370_);
v___x_380_ = lean_uint32_dec_eq(v___x_379_, v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_string_utf8_next_fast(v_a_357_, v_searcher_370_);
lean_dec(v_searcher_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_381_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_currPos_369_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_381_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
v_a_360_ = v___x_383_;
goto _start;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_slice_389_; lean_object* v_nextIt_391_; 
v___x_386_ = lean_string_utf8_next_fast(v_a_357_, v_searcher_370_);
v___x_387_ = lean_nat_sub(v___x_386_, v_searcher_370_);
v___x_388_ = lean_nat_add(v_searcher_370_, v___x_387_);
lean_dec(v___x_387_);
v_slice_389_ = l_String_Slice_subslice_x21(v___x_358_, v_currPos_369_, v_searcher_370_);
lean_inc(v___x_388_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_388_);
lean_ctor_set(v___x_372_, 0, v___x_388_);
v_nextIt_391_ = v___x_372_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_388_);
v_nextIt_391_ = v_reuseFailAlloc_394_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v_startInclusive_392_; lean_object* v_endExclusive_393_; 
v_startInclusive_392_ = lean_ctor_get(v_slice_389_, 0);
lean_inc(v_startInclusive_392_);
v_endExclusive_393_ = lean_ctor_get(v_slice_389_, 1);
lean_inc(v_endExclusive_393_);
lean_dec_ref(v_slice_389_);
v_it_363_ = v_nextIt_391_;
v_startInclusive_364_ = v_startInclusive_392_;
v_endExclusive_365_ = v_endExclusive_393_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v___x_395_; 
lean_del_object(v___x_372_);
lean_dec(v_searcher_370_);
v___x_395_ = lean_box(1);
lean_inc(v___x_359_);
v_it_363_ = v___x_395_;
v_startInclusive_364_ = v_currPos_369_;
v_endExclusive_365_ = v___x_359_;
goto v___jp_362_;
}
}
}
else
{
lean_dec(v___x_359_);
lean_dec_ref(v_a_357_);
return v_b_361_;
}
v___jp_362_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_inc_ref(v_a_357_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v_a_357_);
lean_ctor_set(v___x_366_, 1, v_startInclusive_364_);
lean_ctor_set(v___x_366_, 2, v_endExclusive_365_);
v___x_367_ = lean_array_push(v_b_361_, v___x_366_);
v_a_360_ = v_it_363_;
v_b_361_ = v___x_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_397_, lean_object* v___x_398_, lean_object* v___x_399_, lean_object* v_a_400_, lean_object* v_b_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_397_, v___x_398_, v___x_399_, v_a_400_, v_b_401_);
lean_dec_ref(v___x_398_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_403_, size_t v_i_404_, lean_object* v_bs_405_){
_start:
{
uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_lt(v_i_404_, v_sz_403_);
if (v___x_406_ == 0)
{
return v_bs_405_;
}
else
{
lean_object* v_v_407_; lean_object* v___x_408_; lean_object* v_bs_x27_409_; lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v_v_407_ = lean_array_uget(v_bs_405_, v_i_404_);
v___x_408_ = lean_unsigned_to_nat(0u);
v_bs_x27_409_ = lean_array_uset(v_bs_405_, v_i_404_, v___x_408_);
v___x_410_ = l_String_Slice_toString(v_v_407_);
lean_dec(v_v_407_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_404_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_409_, v_i_404_, v___x_410_);
v_i_404_ = v___x_412_;
v_bs_405_ = v___x_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_415_, lean_object* v_i_416_, lean_object* v_bs_417_){
_start:
{
size_t v_sz_boxed_418_; size_t v_i_boxed_419_; lean_object* v_res_420_; 
v_sz_boxed_418_ = lean_unbox_usize(v_sz_415_);
lean_dec(v_sz_415_);
v_i_boxed_419_ = lean_unbox_usize(v_i_416_);
lean_dec(v_i_416_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_418_, v_i_boxed_419_, v_bs_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
return v_x_421_;
}
else
{
lean_object* v_key_423_; lean_object* v_value_424_; lean_object* v_tail_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_448_; 
v_key_423_ = lean_ctor_get(v_x_422_, 0);
v_value_424_ = lean_ctor_get(v_x_422_, 1);
v_tail_425_ = lean_ctor_get(v_x_422_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_448_ == 0)
{
v___x_427_ = v_x_422_;
v_isShared_428_ = v_isSharedCheck_448_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_tail_425_);
lean_inc(v_value_424_);
lean_inc(v_key_423_);
lean_dec(v_x_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_448_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v_fold_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_429_ = lean_array_get_size(v_x_421_);
v___x_430_ = lean_uint64_of_nat(v_key_423_);
v___x_431_ = 32ULL;
v___x_432_ = lean_uint64_shift_right(v___x_430_, v___x_431_);
v_fold_433_ = lean_uint64_xor(v___x_430_, v___x_432_);
v___x_434_ = 16ULL;
v___x_435_ = lean_uint64_shift_right(v_fold_433_, v___x_434_);
v___x_436_ = lean_uint64_xor(v_fold_433_, v___x_435_);
v___x_437_ = lean_uint64_to_usize(v___x_436_);
v___x_438_ = lean_usize_of_nat(v___x_429_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_sub(v___x_438_, v___x_439_);
v___x_441_ = lean_usize_land(v___x_437_, v___x_440_);
v___x_442_ = lean_array_uget_borrowed(v_x_421_, v___x_441_);
lean_inc(v___x_442_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 2, v___x_442_);
v___x_444_ = v___x_427_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_key_423_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_value_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v___x_442_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_array_uset(v_x_421_, v___x_441_, v___x_444_);
v_x_421_ = v___x_445_;
v_x_422_ = v_tail_425_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_449_, lean_object* v_source_450_, lean_object* v_target_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_array_get_size(v_source_450_);
v___x_453_ = lean_nat_dec_lt(v_i_449_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec_ref(v_source_450_);
lean_dec(v_i_449_);
return v_target_451_;
}
else
{
lean_object* v_es_454_; lean_object* v___x_455_; lean_object* v_source_456_; lean_object* v_target_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_es_454_ = lean_array_fget(v_source_450_, v_i_449_);
v___x_455_ = lean_box(0);
v_source_456_ = lean_array_fset(v_source_450_, v_i_449_, v___x_455_);
v_target_457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_451_, v_es_454_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_add(v_i_449_, v___x_458_);
lean_dec(v_i_449_);
v_i_449_ = v___x_459_;
v_source_450_ = v_source_456_;
v_target_451_ = v_target_457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_nbuckets_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_462_ = lean_array_get_size(v_data_461_);
v___x_463_ = lean_unsigned_to_nat(2u);
v_nbuckets_464_ = lean_nat_mul(v___x_462_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_box(0);
v___x_467_ = lean_mk_array(v_nbuckets_464_, v___x_466_);
v___x_468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_465_, v_data_461_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
else
{
lean_object* v_key_472_; lean_object* v_tail_473_; uint8_t v___x_474_; 
v_key_472_ = lean_ctor_get(v_x_470_, 0);
v_tail_473_ = lean_ctor_get(v_x_470_, 2);
v___x_474_ = lean_nat_dec_eq(v_key_472_, v_a_469_);
if (v___x_474_ == 0)
{
v_x_470_ = v_tail_473_;
goto _start;
}
else
{
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_476_, v_x_477_);
lean_dec(v_x_477_);
lean_dec(v_a_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_480_, lean_object* v_b_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_dec(v_b_481_);
lean_dec(v_a_480_);
return v_x_482_;
}
else
{
lean_object* v_key_483_; lean_object* v_value_484_; lean_object* v_tail_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_497_; 
v_key_483_ = lean_ctor_get(v_x_482_, 0);
v_value_484_ = lean_ctor_get(v_x_482_, 1);
v_tail_485_ = lean_ctor_get(v_x_482_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_497_ == 0)
{
v___x_487_ = v_x_482_;
v_isShared_488_ = v_isSharedCheck_497_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_tail_485_);
lean_inc(v_value_484_);
lean_inc(v_key_483_);
lean_dec(v_x_482_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_497_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_key_483_, v_a_480_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_480_, v_b_481_, v_tail_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v___x_490_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_key_483_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_value_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v___x_490_);
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
lean_object* v___x_495_; 
lean_dec(v_value_484_);
lean_dec(v_key_483_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v_b_481_);
lean_ctor_set(v___x_487_, 0, v_a_480_);
v___x_495_ = v___x_487_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_480_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_b_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_tail_485_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v_size_501_; lean_object* v_buckets_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_545_; 
v_size_501_ = lean_ctor_get(v_m_498_, 0);
v_buckets_502_ = lean_ctor_get(v_m_498_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_m_498_);
if (v_isSharedCheck_545_ == 0)
{
v___x_504_ = v_m_498_;
v_isShared_505_ = v_isSharedCheck_545_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_buckets_502_);
lean_inc(v_size_501_);
lean_dec(v_m_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_545_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v_fold_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v_bkt_519_; uint8_t v___x_520_; 
v___x_506_ = lean_array_get_size(v_buckets_502_);
v___x_507_ = lean_uint64_of_nat(v_a_499_);
v___x_508_ = 32ULL;
v___x_509_ = lean_uint64_shift_right(v___x_507_, v___x_508_);
v_fold_510_ = lean_uint64_xor(v___x_507_, v___x_509_);
v___x_511_ = 16ULL;
v___x_512_ = lean_uint64_shift_right(v_fold_510_, v___x_511_);
v___x_513_ = lean_uint64_xor(v_fold_510_, v___x_512_);
v___x_514_ = lean_uint64_to_usize(v___x_513_);
v___x_515_ = lean_usize_of_nat(v___x_506_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_sub(v___x_515_, v___x_516_);
v___x_518_ = lean_usize_land(v___x_514_, v___x_517_);
v_bkt_519_ = lean_array_uget_borrowed(v_buckets_502_, v___x_518_);
v___x_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_499_, v_bkt_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v_size_x27_522_; lean_object* v___x_523_; lean_object* v_buckets_x27_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v_size_x27_522_ = lean_nat_add(v_size_501_, v___x_521_);
lean_dec(v_size_501_);
lean_inc(v_bkt_519_);
v___x_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_523_, 0, v_a_499_);
lean_ctor_set(v___x_523_, 1, v_b_500_);
lean_ctor_set(v___x_523_, 2, v_bkt_519_);
v_buckets_x27_524_ = lean_array_uset(v_buckets_502_, v___x_518_, v___x_523_);
v___x_525_ = lean_unsigned_to_nat(4u);
v___x_526_ = lean_nat_mul(v_size_x27_522_, v___x_525_);
v___x_527_ = lean_unsigned_to_nat(3u);
v___x_528_ = lean_nat_div(v___x_526_, v___x_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_array_get_size(v_buckets_x27_524_);
v___x_530_ = lean_nat_dec_le(v___x_528_, v___x_529_);
lean_dec(v___x_528_);
if (v___x_530_ == 0)
{
lean_object* v_val_531_; lean_object* v___x_533_; 
v_val_531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_524_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_val_531_);
lean_ctor_set(v___x_504_, 0, v_size_x27_522_);
v___x_533_ = v___x_504_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_size_x27_522_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_val_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_object* v___x_536_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_buckets_x27_524_);
lean_ctor_set(v___x_504_, 0, v_size_x27_522_);
v___x_536_ = v___x_504_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_size_x27_522_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_buckets_x27_524_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v___x_538_; lean_object* v_buckets_x27_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc(v_bkt_519_);
v___x_538_ = lean_box(0);
v_buckets_x27_539_ = lean_array_uset(v_buckets_502_, v___x_518_, v___x_538_);
v___x_540_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_499_, v_b_500_, v_bkt_519_);
v___x_541_ = lean_array_uset(v_buckets_x27_539_, v___x_518_, v___x_540_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_541_);
v___x_543_ = v___x_504_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_size_501_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_546_, lean_object* v_as_547_, size_t v_i_548_, size_t v_stop_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_eq(v_i_548_, v_stop_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_array_uget_borrowed(v_as_547_, v_i_548_);
v___x_552_ = lean_name_eq(v_a_546_, v___x_551_);
if (v___x_552_ == 0)
{
size_t v___x_553_; size_t v___x_554_; 
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_548_, v___x_553_);
v_i_548_ = v___x_554_;
goto _start;
}
else
{
return v___x_552_;
}
}
else
{
uint8_t v___x_556_; 
v___x_556_ = 0;
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_557_, lean_object* v_as_558_, lean_object* v_i_559_, lean_object* v_stop_560_){
_start:
{
size_t v_i_boxed_561_; size_t v_stop_boxed_562_; uint8_t v_res_563_; lean_object* v_r_564_; 
v_i_boxed_561_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_stop_boxed_562_ = lean_unbox_usize(v_stop_560_);
lean_dec(v_stop_560_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_557_, v_as_558_, v_i_boxed_561_, v_stop_boxed_562_);
lean_dec_ref(v_as_558_);
lean_dec(v_a_557_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v_as_565_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
return v___x_569_;
}
else
{
if (v___x_569_ == 0)
{
return v___x_569_;
}
else
{
size_t v___x_570_; size_t v___x_571_; uint8_t v___x_572_; 
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_568_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_566_, v_as_565_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_573_, lean_object* v_a_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_as_573_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_577_, lean_object* v_fallback_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_inc(v_fallback_578_);
return v_fallback_578_;
}
else
{
lean_object* v_key_580_; lean_object* v_value_581_; lean_object* v_tail_582_; uint8_t v___x_583_; 
v_key_580_ = lean_ctor_get(v_x_579_, 0);
v_value_581_ = lean_ctor_get(v_x_579_, 1);
v_tail_582_ = lean_ctor_get(v_x_579_, 2);
v___x_583_ = lean_nat_dec_eq(v_key_580_, v_a_577_);
if (v___x_583_ == 0)
{
v_x_579_ = v_tail_582_;
goto _start;
}
else
{
lean_inc(v_value_581_);
return v_value_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_585_, lean_object* v_fallback_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_585_, v_fallback_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec(v_fallback_586_);
lean_dec(v_a_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_589_, lean_object* v_a_590_, lean_object* v_fallback_591_){
_start:
{
lean_object* v_buckets_592_; lean_object* v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v_fold_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_buckets_592_ = lean_ctor_get(v_m_589_, 1);
v___x_593_ = lean_array_get_size(v_buckets_592_);
v___x_594_ = lean_uint64_of_nat(v_a_590_);
v___x_595_ = 32ULL;
v___x_596_ = lean_uint64_shift_right(v___x_594_, v___x_595_);
v_fold_597_ = lean_uint64_xor(v___x_594_, v___x_596_);
v___x_598_ = 16ULL;
v___x_599_ = lean_uint64_shift_right(v_fold_597_, v___x_598_);
v___x_600_ = lean_uint64_xor(v_fold_597_, v___x_599_);
v___x_601_ = lean_uint64_to_usize(v___x_600_);
v___x_602_ = lean_usize_of_nat(v___x_593_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_sub(v___x_602_, v___x_603_);
v___x_605_ = lean_usize_land(v___x_601_, v___x_604_);
v___x_606_ = lean_array_uget_borrowed(v_buckets_592_, v___x_605_);
v___x_607_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_590_, v_fallback_591_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_608_, lean_object* v_a_609_, lean_object* v_fallback_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_608_, v_a_609_, v_fallback_610_);
lean_dec(v_fallback_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_m_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_614_, size_t v_sz_615_, size_t v_i_616_, lean_object* v_b_617_){
_start:
{
lean_object* v_a_620_; uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_lt(v_i_616_, v_sz_615_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_b_617_);
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_a_626_ = lean_array_uget_borrowed(v_as_614_, v_i_616_);
v_fst_627_ = lean_ctor_get(v_a_626_, 0);
v_snd_628_ = lean_ctor_get(v_a_626_, 1);
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_617_, v_fst_627_, v___x_629_);
v___x_631_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_630_, v_snd_628_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_inc(v_snd_628_);
v___x_632_ = lean_array_push(v___x_630_, v_snd_628_);
lean_inc(v_fst_627_);
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_617_, v_fst_627_, v___x_632_);
v_a_620_ = v___x_633_;
goto v___jp_619_;
}
else
{
lean_dec(v___x_630_);
v_a_620_ = v_b_617_;
goto v___jp_619_;
}
}
v___jp_619_:
{
size_t v___x_621_; size_t v___x_622_; 
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_616_, v___x_621_);
v_i_616_ = v___x_622_;
v_b_617_ = v_a_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_640_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_634_, v_sz_boxed_639_, v_i_boxed_640_, v_b_637_);
lean_dec_ref(v_as_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_642_){
_start:
{
lean_object* v___x_644_; lean_object* v_putStr_645_; lean_object* v___x_646_; 
v___x_644_ = lean_get_stdout();
v_putStr_645_ = lean_ctor_get(v___x_644_, 4);
lean_inc_ref(v_putStr_645_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_apply_2(v_putStr_645_, v_s_642_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_650_){
_start:
{
uint32_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = 10;
v___x_653_ = lean_string_push(v_s_650_, v___x_652_);
v___x_654_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_655_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_658_, lean_object* v_a_659_, lean_object* v_b_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_659_, v___x_658_);
v___x_662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_660_, v___x_658_);
v___x_663_ = lean_string_dec_lt(v___x_661_, v___x_662_);
lean_dec_ref(v___x_662_);
lean_dec_ref(v___x_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_664_, lean_object* v_a_665_, lean_object* v_b_666_){
_start:
{
uint8_t v___x_11634__boxed_667_; uint8_t v_res_668_; lean_object* v_r_669_; 
v___x_11634__boxed_667_ = lean_unbox(v___x_664_);
v_res_668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11634__boxed_667_, v_a_665_, v_b_666_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v_hi_670_, lean_object* v_pivot_671_, lean_object* v_as_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_nat_dec_lt(v_k_674_, v_hi_670_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_k_674_);
lean_dec(v_pivot_671_);
v___x_676_ = lean_array_fswap(v_as_672_, v_i_673_, v_hi_670_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_i_673_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_678_ = lean_array_fget_borrowed(v_as_672_, v_k_674_);
lean_inc(v___x_678_);
v___x_679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_678_, v___x_675_);
lean_inc(v_pivot_671_);
v___x_680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_671_, v___x_675_);
v___x_681_ = lean_string_dec_lt(v___x_679_, v___x_680_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_679_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_k_674_, v___x_682_);
lean_dec(v_k_674_);
v_k_674_ = v___x_683_;
goto _start;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_array_fswap(v_as_672_, v_i_673_, v_k_674_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_add(v_i_673_, v___x_686_);
lean_dec(v_i_673_);
v___x_688_ = lean_nat_add(v_k_674_, v___x_686_);
lean_dec(v_k_674_);
v_as_672_ = v___x_685_;
v_i_673_ = v___x_687_;
v_k_674_ = v___x_688_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v_hi_690_, lean_object* v_pivot_691_, lean_object* v_as_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_690_, v_pivot_691_, v_as_692_, v_i_693_, v_k_694_);
lean_dec(v_hi_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v_n_696_, lean_object* v_as_697_, lean_object* v_lo_698_, lean_object* v_hi_699_){
_start:
{
lean_object* v___y_701_; uint8_t v___x_711_; 
v___x_711_ = lean_nat_dec_lt(v_lo_698_, v_hi_699_);
if (v___x_711_ == 0)
{
lean_dec(v_lo_698_);
return v_as_697_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_mid_714_; lean_object* v___y_716_; lean_object* v___y_722_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_712_ = lean_nat_add(v_lo_698_, v_hi_699_);
v___x_713_ = lean_unsigned_to_nat(1u);
v_mid_714_ = lean_nat_shiftr(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
v___x_727_ = lean_array_fget_borrowed(v_as_697_, v_mid_714_);
v___x_728_ = lean_array_fget_borrowed(v_as_697_, v_lo_698_);
lean_inc(v___x_728_);
lean_inc(v___x_727_);
v___x_729_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_711_, v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
v___y_722_ = v_as_697_;
goto v___jp_721_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_array_fswap(v_as_697_, v_lo_698_, v_mid_714_);
v___y_722_ = v___x_730_;
goto v___jp_721_;
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_array_fget_borrowed(v___y_716_, v_mid_714_);
v___x_718_ = lean_array_fget_borrowed(v___y_716_, v_hi_699_);
lean_inc(v___x_718_);
lean_inc(v___x_717_);
v___x_719_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_711_, v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_dec(v_mid_714_);
v___y_701_ = v___y_716_;
goto v___jp_700_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_array_fswap(v___y_716_, v_mid_714_, v_hi_699_);
lean_dec(v_mid_714_);
v___y_701_ = v___x_720_;
goto v___jp_700_;
}
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_array_fget_borrowed(v___y_722_, v_hi_699_);
v___x_724_ = lean_array_fget_borrowed(v___y_722_, v_lo_698_);
lean_inc(v___x_724_);
lean_inc(v___x_723_);
v___x_725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_711_, v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
v___y_716_ = v___y_722_;
goto v___jp_715_;
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_array_fswap(v___y_722_, v_lo_698_, v_hi_699_);
v___y_716_ = v___x_726_;
goto v___jp_715_;
}
}
}
v___jp_700_:
{
lean_object* v_pivot_702_; lean_object* v___x_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; uint8_t v___x_706_; 
v_pivot_702_ = lean_array_fget(v___y_701_, v_hi_699_);
lean_inc_n(v_lo_698_, 2);
v___x_703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_699_, v_pivot_702_, v___y_701_, v_lo_698_, v_lo_698_);
v_fst_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_fst_704_);
v_snd_705_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_snd_705_);
lean_dec_ref(v___x_703_);
v___x_706_ = lean_nat_dec_le(v_hi_699_, v_fst_704_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_696_, v_snd_705_, v_lo_698_, v_fst_704_);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_fst_704_, v___x_708_);
lean_dec(v_fst_704_);
v_as_697_ = v___x_707_;
v_lo_698_ = v___x_709_;
goto _start;
}
else
{
lean_dec(v_fst_704_);
lean_dec(v_lo_698_);
return v_snd_705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v_n_731_, lean_object* v_as_732_, lean_object* v_lo_733_, lean_object* v_hi_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_731_, v_as_732_, v_lo_733_, v_hi_734_);
lean_dec(v_hi_734_);
lean_dec(v_n_731_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_738_, size_t v_sz_739_, size_t v_i_740_, lean_object* v_bs_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_740_, v_sz_739_);
if (v___x_742_ == 0)
{
lean_dec_ref(v___x_738_);
return v_bs_741_;
}
else
{
lean_object* v_v_743_; lean_object* v___x_744_; lean_object* v_bs_x27_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_v_743_ = lean_array_uget(v_bs_741_, v_i_740_);
v___x_744_ = lean_unsigned_to_nat(0u);
v_bs_x27_745_ = lean_array_uset(v_bs_741_, v_i_740_, v___x_744_);
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_738_);
v___x_747_ = lean_string_append(v___x_738_, v___x_746_);
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_743_, v___x_742_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
v___x_752_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_740_, v___x_754_);
v___x_756_ = lean_array_uset(v_bs_x27_745_, v_i_740_, v___x_753_);
v_i_740_ = v___x_755_;
v_bs_741_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_bs_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_758_, v_sz_boxed_762_, v_i_boxed_763_, v_bs_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_765_, size_t v_sz_766_, size_t v_i_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_a_771_; uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_767_, v_sz_766_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_768_);
return v___x_776_;
}
else
{
lean_object* v_a_777_; lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_820_; 
v_a_777_ = lean_array_uget_borrowed(v_as_765_, v_i_767_);
v_fst_778_ = lean_ctor_get(v_a_777_, 0);
v_snd_779_ = lean_ctor_get(v_a_777_, 1);
v_fst_780_ = lean_ctor_get(v_b_768_, 0);
v_snd_781_ = lean_ctor_get(v_b_768_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_b_768_);
if (v_isSharedCheck_820_ == 0)
{
v___x_783_ = v_b_768_;
v_isShared_784_ = v_isSharedCheck_820_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_b_768_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_820_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_sub(v_fst_778_, v___x_785_);
v___x_787_ = lean_array_get_size(v_fst_780_);
v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v___x_786_);
if (v_isShared_784_ == 0)
{
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_781_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_a_771_ = v___x_790_;
goto v___jp_770_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___x_809_; lean_object* v___y_811_; lean_object* v___y_812_; uint8_t v___x_814_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_array_fget_borrowed(v_fst_780_, v___x_786_);
v___x_794_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_793_);
v___x_809_ = lean_array_get_size(v_snd_779_);
v___x_814_ = lean_nat_dec_eq(v___x_809_, v___x_792_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___y_817_; uint8_t v___x_819_; 
v___x_815_ = lean_nat_sub(v___x_809_, v___x_785_);
v___x_819_ = lean_nat_dec_le(v___x_792_, v___x_815_);
if (v___x_819_ == 0)
{
lean_inc(v___x_815_);
v___y_817_ = v___x_815_;
goto v___jp_816_;
}
else
{
v___y_817_ = v___x_792_;
goto v___jp_816_;
}
v___jp_816_:
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v___y_817_, v___x_815_);
if (v___x_818_ == 0)
{
lean_dec(v___x_815_);
lean_inc(v___y_817_);
v___y_811_ = v___y_817_;
v___y_812_ = v___y_817_;
goto v___jp_810_;
}
else
{
v___y_811_ = v___y_817_;
v___y_812_ = v___x_815_;
goto v___jp_810_;
}
}
}
else
{
lean_inc(v_snd_779_);
v___y_796_ = v_snd_779_;
goto v___jp_795_;
}
v___jp_795_:
{
size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_sz_797_ = lean_array_size(v___y_796_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_794_, v_sz_797_, v___x_798_, v___y_796_);
lean_inc(v___x_786_);
v___x_800_ = l_Array_extract___redArg(v_fst_780_, v___x_792_, v___x_786_);
v___x_801_ = l_Array_append___redArg(v___x_800_, v___x_799_);
v___x_802_ = l_Array_extract___redArg(v_fst_780_, v___x_786_, v___x_787_);
lean_dec(v_fst_780_);
v___x_803_ = l_Array_append___redArg(v___x_801_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = lean_array_get_size(v___x_799_);
lean_dec_ref(v___x_799_);
v___x_805_ = lean_nat_add(v_snd_781_, v___x_804_);
lean_dec(v_snd_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_805_);
lean_ctor_set(v___x_783_, 0, v___x_803_);
v___x_807_ = v___x_783_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v_a_771_ = v___x_807_;
goto v___jp_770_;
}
}
v___jp_810_:
{
lean_object* v___x_813_; 
lean_inc(v_snd_779_);
v___x_813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_809_, v_snd_779_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
v___y_796_ = v___x_813_;
goto v___jp_795_;
}
}
}
}
v___jp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_767_, v___x_772_);
v_i_767_ = v___x_773_;
v_b_768_ = v_a_771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_821_, lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_827_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_821_, v_sz_boxed_826_, v_i_boxed_827_, v_b_824_);
lean_dec_ref(v_as_821_);
return v_res_828_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_unsigned_to_nat(16u);
v___x_831_ = lean_mk_array(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_b_848_){
_start:
{
lean_object* v_a_851_; uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_848_);
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v_snd_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_970_; 
v_a_857_ = lean_array_uget_borrowed(v_as_845_, v_i_847_);
v_snd_858_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_snd_858_);
v_fst_859_ = lean_ctor_get(v_snd_858_, 0);
v_snd_860_ = lean_ctor_get(v_snd_858_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_snd_858_);
if (v_isSharedCheck_970_ == 0)
{
v___x_862_ = v_snd_858_;
v_isShared_863_ = v_isSharedCheck_970_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_inc(v_fst_859_);
lean_dec(v_snd_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_970_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; size_t v_sz_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_866_ = lean_array_size(v_snd_860_);
v___x_867_ = ((size_t)0ULL);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_860_, v_sz_866_, v___x_867_, v___x_865_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___x_884_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = lean_box(0);
v___x_884_ = l_IO_FS_readFile(v_fst_859_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_size_889_; lean_object* v_buckets_890_; lean_object* v___x_891_; lean_object* v___x_892_; size_t v_sz_893_; lean_object* v___x_894_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_938_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
lean_dec(v_snd_860_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_n(v_a_885_, 2);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = lean_string_utf8_byte_size(v_a_885_);
v___x_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_887_, 0, v_a_885_);
lean_ctor_set(v___x_887_, 1, v___x_864_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
v___x_888_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_887_);
v_size_889_ = lean_ctor_get(v_a_869_, 0);
lean_inc(v_size_889_);
v_buckets_890_ = lean_ctor_get(v_a_869_, 1);
lean_inc_ref(v_buckets_890_);
lean_dec(v_a_869_);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_892_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_885_, v___x_887_, v___x_886_, v___x_888_, v___x_891_);
lean_dec_ref_known(v___x_887_, 3);
v_sz_893_ = lean_array_size(v___x_892_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_893_, v___x_867_, v___x_892_);
v___x_944_ = lean_mk_empty_array_with_capacity(v_size_889_);
lean_dec(v_size_889_);
v___x_945_ = lean_array_get_size(v_buckets_890_);
v___x_946_ = lean_nat_dec_lt(v___x_864_, v___x_945_);
if (v___x_946_ == 0)
{
lean_dec_ref(v_buckets_890_);
v___y_938_ = v___x_944_;
goto v___jp_937_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = lean_nat_dec_le(v___x_945_, v___x_945_);
if (v___x_947_ == 0)
{
if (v___x_946_ == 0)
{
lean_dec_ref(v_buckets_890_);
v___y_938_ = v___x_944_;
goto v___jp_937_;
}
else
{
size_t v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_usize_of_nat(v___x_945_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_890_, v___x_867_, v___x_948_, v___x_944_);
lean_dec_ref(v_buckets_890_);
v___y_938_ = v___x_949_;
goto v___jp_937_;
}
}
else
{
size_t v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_usize_of_nat(v___x_945_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_890_, v___x_867_, v___x_950_, v___x_944_);
lean_dec_ref(v_buckets_890_);
v___y_938_ = v___x_951_;
goto v___jp_937_;
}
}
v___jp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_864_);
lean_ctor_set(v___x_862_, 0, v___x_894_);
v___x_899_ = v___x_862_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_864_);
v___x_899_ = v_reuseFailAlloc_922_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
size_t v_sz_900_; lean_object* v___x_901_; 
v_sz_900_ = lean_array_size(v___y_897_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_897_, v_sz_900_, v___x_867_, v___x_899_);
lean_dec_ref(v___y_897_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_fst_903_; lean_object* v_snd_904_; uint8_t v___x_905_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v_fst_903_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_fst_903_);
v_snd_904_ = lean_ctor_get(v_a_902_, 1);
lean_inc(v_snd_904_);
lean_dec(v_a_902_);
v___x_905_ = lean_nat_dec_lt(v___x_864_, v_snd_904_);
if (v___x_905_ == 0)
{
lean_dec(v_snd_904_);
lean_dec(v_fst_903_);
lean_dec(v_fst_859_);
v_a_851_ = v___x_870_;
goto v___jp_850_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_904_);
v___x_907_ = l_Nat_reprFast(v_snd_904_);
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
lean_dec_ref(v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
v___x_911_ = lean_nat_dec_eq(v_snd_904_, v___y_896_);
lean_dec(v_snd_904_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_872_ = v_fst_903_;
v___y_873_ = v___x_910_;
v___y_874_ = v___x_912_;
goto v___jp_871_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_872_ = v_fst_903_;
v___y_873_ = v___x_910_;
v___y_874_ = v___x_913_;
goto v___jp_871_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_fst_859_);
v_a_914_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_901_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_901_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
v___jp_923_:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_924_, v___y_926_, v___y_925_, v___y_928_);
lean_dec(v___y_928_);
lean_dec(v___y_924_);
v___y_896_ = v___y_927_;
v___y_897_ = v___x_929_;
goto v___jp_895_;
}
v___jp_930_:
{
uint8_t v___x_936_; 
v___x_936_ = lean_nat_dec_le(v___y_935_, v___y_933_);
if (v___x_936_ == 0)
{
lean_dec(v___y_933_);
lean_inc(v___y_935_);
v___y_924_ = v___y_931_;
v___y_925_ = v___y_935_;
v___y_926_ = v___y_932_;
v___y_927_ = v___y_934_;
v___y_928_ = v___y_935_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_931_;
v___y_925_ = v___y_935_;
v___y_926_ = v___y_932_;
v___y_927_ = v___y_934_;
v___y_928_ = v___y_933_;
goto v___jp_923_;
}
}
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_array_get_size(v___y_938_);
v___x_941_ = lean_nat_dec_eq(v___x_940_, v___x_864_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_nat_sub(v___x_940_, v___x_939_);
v___x_943_ = lean_nat_dec_le(v___x_864_, v___x_942_);
if (v___x_943_ == 0)
{
lean_inc(v___x_942_);
v___y_931_ = v___x_940_;
v___y_932_ = v___y_938_;
v___y_933_ = v___x_942_;
v___y_934_ = v___x_939_;
v___y_935_ = v___x_942_;
goto v___jp_930_;
}
else
{
v___y_931_ = v___x_940_;
v___y_932_ = v___y_938_;
v___y_933_ = v___x_942_;
v___y_934_ = v___x_939_;
v___y_935_ = v___x_864_;
goto v___jp_930_;
}
}
else
{
v___y_896_ = v___x_939_;
v___y_897_ = v___y_938_;
goto v___jp_895_;
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref_known(v___x_884_, 1);
lean_dec(v_a_869_);
lean_del_object(v___x_862_);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_953_ = lean_string_append(v___x_952_, v_fst_859_);
lean_dec(v_fst_859_);
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
v___x_956_ = lean_array_get_size(v_snd_860_);
lean_dec(v_snd_860_);
v___x_957_ = l_Nat_reprFast(v___x_956_);
v___x_958_ = lean_string_append(v___x_955_, v___x_957_);
lean_dec_ref(v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_960_ = lean_string_append(v___x_958_, v___x_959_);
v___x_961_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_dec_ref_known(v___x_961_, 1);
v_a_851_ = v___x_870_;
goto v___jp_850_;
}
else
{
return v___x_961_;
}
}
v___jp_871_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = lean_string_append(v___y_873_, v___y_874_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_877_ = lean_string_append(v___x_875_, v___x_876_);
v___x_878_ = lean_string_append(v___x_877_, v_fst_859_);
v___x_879_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_881_ = lean_array_to_list(v___y_872_);
v___x_882_ = l_String_intercalate(v___x_880_, v___x_881_);
v___x_883_ = l_IO_FS_writeFile(v_fst_859_, v___x_882_);
lean_dec_ref(v___x_882_);
lean_dec(v_fst_859_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_dec_ref_known(v___x_883_, 1);
v_a_851_ = v___x_870_;
goto v___jp_850_;
}
else
{
return v___x_883_;
}
}
else
{
lean_dec(v___y_872_);
lean_dec(v_fst_859_);
return v___x_879_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_862_);
lean_dec(v_snd_860_);
lean_dec(v_fst_859_);
v_a_962_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_868_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_868_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
v___jp_850_:
{
size_t v___x_852_; size_t v___x_853_; 
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_847_, v___x_852_);
v_i_847_ = v___x_853_;
v_b_848_ = v_a_851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_971_, lean_object* v_sz_972_, lean_object* v_i_973_, lean_object* v_b_974_, lean_object* v___y_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_972_);
lean_dec(v_sz_972_);
v_i_boxed_977_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_971_, v_sz_boxed_976_, v_i_boxed_977_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_979_, lean_object* v_x_980_){
_start:
{
if (lean_obj_tag(v_x_980_) == 0)
{
uint8_t v___x_981_; 
v___x_981_ = 0;
return v___x_981_;
}
else
{
lean_object* v_key_982_; lean_object* v_tail_983_; uint8_t v___x_984_; 
v_key_982_ = lean_ctor_get(v_x_980_, 0);
v_tail_983_ = lean_ctor_get(v_x_980_, 2);
v___x_984_ = lean_string_dec_eq(v_key_982_, v_a_979_);
if (v___x_984_ == 0)
{
v_x_980_ = v_tail_983_;
goto _start;
}
else
{
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_a_986_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_dec(v_b_991_);
lean_dec_ref(v_a_990_);
return v_x_992_;
}
else
{
lean_object* v_key_993_; lean_object* v_value_994_; lean_object* v_tail_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1007_; 
v_key_993_ = lean_ctor_get(v_x_992_, 0);
v_value_994_ = lean_ctor_get(v_x_992_, 1);
v_tail_995_ = lean_ctor_get(v_x_992_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_997_ = v_x_992_;
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_tail_995_);
lean_inc(v_value_994_);
lean_inc(v_key_993_);
lean_dec(v_x_992_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
uint8_t v___x_999_; 
v___x_999_ = lean_string_dec_eq(v_key_993_, v_a_990_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_990_, v_b_991_, v_tail_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_key_993_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_value_994_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_value_994_);
lean_dec(v_key_993_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_b_991_);
lean_ctor_set(v___x_997_, 0, v_a_990_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_b_991_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_tail_995_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
return v_x_1008_;
}
else
{
lean_object* v_key_1010_; lean_object* v_value_1011_; lean_object* v_tail_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1035_; 
v_key_1010_ = lean_ctor_get(v_x_1009_, 0);
v_value_1011_ = lean_ctor_get(v_x_1009_, 1);
v_tail_1012_ = lean_ctor_get(v_x_1009_, 2);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1009_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1014_ = v_x_1009_;
v_isShared_1015_ = v_isSharedCheck_1035_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_tail_1012_);
lean_inc(v_value_1011_);
lean_inc(v_key_1010_);
lean_dec(v_x_1009_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1035_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; uint64_t v_fold_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1016_ = lean_array_get_size(v_x_1008_);
v___x_1017_ = lean_string_hash(v_key_1010_);
v___x_1018_ = 32ULL;
v___x_1019_ = lean_uint64_shift_right(v___x_1017_, v___x_1018_);
v_fold_1020_ = lean_uint64_xor(v___x_1017_, v___x_1019_);
v___x_1021_ = 16ULL;
v___x_1022_ = lean_uint64_shift_right(v_fold_1020_, v___x_1021_);
v___x_1023_ = lean_uint64_xor(v_fold_1020_, v___x_1022_);
v___x_1024_ = lean_uint64_to_usize(v___x_1023_);
v___x_1025_ = lean_usize_of_nat(v___x_1016_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_sub(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_usize_land(v___x_1024_, v___x_1027_);
v___x_1029_ = lean_array_uget_borrowed(v_x_1008_, v___x_1028_);
lean_inc(v___x_1029_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 2, v___x_1029_);
v___x_1031_ = v___x_1014_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_key_1010_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_value_1011_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_array_uset(v_x_1008_, v___x_1028_, v___x_1031_);
v_x_1008_ = v___x_1032_;
v_x_1009_ = v_tail_1012_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1036_, lean_object* v_source_1037_, lean_object* v_target_1038_){
_start:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_array_get_size(v_source_1037_);
v___x_1040_ = lean_nat_dec_lt(v_i_1036_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec_ref(v_source_1037_);
lean_dec(v_i_1036_);
return v_target_1038_;
}
else
{
lean_object* v_es_1041_; lean_object* v___x_1042_; lean_object* v_source_1043_; lean_object* v_target_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_es_1041_ = lean_array_fget(v_source_1037_, v_i_1036_);
v___x_1042_ = lean_box(0);
v_source_1043_ = lean_array_fset(v_source_1037_, v_i_1036_, v___x_1042_);
v_target_1044_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1038_, v_es_1041_);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_i_1036_, v___x_1045_);
lean_dec(v_i_1036_);
v_i_1036_ = v___x_1046_;
v_source_1037_ = v_source_1043_;
v_target_1038_ = v_target_1044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_nbuckets_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1049_ = lean_array_get_size(v_data_1048_);
v___x_1050_ = lean_unsigned_to_nat(2u);
v_nbuckets_1051_ = lean_nat_mul(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_mk_array(v_nbuckets_1051_, v___x_1053_);
v___x_1055_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1052_, v_data_1048_, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v_size_1059_; lean_object* v_buckets_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1103_; 
v_size_1059_ = lean_ctor_get(v_m_1056_, 0);
v_buckets_1060_ = lean_ctor_get(v_m_1056_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_m_1056_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1062_ = v_m_1056_;
v_isShared_1063_ = v_isSharedCheck_1103_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_buckets_1060_);
lean_inc(v_size_1059_);
lean_dec(v_m_1056_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1103_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; uint64_t v___x_1067_; uint64_t v_fold_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v_bkt_1077_; uint8_t v___x_1078_; 
v___x_1064_ = lean_array_get_size(v_buckets_1060_);
v___x_1065_ = lean_string_hash(v_a_1057_);
v___x_1066_ = 32ULL;
v___x_1067_ = lean_uint64_shift_right(v___x_1065_, v___x_1066_);
v_fold_1068_ = lean_uint64_xor(v___x_1065_, v___x_1067_);
v___x_1069_ = 16ULL;
v___x_1070_ = lean_uint64_shift_right(v_fold_1068_, v___x_1069_);
v___x_1071_ = lean_uint64_xor(v_fold_1068_, v___x_1070_);
v___x_1072_ = lean_uint64_to_usize(v___x_1071_);
v___x_1073_ = lean_usize_of_nat(v___x_1064_);
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_sub(v___x_1073_, v___x_1074_);
v___x_1076_ = lean_usize_land(v___x_1072_, v___x_1075_);
v_bkt_1077_ = lean_array_uget_borrowed(v_buckets_1060_, v___x_1076_);
v___x_1078_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1057_, v_bkt_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v_size_x27_1080_; lean_object* v___x_1081_; lean_object* v_buckets_x27_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1079_ = lean_unsigned_to_nat(1u);
v_size_x27_1080_ = lean_nat_add(v_size_1059_, v___x_1079_);
lean_dec(v_size_1059_);
lean_inc(v_bkt_1077_);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v_a_1057_);
lean_ctor_set(v___x_1081_, 1, v_b_1058_);
lean_ctor_set(v___x_1081_, 2, v_bkt_1077_);
v_buckets_x27_1082_ = lean_array_uset(v_buckets_1060_, v___x_1076_, v___x_1081_);
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_nat_mul(v_size_x27_1080_, v___x_1083_);
v___x_1085_ = lean_unsigned_to_nat(3u);
v___x_1086_ = lean_nat_div(v___x_1084_, v___x_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_array_get_size(v_buckets_x27_1082_);
v___x_1088_ = lean_nat_dec_le(v___x_1086_, v___x_1087_);
lean_dec(v___x_1086_);
if (v___x_1088_ == 0)
{
lean_object* v_val_1089_; lean_object* v___x_1091_; 
v_val_1089_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1082_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v_val_1089_);
lean_ctor_set(v___x_1062_, 0, v_size_x27_1080_);
v___x_1091_ = v___x_1062_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_size_x27_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_val_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v___x_1094_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v_buckets_x27_1082_);
lean_ctor_set(v___x_1062_, 0, v_size_x27_1080_);
v___x_1094_ = v___x_1062_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_size_x27_1080_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_buckets_x27_1082_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v_buckets_x27_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_inc(v_bkt_1077_);
v___x_1096_ = lean_box(0);
v_buckets_x27_1097_ = lean_array_uset(v_buckets_1060_, v___x_1076_, v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1057_, v_b_1058_, v_bkt_1077_);
v___x_1099_ = lean_array_uset(v_buckets_x27_1097_, v___x_1076_, v___x_1098_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1099_);
v___x_1101_ = v___x_1062_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_size_1059_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1104_, lean_object* v_fallback_1105_, lean_object* v_x_1106_){
_start:
{
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_inc(v_fallback_1105_);
return v_fallback_1105_;
}
else
{
lean_object* v_key_1107_; lean_object* v_value_1108_; lean_object* v_tail_1109_; uint8_t v___x_1110_; 
v_key_1107_ = lean_ctor_get(v_x_1106_, 0);
v_value_1108_ = lean_ctor_get(v_x_1106_, 1);
v_tail_1109_ = lean_ctor_get(v_x_1106_, 2);
v___x_1110_ = lean_string_dec_eq(v_key_1107_, v_a_1104_);
if (v___x_1110_ == 0)
{
v_x_1106_ = v_tail_1109_;
goto _start;
}
else
{
lean_inc(v_value_1108_);
return v_value_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1112_, lean_object* v_fallback_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1112_, v_fallback_1113_, v_x_1114_);
lean_dec(v_x_1114_);
lean_dec(v_fallback_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1116_, lean_object* v_a_1117_, lean_object* v_fallback_1118_){
_start:
{
lean_object* v_buckets_1119_; lean_object* v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v_fold_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_buckets_1119_ = lean_ctor_get(v_m_1116_, 1);
v___x_1120_ = lean_array_get_size(v_buckets_1119_);
v___x_1121_ = lean_string_hash(v_a_1117_);
v___x_1122_ = 32ULL;
v___x_1123_ = lean_uint64_shift_right(v___x_1121_, v___x_1122_);
v_fold_1124_ = lean_uint64_xor(v___x_1121_, v___x_1123_);
v___x_1125_ = 16ULL;
v___x_1126_ = lean_uint64_shift_right(v_fold_1124_, v___x_1125_);
v___x_1127_ = lean_uint64_xor(v_fold_1124_, v___x_1126_);
v___x_1128_ = lean_uint64_to_usize(v___x_1127_);
v___x_1129_ = lean_usize_of_nat(v___x_1120_);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_sub(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_usize_land(v___x_1128_, v___x_1131_);
v___x_1133_ = lean_array_uget_borrowed(v_buckets_1119_, v___x_1132_);
v___x_1134_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1117_, v_fallback_1118_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1135_, lean_object* v_a_1136_, lean_object* v_fallback_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1135_, v_a_1136_, v_fallback_1137_);
lean_dec(v_fallback_1137_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_m_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_b_1144_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_b_1144_);
return v___x_1147_;
}
else
{
lean_object* v_a_1148_; lean_object* v_file_1149_; lean_object* v_pos_1150_; lean_object* v_option_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1177_; 
v_a_1148_ = lean_array_uget_borrowed(v_as_1141_, v_i_1143_);
v_file_1149_ = lean_ctor_get(v_a_1148_, 0);
v_pos_1150_ = lean_ctor_get(v_a_1148_, 1);
lean_inc_ref(v_pos_1150_);
v_option_1151_ = lean_ctor_get(v_a_1148_, 2);
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1149_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_file_1149_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1144_, v_file_1149_, v___x_1153_);
lean_dec_ref_known(v___x_1153_, 2);
v_fst_1155_ = lean_ctor_get(v___x_1154_, 0);
v_snd_1156_ = lean_ctor_get(v___x_1154_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1158_ = v___x_1154_;
v_isShared_1159_ = v_isSharedCheck_1177_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v___x_1154_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1177_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_line_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1175_; 
v_line_1160_ = lean_ctor_get(v_pos_1150_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_pos_1150_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_pos_1150_, 1);
lean_dec(v_unused_1176_);
v___x_1162_ = v_pos_1150_;
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_line_1160_);
lean_dec(v_pos_1150_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
lean_inc(v_option_1151_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v_option_1151_);
lean_ctor_set(v___x_1158_, 0, v_line_1160_);
v___x_1165_ = v___x_1158_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_line_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_option_1151_);
v___x_1165_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_array_push(v_snd_1156_, v___x_1165_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1166_);
lean_ctor_set(v___x_1162_, 0, v_fst_1155_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1155_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; 
lean_inc_ref(v_file_1149_);
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1144_, v_file_1149_, v___x_1168_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1143_, v___x_1170_);
v_i_1143_ = v___x_1171_;
v_b_1144_ = v___x_1169_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1178_, lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_){
_start:
{
size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1178_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1181_);
lean_dec_ref(v_as_1178_);
return v_res_1185_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_unsigned_to_nat(16u);
v___x_1188_ = lean_mk_array(v___x_1187_, v___x_1186_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_byFile_1191_; 
v___x_1189_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1190_ = lean_unsigned_to_nat(0u);
v_byFile_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1191_, 0, v___x_1190_);
lean_ctor_set(v_byFile_1191_, 1, v___x_1189_);
return v_byFile_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v_byFile_1195_; size_t v_sz_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v_byFile_1195_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1196_ = lean_array_size(v_records_1192_);
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1192_, v_sz_1196_, v___x_1197_, v_byFile_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___y_1201_; lean_object* v_size_1213_; lean_object* v_buckets_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v_size_1213_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_size_1213_);
v_buckets_1214_ = lean_ctor_get(v_a_1199_, 1);
lean_inc_ref(v_buckets_1214_);
lean_dec(v_a_1199_);
v___x_1215_ = lean_mk_empty_array_with_capacity(v_size_1213_);
lean_dec(v_size_1213_);
v___x_1216_ = lean_array_get_size(v_buckets_1214_);
v___x_1217_ = lean_nat_dec_lt(v___x_1194_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v_buckets_1214_);
v___y_1201_ = v___x_1215_;
goto v___jp_1200_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
if (v___x_1218_ == 0)
{
if (v___x_1217_ == 0)
{
lean_dec_ref(v_buckets_1214_);
v___y_1201_ = v___x_1215_;
goto v___jp_1200_;
}
else
{
size_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_usize_of_nat(v___x_1216_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1214_, v___x_1197_, v___x_1219_, v___x_1215_);
lean_dec_ref(v_buckets_1214_);
v___y_1201_ = v___x_1220_;
goto v___jp_1200_;
}
}
else
{
size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_usize_of_nat(v___x_1216_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1214_, v___x_1197_, v___x_1221_, v___x_1215_);
lean_dec_ref(v_buckets_1214_);
v___y_1201_ = v___x_1222_;
goto v___jp_1200_;
}
}
v___jp_1200_:
{
lean_object* v___x_1202_; size_t v_sz_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_box(0);
v_sz_1203_ = lean_array_size(v___y_1201_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1201_, v_sz_1203_, v___x_1197_, v___x_1202_);
lean_dec_ref(v___y_1201_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v___x_1204_, 0);
lean_dec(v_unused_1212_);
v___x_1206_ = v___x_1204_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_dec(v___x_1204_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1202_);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1202_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1198_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1198_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1231_);
lean_dec_ref(v_records_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1234_, lean_object* v_m_1235_, lean_object* v_a_1236_, lean_object* v_fallback_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1235_, v_a_1236_, v_fallback_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_, lean_object* v_fallback_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1239_, v_m_1240_, v_a_1241_, v_fallback_1242_);
lean_dec(v_fallback_1242_);
lean_dec_ref(v_a_1241_);
lean_dec_ref(v_m_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_b_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1245_, v_a_1246_, v_b_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_, lean_object* v_fallback_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1250_, v_a_1251_, v_fallback_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1254_, lean_object* v_m_1255_, lean_object* v_a_1256_, lean_object* v_fallback_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1254_, v_m_1255_, v_a_1256_, v_fallback_1257_);
lean_dec(v_fallback_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_m_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1260_, v_a_1261_, v_b_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v_inst_1267_, lean_object* v_R_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1264_, v___x_1265_, v___x_1266_, v_a_1269_, v_b_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v_inst_1275_, lean_object* v_R_1276_, lean_object* v_a_1277_, lean_object* v_b_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1272_, v___x_1273_, v___x_1274_, v_inst_1275_, v_R_1276_, v_a_1277_, v_b_1278_);
lean_dec_ref(v___x_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v_n_1280_, lean_object* v_as_1281_, lean_object* v_lo_1282_, lean_object* v_hi_1283_, lean_object* v_w_1284_, lean_object* v_hlo_1285_, lean_object* v_hhi_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_1280_, v_as_1281_, v_lo_1282_, v_hi_1283_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v_n_1288_, lean_object* v_as_1289_, lean_object* v_lo_1290_, lean_object* v_hi_1291_, lean_object* v_w_1292_, lean_object* v_hlo_1293_, lean_object* v_hhi_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v_n_1288_, v_as_1289_, v_lo_1290_, v_hi_1291_, v_w_1292_, v_hlo_1293_, v_hhi_1294_);
lean_dec(v_hi_1291_);
lean_dec(v_n_1288_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1296_, lean_object* v_as_1297_, lean_object* v_lo_1298_, lean_object* v_hi_1299_, lean_object* v_w_1300_, lean_object* v_hlo_1301_, lean_object* v_hhi_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1296_, v_as_1297_, v_lo_1298_, v_hi_1299_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1304_, lean_object* v_as_1305_, lean_object* v_lo_1306_, lean_object* v_hi_1307_, lean_object* v_w_1308_, lean_object* v_hlo_1309_, lean_object* v_hhi_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1304_, v_as_1305_, v_lo_1306_, v_hi_1307_, v_w_1308_, v_hlo_1309_, v_hhi_1310_);
lean_dec(v_hi_1307_);
lean_dec(v_n_1304_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1312_, lean_object* v_a_1313_, lean_object* v_fallback_1314_, lean_object* v_x_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1313_, v_fallback_1314_, v_x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1317_, lean_object* v_a_1318_, lean_object* v_fallback_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1317_, v_a_1318_, v_fallback_1319_, v_x_1320_);
lean_dec(v_x_1320_);
lean_dec(v_fallback_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1322_, lean_object* v_a_1323_, lean_object* v_x_1324_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1323_, v_x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_a_1327_, lean_object* v_x_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1326_, v_a_1327_, v_x_1328_);
lean_dec(v_x_1328_);
lean_dec_ref(v_a_1327_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1331_, lean_object* v_data_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1335_, v_b_1336_, v_x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1339_, lean_object* v_a_1340_, lean_object* v_fallback_1341_, lean_object* v_x_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1340_, v_fallback_1341_, v_x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_a_1345_, lean_object* v_fallback_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1344_, v_a_1345_, v_fallback_1346_, v_x_1347_);
lean_dec(v_x_1347_);
lean_dec(v_fallback_1346_);
lean_dec(v_a_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1349_, lean_object* v_a_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1350_, v_x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1353_, lean_object* v_a_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v_res_1356_; lean_object* v_r_1357_; 
v_res_1356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1353_, v_a_1354_, v_x_1355_);
lean_dec(v_x_1355_);
lean_dec(v_a_1354_);
v_r_1357_ = lean_box(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1358_, lean_object* v_data_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1361_, lean_object* v_a_1362_, lean_object* v_b_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1362_, v_b_1363_, v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v_n_1366_, lean_object* v_lo_1367_, lean_object* v_hi_1368_, lean_object* v_hhi_1369_, lean_object* v_pivot_1370_, lean_object* v_as_1371_, lean_object* v_i_1372_, lean_object* v_k_1373_, lean_object* v_ilo_1374_, lean_object* v_ik_1375_, lean_object* v_w_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_1368_, v_pivot_1370_, v_as_1371_, v_i_1372_, v_k_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v_n_1378_, lean_object* v_lo_1379_, lean_object* v_hi_1380_, lean_object* v_hhi_1381_, lean_object* v_pivot_1382_, lean_object* v_as_1383_, lean_object* v_i_1384_, lean_object* v_k_1385_, lean_object* v_ilo_1386_, lean_object* v_ik_1387_, lean_object* v_w_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v_n_1378_, v_lo_1379_, v_hi_1380_, v_hhi_1381_, v_pivot_1382_, v_as_1383_, v_i_1384_, v_k_1385_, v_ilo_1386_, v_ik_1387_, v_w_1388_);
lean_dec(v_hi_1380_);
lean_dec(v_lo_1379_);
lean_dec(v_n_1378_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1390_, lean_object* v_lo_1391_, lean_object* v_hi_1392_, lean_object* v_hhi_1393_, lean_object* v_pivot_1394_, lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_k_1397_, lean_object* v_ilo_1398_, lean_object* v_ik_1399_, lean_object* v_w_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1392_, v_pivot_1394_, v_as_1395_, v_i_1396_, v_k_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1402_, lean_object* v_lo_1403_, lean_object* v_hi_1404_, lean_object* v_hhi_1405_, lean_object* v_pivot_1406_, lean_object* v_as_1407_, lean_object* v_i_1408_, lean_object* v_k_1409_, lean_object* v_ilo_1410_, lean_object* v_ik_1411_, lean_object* v_w_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1402_, v_lo_1403_, v_hi_1404_, v_hhi_1405_, v_pivot_1406_, v_as_1407_, v_i_1408_, v_k_1409_, v_ilo_1410_, v_ik_1411_, v_w_1412_);
lean_dec_ref(v_pivot_1406_);
lean_dec(v_hi_1404_);
lean_dec(v_lo_1403_);
lean_dec(v_n_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1414_, lean_object* v_i_1415_, lean_object* v_source_1416_, lean_object* v_target_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1415_, v_source_1416_, v_target_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1419_, lean_object* v_i_1420_, lean_object* v_source_1421_, lean_object* v_target_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1420_, v_source_1421_, v_target_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1425_, v_x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1429_, v_x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v_env_1436_; lean_object* v___x_1437_; lean_object* v_env_1438_; lean_object* v___x_1439_; lean_object* v_toEnvExtension_1440_; lean_object* v_asyncMode_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1435_ = lean_st_ref_get(v___y_1433_);
v_env_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_ref(v_env_1436_);
lean_dec(v___x_1435_);
v___x_1437_ = lean_st_ref_get(v___y_1433_);
v_env_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_env_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = l_Lean_declRangeExt;
v_toEnvExtension_1440_ = lean_ctor_get(v___x_1439_, 0);
v_asyncMode_1441_ = lean_ctor_get(v_toEnvExtension_1440_, 2);
v___x_1442_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1443_ = 0;
lean_inc(v_declName_1432_);
v___x_1444_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1442_, v___x_1439_, v_env_1436_, v_declName_1432_, v_asyncMode_1441_, v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = 1;
v___x_1446_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1442_, v___x_1439_, v_env_1438_, v_declName_1432_, v_asyncMode_1441_, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; 
lean_dec_ref(v_env_1438_);
lean_dec(v_declName_1432_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1444_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1449_, v___y_1450_);
lean_dec(v___y_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v_env_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = lean_st_ref_get(v___y_1454_);
v_env_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_isRecCore(v_env_1457_, v_declName_1453_);
v___x_1459_ = lean_box(v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1461_, v___y_1462_);
lean_dec(v___y_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_ranges_1470_; lean_object* v___x_1476_; lean_object* v_env_1477_; lean_object* v___x_1478_; lean_object* v_a_1479_; uint8_t v___y_1485_; uint8_t v___x_1489_; 
v___x_1476_ = lean_st_ref_get(v___y_1467_);
v_env_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref_n(v_env_1477_, 2);
lean_dec(v___x_1476_);
lean_inc_n(v_declName_1465_, 2);
v___x_1478_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1465_, v___y_1467_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___x_1489_ = l_Lean_isAuxRecursor(v_env_1477_, v_declName_1465_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
lean_inc(v_declName_1465_);
v___x_1490_ = l_Lean_isNoConfusion(v_env_1477_, v_declName_1465_);
v___y_1485_ = v___x_1490_;
goto v___jp_1484_;
}
else
{
lean_dec_ref(v_env_1477_);
v___y_1485_ = v___x_1489_;
goto v___jp_1484_;
}
v___jp_1469_:
{
if (lean_obj_tag(v_ranges_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = l_Lean_builtinDeclRanges;
v___x_1472_ = lean_st_ref_get(v___x_1471_);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1472_, v_declName_1465_);
lean_dec(v_declName_1465_);
lean_dec(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_declName_1465_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_ranges_1470_);
return v___x_1475_;
}
}
v___jp_1480_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_a_1483_; 
v___x_1481_ = l_Lean_Name_getPrefix(v_declName_1465_);
v___x_1482_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1481_, v___y_1467_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
v_ranges_1470_ = v_a_1483_;
goto v___jp_1469_;
}
v___jp_1484_:
{
if (v___y_1485_ == 0)
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_unbox(v_a_1479_);
lean_dec(v_a_1479_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v_a_1488_; 
lean_inc(v_declName_1465_);
v___x_1487_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1465_, v___y_1467_);
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v_ranges_1470_ = v_a_1488_;
goto v___jp_1469_;
}
else
{
goto v___jp_1480_;
}
}
else
{
lean_dec(v_a_1479_);
goto v___jp_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1496_, lean_object* v_site_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
if (lean_obj_tag(v_site_1497_) == 0)
{
lean_object* v_name_1501_; lean_object* v___x_1502_; 
v_name_1501_ = lean_ctor_get(v_site_1497_, 0);
lean_inc(v_name_1501_);
lean_dec_ref_known(v_site_1497_, 1);
v___x_1502_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1501_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1524_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1524_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1524_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
if (lean_obj_tag(v_a_1503_) == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_box(0);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
else
{
lean_object* v_val_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1523_; 
v_val_1511_ = lean_ctor_get(v_a_1503_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1513_ = v_a_1503_;
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_val_1511_);
lean_dec(v_a_1503_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1523_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_range_1515_; lean_object* v_pos_1516_; lean_object* v___x_1518_; 
v_range_1515_ = lean_ctor_get(v_val_1511_, 0);
lean_inc_ref(v_range_1515_);
lean_dec(v_val_1511_);
v_pos_1516_ = lean_ctor_get(v_range_1515_, 0);
lean_inc_ref(v_pos_1516_);
lean_dec_ref(v_range_1515_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v_pos_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_pos_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1518_);
v___x_1520_ = v___x_1505_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1502_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1502_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_n_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1564_; 
v_n_1533_ = lean_ctor_get(v_site_1497_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_site_1497_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1535_ = v_site_1497_;
v_isShared_1536_ = v_isSharedCheck_1564_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_n_1533_);
lean_dec(v_site_1497_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1564_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v_env_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_st_ref_get(v_a_1499_);
v_env_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_ref(v_env_1538_);
lean_dec(v___x_1537_);
v___x_1539_ = l_Lean_getVersoModuleDoc_x3f(v_env_1538_, v_failMod_1496_);
lean_dec_ref(v_env_1538_);
if (lean_obj_tag(v___x_1539_) == 1)
{
lean_object* v_val_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1559_; 
v_val_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1559_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_val_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1559_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_array_get_size(v_val_1540_);
v___x_1545_ = lean_nat_dec_lt(v_n_1533_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_del_object(v___x_1542_);
lean_dec(v_val_1540_);
lean_dec(v_n_1533_);
v___x_1546_ = lean_box(0);
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1546_);
v___x_1548_ = v___x_1535_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
else
{
lean_object* v___x_1550_; lean_object* v_declarationRange_1551_; lean_object* v_pos_1552_; lean_object* v___x_1554_; 
v___x_1550_ = lean_array_fget(v_val_1540_, v_n_1533_);
lean_dec(v_n_1533_);
lean_dec(v_val_1540_);
v_declarationRange_1551_ = lean_ctor_get(v___x_1550_, 2);
lean_inc_ref(v_declarationRange_1551_);
lean_dec(v___x_1550_);
v_pos_1552_ = lean_ctor_get(v_declarationRange_1551_, 0);
lean_inc_ref(v_pos_1552_);
lean_dec_ref(v_declarationRange_1551_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_pos_1552_);
v___x_1554_ = v___x_1542_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_pos_1552_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1554_);
v___x_1556_ = v___x_1535_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v___x_1539_);
lean_dec(v_n_1533_);
v___x_1560_ = lean_box(0);
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1560_);
v___x_1562_ = v___x_1535_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1565_, lean_object* v_site_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1565_, v_site_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_failMod_1565_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1571_, v___y_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1581_, v___y_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
lean_object* v_name_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_name_1595_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_name_1595_);
lean_dec_ref_known(v_x_1594_, 1);
v___x_1596_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1597_ = 1;
v___x_1598_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1595_, v___x_1597_);
v___x_1599_ = lean_string_append(v___x_1596_, v___x_1598_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v_n_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_n_1602_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_n_1602_);
lean_dec_ref_known(v_x_1594_, 1);
v___x_1603_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_n_1602_, v___x_1604_);
lean_dec(v_n_1602_);
v___x_1606_ = l_Nat_reprFast(v___x_1605_);
v___x_1607_ = lean_string_append(v___x_1603_, v___x_1606_);
lean_dec_ref(v___x_1606_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___boxed(lean_object* v_x_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(v_x_1611_);
lean_dec_ref(v_x_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_1613_, lean_object* v_k_1614_){
_start:
{
if (lean_obj_tag(v_t_1613_) == 0)
{
uint8_t v_failed_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_failed_1615_ = lean_ctor_get_uint8(v_t_1613_, 0);
lean_dec_ref_known(v_t_1613_, 0);
v___x_1616_ = lean_box(v_failed_1615_);
v___x_1617_ = lean_apply_1(v_k_1614_, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v_records_1618_; uint8_t v_unlocated_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_records_1618_ = lean_ctor_get(v_t_1613_, 0);
lean_inc_ref(v_records_1618_);
v_unlocated_1619_ = lean_ctor_get_uint8(v_t_1613_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1613_, 1);
v___x_1620_ = lean_box(v_unlocated_1619_);
v___x_1621_ = lean_apply_2(v_k_1614_, v_records_1618_, v___x_1620_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_1622_, lean_object* v_ctorIdx_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_k_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1624_, v_k_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_1628_, lean_object* v_ctorIdx_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_k_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_1628_, v_ctorIdx_1629_, v_t_1630_, v_h_1631_, v_k_1632_);
lean_dec(v_ctorIdx_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_1634_, lean_object* v_reported_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1634_, v_reported_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_reported_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1638_, v_reported_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_1642_, lean_object* v_recorded_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1642_, v_recorded_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_1645_, lean_object* v_t_1646_, lean_object* v_h_1647_, lean_object* v_recorded_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1646_, v_recorded_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_env_1654_; lean_object* v___x_1655_; lean_object* v_toEnvExtension_1656_; lean_object* v_asyncMode_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_merged_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v___x_1653_ = lean_st_ref_get(v___y_1651_);
v_env_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref(v_env_1654_);
lean_dec(v___x_1653_);
v___x_1655_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1656_ = lean_ctor_get(v___x_1655_, 0);
v_asyncMode_1657_ = lean_ctor_get(v_toEnvExtension_1656_, 2);
v___x_1658_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1659_ = lean_box(0);
v___x_1660_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1658_, v___x_1655_, v_env_1654_, v_asyncMode_1657_, v___x_1659_);
v_merged_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v___x_1660_, 1);
lean_dec(v_unused_1670_);
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_merged_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v_merged_1661_);
lean_ctor_set(v___x_1663_, 0, v_o_1650_);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_o_1650_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_merged_1661_);
v___x_1666_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1671_, v___y_1672_);
lean_dec(v___y_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1675_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1685_, lean_object* v_opt_1686_){
_start:
{
lean_object* v_name_1687_; lean_object* v_defValue_1688_; lean_object* v_map_1689_; lean_object* v___x_1690_; 
v_name_1687_ = lean_ctor_get(v_opt_1686_, 0);
v_defValue_1688_ = lean_ctor_get(v_opt_1686_, 1);
v_map_1689_ = lean_ctor_get(v_opts_1685_, 0);
v___x_1690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1689_, v_name_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_unbox(v_defValue_1688_);
return v___x_1691_;
}
else
{
lean_object* v_val_1692_; 
v_val_1692_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1690_, 1);
if (lean_obj_tag(v_val_1692_) == 1)
{
uint8_t v_v_1693_; 
v_v_1693_ = lean_ctor_get_uint8(v_val_1692_, 0);
lean_dec_ref_known(v_val_1692_, 0);
return v_v_1693_;
}
else
{
uint8_t v___x_1694_; 
lean_dec(v_val_1692_);
v___x_1694_ = lean_unbox(v_defValue_1688_);
return v___x_1694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1695_, lean_object* v_opt_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1695_, v_opt_1696_);
lean_dec_ref(v_opt_1696_);
lean_dec_ref(v_opts_1695_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1699_, lean_object* v_opt_1700_){
_start:
{
lean_object* v_name_1701_; lean_object* v_defValue_1702_; lean_object* v_map_1703_; lean_object* v___x_1704_; 
v_name_1701_ = lean_ctor_get(v_opt_1700_, 0);
v_defValue_1702_ = lean_ctor_get(v_opt_1700_, 1);
v_map_1703_ = lean_ctor_get(v_opts_1699_, 0);
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1703_, v_name_1701_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_inc(v_defValue_1702_);
return v_defValue_1702_;
}
else
{
lean_object* v_val_1705_; 
v_val_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___x_1704_, 1);
if (lean_obj_tag(v_val_1705_) == 3)
{
lean_object* v_v_1706_; 
v_v_1706_ = lean_ctor_get(v_val_1705_, 0);
lean_inc(v_v_1706_);
lean_dec_ref_known(v_val_1705_, 1);
return v_v_1706_;
}
else
{
lean_dec(v_val_1705_);
lean_inc(v_defValue_1702_);
return v_defValue_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1707_, lean_object* v_opt_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1707_, v_opt_1708_);
lean_dec_ref(v_opt_1708_);
lean_dec_ref(v_opts_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_options_1714_; lean_object* v___x_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1726_; 
v_options_1714_ = lean_ctor_get(v_c_1710_, 6);
lean_inc_ref(v_options_1714_);
lean_dec_ref(v_c_1710_);
v___x_1715_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1714_, v___y_1712_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1726_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1720_ = l_linter_doc_deferred;
v___x_1721_ = l_Lean_Linter_getLinterValue(v___x_1720_, v_a_1716_);
lean_dec(v_a_1716_);
v___x_1722_ = lean_box(v___x_1721_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1722_);
v___x_1724_ = v___x_1718_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1732_, lean_object* v_docCheckedModules_1733_, lean_object* v_m_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1732_, v_m_1734_);
if (v___x_1735_ == 0)
{
return v___x_1735_;
}
else
{
uint8_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = l_Lean_NameSet_contains(v_docCheckedModules_1733_, v_m_1734_);
v___x_1737_ = lean_bool_not(v___x_1736_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1738_, lean_object* v_docCheckedModules_1739_, lean_object* v_m_1740_){
_start:
{
uint8_t v_res_1741_; lean_object* v_r_1742_; 
v_res_1741_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1738_, v_docCheckedModules_1739_, v_m_1740_);
lean_dec(v_m_1740_);
lean_dec(v_docCheckedModules_1739_);
lean_dec(v_pkgRoot_1738_);
v_r_1742_ = lean_box(v_res_1741_);
return v_r_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_1750_, lean_object* v_sp_1751_, lean_object* v_as_1752_, size_t v_sz_1753_, size_t v_i_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_a_1760_; uint8_t v_unlocated_1764_; 
v_unlocated_1764_ = lean_usize_dec_lt(v_i_1754_, v_sz_1753_);
if (v_unlocated_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec(v_sp_1751_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_b_1755_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; lean_object* v_snd_1767_; lean_object* v_fst_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1897_; 
v_a_1766_ = lean_array_uget_borrowed(v_as_1752_, v_i_1754_);
v_snd_1767_ = lean_ctor_get(v_a_1766_, 1);
lean_inc(v_snd_1767_);
v_fst_1768_ = lean_ctor_get(v_snd_1767_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_snd_1767_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_snd_1767_, 1);
lean_dec(v_unused_1898_);
v___x_1770_ = v_snd_1767_;
v_isShared_1771_ = v_isSharedCheck_1897_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_fst_1768_);
lean_dec(v_snd_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1897_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_fst_1772_; lean_object* v_site_1773_; lean_object* v___x_1774_; 
v_fst_1772_ = lean_ctor_get(v_a_1766_, 0);
v_site_1773_ = lean_ctor_get(v_fst_1768_, 0);
lean_inc_ref_n(v_site_1773_, 2);
lean_dec(v_fst_1768_);
v___x_1774_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_1772_, v_site_1773_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
if (lean_obj_tag(v_a_1775_) == 0)
{
lean_object* v_fst_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1815_; 
v_fst_1776_ = lean_ctor_get(v_b_1755_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_b_1755_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_b_1755_, 1);
lean_dec(v_unused_1816_);
v___x_1778_ = v_b_1755_;
v_isShared_1779_ = v_isSharedCheck_1815_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_fst_1776_);
lean_dec(v_b_1755_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1815_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v_name_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1780_ = l_linter_doc_deferred;
v_name_1781_ = lean_ctor_get(v___x_1780_, 0);
v___x_1782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_1783_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1773_);
v___x_1784_ = lean_string_append(v___x_1782_, v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
lean_inc(v_fst_1772_);
v___x_1787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1772_, v___x_1750_);
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
lean_inc(v_name_1781_);
v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1781_, v___x_1750_);
v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
v___x_1795_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec_ref_known(v___x_1795_, 1);
lean_del_object(v___x_1770_);
v___x_1796_ = lean_box(v_unlocated_1764_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v___x_1796_);
v___x_1798_ = v___x_1778_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_fst_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v_a_1760_ = v___x_1798_;
goto v___jp_1759_;
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1814_; 
lean_del_object(v___x_1778_);
lean_dec(v_fst_1776_);
lean_dec(v_sp_1751_);
v_a_1800_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1802_ = v___x_1795_;
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1795_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v_ref_1804_ = lean_ctor_get(v___y_1756_, 5);
v___x_1805_ = lean_io_error_to_string(v_a_1800_);
v___x_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = l_Lean_MessageData_ofFormat(v___x_1806_);
lean_inc(v_ref_1804_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v___x_1807_);
lean_ctor_set(v___x_1770_, 0, v_ref_1804_);
v___x_1809_ = v___x_1770_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_ref_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1809_);
v___x_1811_ = v___x_1802_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1817_; lean_object* v_snd_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_site_1773_);
v_fst_1817_ = lean_ctor_get(v_b_1755_, 0);
v_snd_1818_ = lean_ctor_get(v_b_1755_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_b_1755_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1820_ = v_b_1755_;
v_isShared_1821_ = v_isSharedCheck_1888_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snd_1818_);
lean_inc(v_fst_1817_);
lean_dec(v_b_1755_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1888_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1887_; 
v_val_1822_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1824_ = v_a_1775_;
v_isShared_1825_ = v_isSharedCheck_1887_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v_a_1775_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1887_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1772_);
lean_inc(v_sp_1751_);
v___x_1827_ = l_Lean_SearchPath_findWithExt(v_sp_1751_, v___x_1826_, v_fst_1772_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
if (lean_obj_tag(v_a_1828_) == 0)
{
lean_object* v___x_1829_; lean_object* v_name_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_val_1822_);
lean_dec(v_snd_1818_);
v___x_1829_ = l_linter_doc_deferred;
v_name_1830_ = lean_ctor_get(v___x_1829_, 0);
v___x_1831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_1772_);
v___x_1832_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1772_, v___x_1750_);
v___x_1833_ = lean_string_append(v___x_1831_, v___x_1832_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_1835_ = lean_string_append(v___x_1833_, v___x_1834_);
lean_inc(v_name_1830_);
v___x_1836_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1830_, v___x_1750_);
v___x_1837_ = lean_string_append(v___x_1835_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1839_ = lean_string_append(v___x_1837_, v___x_1838_);
v___x_1840_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec_ref_known(v___x_1840_, 1);
lean_del_object(v___x_1824_);
lean_del_object(v___x_1770_);
v___x_1841_ = lean_box(v_unlocated_1764_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1841_);
v___x_1843_ = v___x_1820_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_fst_1817_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v_a_1760_ = v___x_1843_;
goto v___jp_1759_;
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1820_);
lean_dec(v_fst_1817_);
lean_dec(v_sp_1751_);
v_a_1845_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1847_ = v___x_1840_;
v_isShared_1848_ = v_isSharedCheck_1861_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1840_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1861_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_ref_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v_ref_1849_ = lean_ctor_get(v___y_1756_, 5);
v___x_1850_ = lean_io_error_to_string(v_a_1845_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 3);
lean_ctor_set(v___x_1824_, 0, v___x_1850_);
v___x_1852_ = v___x_1824_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = l_Lean_MessageData_ofFormat(v___x_1852_);
lean_inc(v_ref_1849_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v___x_1853_);
lean_ctor_set(v___x_1770_, 0, v_ref_1849_);
v___x_1855_ = v___x_1770_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_ref_1849_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1855_);
v___x_1857_ = v___x_1847_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1863_; lean_object* v_name_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_del_object(v___x_1824_);
lean_del_object(v___x_1770_);
v_val_1862_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_a_1828_, 1);
v___x_1863_ = l_linter_doc_deferred;
v_name_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_name_1864_);
v___x_1865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1865_, 0, v_val_1862_);
lean_ctor_set(v___x_1865_, 1, v_val_1822_);
lean_ctor_set(v___x_1865_, 2, v_name_1864_);
v___x_1866_ = lean_array_push(v_fst_1817_, v___x_1865_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1866_);
v___x_1868_ = v___x_1820_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_snd_1818_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
v_a_1760_ = v___x_1868_;
goto v___jp_1759_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_val_1822_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_fst_1817_);
lean_dec(v_sp_1751_);
v_a_1870_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1872_ = v___x_1827_;
v_isShared_1873_ = v_isSharedCheck_1886_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1827_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1886_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_ref_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v_ref_1874_ = lean_ctor_get(v___y_1756_, 5);
v___x_1875_ = lean_io_error_to_string(v_a_1870_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 3);
lean_ctor_set(v___x_1824_, 0, v___x_1875_);
v___x_1877_ = v___x_1824_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_MessageData_ofFormat(v___x_1877_);
lean_inc(v_ref_1874_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v___x_1878_);
lean_ctor_set(v___x_1770_, 0, v_ref_1874_);
v___x_1880_ = v___x_1770_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_ref_1874_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1880_);
v___x_1882_ = v___x_1872_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
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
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_site_1773_);
lean_del_object(v___x_1770_);
lean_dec_ref(v_b_1755_);
lean_dec(v_sp_1751_);
v_a_1889_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1774_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1774_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
v___jp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1754_, v___x_1761_);
v_i_1754_ = v___x_1762_;
v_b_1755_ = v_a_1760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_1899_, lean_object* v_sp_1900_, lean_object* v_as_1901_, lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v___x_8894__boxed_1908_; size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v___x_8894__boxed_1908_ = lean_unbox(v___x_1899_);
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_8894__boxed_1908_, v_sp_1900_, v_as_1901_, v_sz_boxed_1909_, v_i_boxed_1910_, v_b_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v_as_1901_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_1918_, uint8_t v___y_1919_, lean_object* v_as_1920_, size_t v_sz_1921_, size_t v_i_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_a_1927_; uint8_t v___x_1931_; 
v___x_1931_ = lean_usize_dec_lt(v_i_1922_, v_sz_1921_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec(v_sp_1918_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_b_1923_);
return v___x_1932_;
}
else
{
lean_object* v_a_1933_; lean_object* v_snd_1934_; lean_object* v_fst_1935_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2032_; 
v_a_1933_ = lean_array_uget_borrowed(v_as_1920_, v_i_1922_);
v_snd_1934_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1934_);
v_fst_1935_ = lean_ctor_get(v_snd_1934_, 0);
lean_inc(v_fst_1935_);
v_fst_1936_ = lean_ctor_get(v_a_1933_, 0);
v_snd_1937_ = lean_ctor_get(v_snd_1934_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_snd_1934_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_snd_1934_, 0);
lean_dec(v_unused_2033_);
v___x_1939_ = v_snd_1934_;
v_isShared_1940_ = v_isSharedCheck_2032_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snd_1937_);
lean_dec(v_snd_1934_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2032_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_site_1941_; lean_object* v_sourceString_1942_; lean_object* v___x_1943_; lean_object* v___y_1945_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v_site_1941_ = lean_ctor_get(v_fst_1935_, 0);
lean_inc_ref(v_site_1941_);
v_sourceString_1942_ = lean_ctor_get(v_fst_1935_, 2);
lean_inc_ref(v_sourceString_1942_);
lean_dec(v_fst_1935_);
v___x_1943_ = lean_box(0);
v___x_2024_ = lean_string_utf8_byte_size(v_sourceString_1942_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_nat_dec_eq(v___x_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2028_ = lean_string_append(v___x_2027_, v_sourceString_1942_);
lean_dec_ref(v_sourceString_1942_);
v___x_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2030_ = lean_string_append(v___x_2028_, v___x_2029_);
v___y_1945_ = v___x_2030_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref(v_sourceString_1942_);
v___x_2031_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1945_ = v___x_2031_;
goto v___jp_1944_;
}
v___jp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1936_);
lean_inc(v_sp_1918_);
v___x_1947_ = l_Lean_SearchPath_findWithExt(v_sp_1918_, v___x_1946_, v_fst_1936_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
if (lean_obj_tag(v_a_1948_) == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1949_ = l_Lean_MessageData_toString(v_snd_1937_);
v___x_1950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_1936_);
v___x_1951_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1936_, v___y_1919_);
v___x_1952_ = lean_string_append(v___x_1950_, v___x_1951_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_1954_ = lean_string_append(v___x_1952_, v___x_1953_);
v___x_1955_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1941_);
v___x_1956_ = lean_string_append(v___x_1954_, v___x_1955_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = lean_string_append(v___x_1956_, v___y_1945_);
lean_dec_ref(v___y_1945_);
v___x_1958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_1959_ = lean_string_append(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_string_append(v___x_1959_, v___x_1949_);
lean_dec_ref(v___x_1949_);
v___x_1961_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
lean_del_object(v___x_1939_);
v_a_1927_ = v___x_1943_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_sp_1918_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1976_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1976_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_ref_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v_ref_1966_ = lean_ctor_get(v___y_1924_, 5);
v___x_1967_ = lean_io_error_to_string(v_a_1962_);
v___x_1968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
v___x_1969_ = l_Lean_MessageData_ofFormat(v___x_1968_);
lean_inc(v_ref_1966_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___x_1969_);
lean_ctor_set(v___x_1939_, 0, v_ref_1966_);
v___x_1971_ = v___x_1939_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_ref_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1971_);
v___x_1973_ = v___x_1964_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_val_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2008_; 
v_val_1977_ = lean_ctor_get(v_a_1948_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1979_ = v_a_1948_;
v_isShared_1980_ = v_isSharedCheck_2008_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_val_1977_);
lean_dec(v_a_1948_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2008_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1981_ = l_Lean_MessageData_toString(v_snd_1937_);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_1983_ = lean_string_append(v_val_1977_, v___x_1982_);
v___x_1984_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1941_);
v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_string_append(v___x_1985_, v___y_1945_);
lean_dec_ref(v___y_1945_);
v___x_1987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_1988_ = lean_string_append(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_string_append(v___x_1988_, v___x_1981_);
lean_dec_ref(v___x_1981_);
v___x_1990_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_dec_ref_known(v___x_1990_, 1);
lean_del_object(v___x_1979_);
lean_del_object(v___x_1939_);
v_a_1927_ = v___x_1943_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_sp_1918_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2007_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2007_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_ref_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v_ref_1995_ = lean_ctor_get(v___y_1924_, 5);
v___x_1996_ = lean_io_error_to_string(v_a_1991_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 3);
lean_ctor_set(v___x_1979_, 0, v___x_1996_);
v___x_1998_ = v___x_1979_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = l_Lean_MessageData_ofFormat(v___x_1998_);
lean_inc(v_ref_1995_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___x_1999_);
lean_ctor_set(v___x_1939_, 0, v_ref_1995_);
v___x_2001_ = v___x_1939_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_ref_1995_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2001_);
v___x_2003_ = v___x_1993_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
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
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_site_1941_);
lean_dec(v_snd_1937_);
lean_dec(v_sp_1918_);
v_a_2009_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2011_ = v___x_1947_;
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1947_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2023_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_ref_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v_ref_2013_ = lean_ctor_get(v___y_1924_, 5);
v___x_2014_ = lean_io_error_to_string(v_a_2009_);
v___x_2015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
v___x_2016_ = l_Lean_MessageData_ofFormat(v___x_2015_);
lean_inc(v_ref_2013_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___x_2016_);
lean_ctor_set(v___x_1939_, 0, v_ref_2013_);
v___x_2018_ = v___x_1939_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_ref_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2018_);
v___x_2020_ = v___x_2011_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
}
v___jp_1926_:
{
size_t v___x_1928_; size_t v___x_1929_; 
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_add(v_i_1922_, v___x_1928_);
v_i_1922_ = v___x_1929_;
v_b_1923_ = v_a_1927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2034_, lean_object* v___y_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v___y_9186__boxed_2042_; size_t v_sz_boxed_2043_; size_t v_i_boxed_2044_; lean_object* v_res_2045_; 
v___y_9186__boxed_2042_ = lean_unbox(v___y_2035_);
v_sz_boxed_2043_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2044_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2034_, v___y_9186__boxed_2042_, v_as_2036_, v_sz_boxed_2043_, v_i_boxed_2044_, v_b_2039_, v___y_2040_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_as_2036_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2046_, lean_object* v_as_2047_, size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_b_2050_){
_start:
{
lean_object* v_a_2053_; uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2050_);
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; uint8_t v___x_2060_; 
v_a_2059_ = lean_array_uget_borrowed(v_as_2047_, v_i_2049_);
v___x_2060_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2046_, v_a_2059_);
if (v___x_2060_ == 0)
{
v_a_2053_ = v_b_2050_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2061_; 
lean_inc(v_a_2059_);
v___x_2061_ = l_Lean_NameSet_insert(v_b_2050_, v_a_2059_);
v_a_2053_ = v___x_2061_;
goto v___jp_2052_;
}
}
v___jp_2052_:
{
size_t v___x_2054_; size_t v___x_2055_; 
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2049_, v___x_2054_);
v_i_2049_ = v___x_2055_;
v_b_2050_ = v_a_2053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2062_, lean_object* v_as_2063_, lean_object* v_sz_2064_, lean_object* v_i_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2064_);
lean_dec(v_sz_2064_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2062_, v_as_2063_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2066_);
lean_dec_ref(v_as_2063_);
lean_dec(v_pkgRoot_2062_);
return v_res_2070_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_unsigned_to_nat(32u);
v___x_2078_ = lean_mk_empty_array_with_capacity(v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2080_ = ((size_t)5ULL);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = lean_unsigned_to_nat(32u);
v___x_2083_ = lean_mk_empty_array_with_capacity(v___x_2082_);
v___x_2084_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2085_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v___x_2081_);
lean_ctor_set(v___x_2085_, 3, v___x_2081_);
lean_ctor_set_usize(v___x_2085_, 4, v___x_2080_);
return v___x_2085_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2086_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = l_Lean_NameSet_empty;
v___x_2092_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_ctor_set(v___x_2093_, 2, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = l_Lean_firstFrontendMacroScope;
v___x_2096_ = lean_nat_add(v___x_2095_, v___x_2094_);
return v___x_2096_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2107_; uint64_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2108_ = 0ULL;
v___x_2109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set_uint64(v___x_2109_, sizeof(void*)*1, v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v_unlocated_2112_; lean_object* v___x_2113_; 
v___x_2110_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2111_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2112_ = 1;
v___x_2113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2111_);
lean_ctor_set(v___x_2113_, 2, v___x_2110_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*3, v_unlocated_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = l_Lean_Options_empty;
v___x_2117_ = l_Lean_Core_getMaxHeartbeats(v___x_2116_);
return v___x_2117_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2118_ = l_Lean_diagnostics;
v___x_2119_ = l_Lean_Options_empty;
v___x_2120_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2119_, v___x_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2121_, lean_object* v_linterOpts_2122_, lean_object* v_sp_2123_, lean_object* v_env_2124_, lean_object* v_pkgRoot_2125_, lean_object* v_docCheckedModules_2126_){
_start:
{
lean_object* v___y_2129_; lean_object* v_a_2133_; uint8_t v___y_2137_; lean_object* v_a_2138_; lean_object* v___y_2155_; lean_object* v_a_2156_; uint8_t v_lintOnly_2180_; uint8_t v_recordExceptions_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; uint8_t v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2244_; lean_object* v___y_2245_; uint8_t v___y_2246_; lean_object* v___y_2247_; uint8_t v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; uint8_t v___y_2251_; uint8_t v___y_2252_; uint8_t v___y_2274_; 
v_lintOnly_2180_ = lean_ctor_get_uint8(v_args_2121_, sizeof(void*)*3);
v_recordExceptions_2181_ = lean_ctor_get_uint8(v_args_2121_, sizeof(void*)*3 + 1);
v___f_2182_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
lean_inc(v_docCheckedModules_2126_);
lean_inc(v_pkgRoot_2125_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2183_, 0, v_pkgRoot_2125_);
lean_closure_set(v___f_2183_, 1, v_docCheckedModules_2126_);
if (v_lintOnly_2180_ == 0)
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = l_linter_doc_deferred;
v___x_2309_ = l_Lean_Linter_getLinterValue(v___x_2308_, v_linterOpts_2122_);
v___y_2274_ = v___x_2309_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2310_; lean_object* v_name_2311_; uint8_t v___x_2312_; 
v___x_2310_ = l_linter_doc_deferred;
v_name_2311_ = lean_ctor_get(v___x_2310_, 0);
v___x_2312_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2311_, v_linterOpts_2122_);
v___y_2274_ = v___x_2312_;
goto v___jp_2273_;
}
v___jp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___y_2129_);
lean_ctor_set(v___x_2130_, 1, v_docCheckedModules_2126_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_mk_io_user_error(v_a_2133_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
v___jp_2136_:
{
if (lean_obj_tag(v_a_2138_) == 0)
{
lean_object* v_msg_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_msg_2139_ = lean_ctor_get(v_a_2138_, 1);
lean_inc_ref(v_msg_2139_);
lean_dec_ref_known(v_a_2138_, 2);
v___x_2140_ = l_Lean_MessageData_toString(v_msg_2139_);
v___x_2141_ = lean_mk_io_user_error(v___x_2140_);
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
else
{
lean_object* v_id_2143_; lean_object* v___x_2144_; 
v_id_2143_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_id_2143_);
lean_dec_ref_known(v_a_2138_, 2);
v___x_2144_ = l_Lean_InternalExceptionId_getName(v_id_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_id_2143_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2147_ = l_Lean_Name_toString(v_a_2145_, v___y_2137_);
v___x_2148_ = lean_string_append(v___x_2146_, v___x_2147_);
lean_dec_ref(v___x_2147_);
v_a_2133_ = v___x_2148_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref_known(v___x_2144_, 1);
v___x_2149_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2150_ = l_Nat_reprFast(v_id_2143_);
v___x_2151_ = lean_string_append(v___x_2149_, v___x_2150_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v_a_2133_ = v___x_2153_;
goto v___jp_2132_;
}
}
}
v___jp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; size_t v_sz_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2157_ = lean_st_ref_get(v___y_2155_);
lean_dec(v___y_2155_);
lean_dec(v___x_2157_);
v___x_2158_ = l_Lean_Environment_header(v_env_2124_);
lean_dec_ref(v_env_2124_);
v___x_2159_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2158_);
v_sz_2160_ = lean_array_size(v___x_2159_);
v___x_2161_ = ((size_t)0ULL);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2125_, v___x_2159_, v_sz_2160_, v___x_2161_, v_docCheckedModules_2126_);
lean_dec_ref(v___x_2159_);
lean_dec(v_pkgRoot_2125_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2156_);
lean_ctor_set(v___x_2167_, 1, v_a_2163_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2167_);
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_a_2156_);
v_a_2172_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
v___jp_2184_:
{
lean_object* v_fileName_2194_; lean_object* v_fileMap_2195_; lean_object* v_currRecDepth_2196_; lean_object* v_ref_2197_; lean_object* v_currNamespace_2198_; lean_object* v_openDecls_2199_; lean_object* v_initHeartbeats_2200_; lean_object* v_maxHeartbeats_2201_; lean_object* v_quotContext_2202_; lean_object* v_currMacroScope_2203_; lean_object* v_cancelTk_x3f_2204_; uint8_t v_suppressElabErrors_2205_; lean_object* v_inheritedTraceOptions_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2240_; 
v_fileName_2194_ = lean_ctor_get(v___y_2192_, 0);
v_fileMap_2195_ = lean_ctor_get(v___y_2192_, 1);
v_currRecDepth_2196_ = lean_ctor_get(v___y_2192_, 3);
v_ref_2197_ = lean_ctor_get(v___y_2192_, 5);
v_currNamespace_2198_ = lean_ctor_get(v___y_2192_, 6);
v_openDecls_2199_ = lean_ctor_get(v___y_2192_, 7);
v_initHeartbeats_2200_ = lean_ctor_get(v___y_2192_, 8);
v_maxHeartbeats_2201_ = lean_ctor_get(v___y_2192_, 9);
v_quotContext_2202_ = lean_ctor_get(v___y_2192_, 10);
v_currMacroScope_2203_ = lean_ctor_get(v___y_2192_, 11);
v_cancelTk_x3f_2204_ = lean_ctor_get(v___y_2192_, 12);
v_suppressElabErrors_2205_ = lean_ctor_get_uint8(v___y_2192_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2206_ = lean_ctor_get(v___y_2192_, 13);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___y_2192_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2241_ = lean_ctor_get(v___y_2192_, 4);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v___y_2192_, 2);
lean_dec(v_unused_2242_);
v___x_2208_ = v___y_2192_;
v_isShared_2209_ = v_isSharedCheck_2240_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_inheritedTraceOptions_2206_);
lean_inc(v_cancelTk_x3f_2204_);
lean_inc(v_currMacroScope_2203_);
lean_inc(v_quotContext_2202_);
lean_inc(v_maxHeartbeats_2201_);
lean_inc(v_initHeartbeats_2200_);
lean_inc(v_openDecls_2199_);
lean_inc(v_currNamespace_2198_);
lean_inc(v_ref_2197_);
lean_inc(v_currRecDepth_2196_);
lean_inc(v_fileMap_2195_);
lean_inc(v_fileName_2194_);
lean_dec(v___y_2192_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2240_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = l_Lean_maxRecDepth;
v___x_2211_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2187_, v___x_2210_);
lean_inc_ref(v___y_2187_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 4, v___x_2211_);
lean_ctor_set(v___x_2208_, 2, v___y_2187_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_fileName_2194_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_fileMap_2195_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___y_2187_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_currRecDepth_2196_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2239_, 5, v_ref_2197_);
lean_ctor_set(v_reuseFailAlloc_2239_, 6, v_currNamespace_2198_);
lean_ctor_set(v_reuseFailAlloc_2239_, 7, v_openDecls_2199_);
lean_ctor_set(v_reuseFailAlloc_2239_, 8, v_initHeartbeats_2200_);
lean_ctor_set(v_reuseFailAlloc_2239_, 9, v_maxHeartbeats_2201_);
lean_ctor_set(v_reuseFailAlloc_2239_, 10, v_quotContext_2202_);
lean_ctor_set(v_reuseFailAlloc_2239_, 11, v_currMacroScope_2203_);
lean_ctor_set(v_reuseFailAlloc_2239_, 12, v_cancelTk_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2239_, 13, v_inheritedTraceOptions_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2239_, sizeof(void*)*14 + 1, v_suppressElabErrors_2205_);
v___x_2213_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; 
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*14, v___y_2189_);
lean_inc_ref(v___y_2186_);
v___x_2214_ = l_Lean_Doc_DeferredCheck_run(v___f_2183_, v___y_2186_, v___x_2213_, v___y_2193_);
if (lean_obj_tag(v___x_2214_) == 0)
{
if (v_recordExceptions_2181_ == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v___y_2193_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_box(0);
v_sz_2217_ = lean_array_size(v_a_2215_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2123_, v___y_2188_, v_a_2215_, v_sz_2217_, v___x_2218_, v___x_2216_, v___x_2213_);
lean_dec_ref(v___x_2213_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2220_; uint8_t v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref_known(v___x_2219_, 1);
v___x_2220_ = lean_array_get_size(v_a_2215_);
lean_dec(v_a_2215_);
v___x_2221_ = lean_nat_dec_eq(v___x_2220_, v___y_2185_);
v___x_2222_ = lean_bool_not(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2223_, 0, v___x_2222_);
v___y_2155_ = v___y_2190_;
v_a_2156_ = v___x_2223_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2224_; 
lean_dec(v_a_2215_);
lean_dec(v___y_2190_);
lean_dec(v_docCheckedModules_2126_);
lean_dec(v_pkgRoot_2125_);
lean_dec_ref(v_env_2124_);
v_a_2224_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2219_, 1);
v___y_2137_ = v___y_2188_;
v_a_2138_ = v_a_2224_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v_a_2225_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___y_2185_);
v___x_2227_ = lean_box(v___y_2191_);
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v_sz_2229_ = lean_array_size(v_a_2225_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v_recordExceptions_2181_, v_sp_2123_, v_a_2225_, v_sz_2229_, v___x_2230_, v___x_2228_, v___x_2213_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___x_2213_);
lean_dec(v_a_2225_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v_fst_2233_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_fst_2233_);
v_snd_2234_ = lean_ctor_get(v_a_2232_, 1);
lean_inc(v_snd_2234_);
lean_dec(v_a_2232_);
v___x_2235_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2235_, 0, v_fst_2233_);
v___x_2236_ = lean_unbox(v_snd_2234_);
lean_dec(v_snd_2234_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1, v___x_2236_);
v___y_2155_ = v___y_2190_;
v_a_2156_ = v___x_2235_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2237_; 
lean_dec(v___y_2190_);
lean_dec(v_docCheckedModules_2126_);
lean_dec(v_pkgRoot_2125_);
lean_dec_ref(v_env_2124_);
v_a_2237_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2231_, 1);
v___y_2137_ = v___y_2188_;
v_a_2138_ = v_a_2237_;
goto v___jp_2136_;
}
}
}
else
{
lean_object* v_a_2238_; 
lean_dec_ref(v___x_2213_);
lean_dec(v___y_2193_);
lean_dec(v___y_2190_);
lean_dec(v_docCheckedModules_2126_);
lean_dec(v_pkgRoot_2125_);
lean_dec_ref(v_env_2124_);
lean_dec(v_sp_2123_);
v_a_2238_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2214_, 1);
v___y_2137_ = v___y_2188_;
v_a_2138_ = v_a_2238_;
goto v___jp_2136_;
}
}
}
}
v___jp_2243_:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_bool_not(v___y_2252_);
if (v___x_2253_ == 0)
{
lean_inc(v___y_2249_);
v___y_2185_ = v___y_2244_;
v___y_2186_ = v___f_2182_;
v___y_2187_ = v___y_2245_;
v___y_2188_ = v___y_2246_;
v___y_2189_ = v___y_2248_;
v___y_2190_ = v___y_2249_;
v___y_2191_ = v___y_2251_;
v___y_2192_ = v___y_2247_;
v___y_2193_ = v___y_2249_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2254_; lean_object* v_env_2255_; lean_object* v_nextMacroScope_2256_; lean_object* v_ngen_2257_; lean_object* v_auxDeclNGen_2258_; lean_object* v_traceState_2259_; lean_object* v_messages_2260_; lean_object* v_infoState_2261_; lean_object* v_snapshotTasks_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2271_; 
v___x_2254_ = lean_st_ref_take(v___y_2249_);
v_env_2255_ = lean_ctor_get(v___x_2254_, 0);
v_nextMacroScope_2256_ = lean_ctor_get(v___x_2254_, 1);
v_ngen_2257_ = lean_ctor_get(v___x_2254_, 2);
v_auxDeclNGen_2258_ = lean_ctor_get(v___x_2254_, 3);
v_traceState_2259_ = lean_ctor_get(v___x_2254_, 4);
v_messages_2260_ = lean_ctor_get(v___x_2254_, 6);
v_infoState_2261_ = lean_ctor_get(v___x_2254_, 7);
v_snapshotTasks_2262_ = lean_ctor_get(v___x_2254_, 8);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v___x_2254_, 5);
lean_dec(v_unused_2272_);
v___x_2264_ = v___x_2254_;
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snapshotTasks_2262_);
lean_inc(v_infoState_2261_);
lean_inc(v_messages_2260_);
lean_inc(v_traceState_2259_);
lean_inc(v_auxDeclNGen_2258_);
lean_inc(v_ngen_2257_);
lean_inc(v_nextMacroScope_2256_);
lean_inc(v_env_2255_);
lean_dec(v___x_2254_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = l_Lean_Kernel_enableDiag(v_env_2255_, v___y_2248_);
lean_inc_ref(v___y_2250_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 5, v___y_2250_);
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_nextMacroScope_2256_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_ngen_2257_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_auxDeclNGen_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_traceState_2259_);
lean_ctor_set(v_reuseFailAlloc_2270_, 5, v___y_2250_);
lean_ctor_set(v_reuseFailAlloc_2270_, 6, v_messages_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 7, v_infoState_2261_);
lean_ctor_set(v_reuseFailAlloc_2270_, 8, v_snapshotTasks_2262_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_st_ref_set(v___y_2249_, v___x_2268_);
lean_inc(v___y_2249_);
v___y_2185_ = v___y_2244_;
v___y_2186_ = v___f_2182_;
v___y_2187_ = v___y_2245_;
v___y_2188_ = v___y_2246_;
v___y_2189_ = v___y_2248_;
v___y_2190_ = v___y_2249_;
v___y_2191_ = v___y_2251_;
v___y_2192_ = v___y_2247_;
v___y_2193_ = v___y_2249_;
goto v___jp_2184_;
}
}
}
}
v___jp_2273_:
{
if (v___y_2274_ == 0)
{
lean_dec_ref(v___f_2183_);
lean_dec(v_pkgRoot_2125_);
lean_dec_ref(v_env_2124_);
lean_dec(v_sp_2123_);
if (v_recordExceptions_2181_ == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2275_, 0, v___y_2274_);
v___y_2129_ = v___x_2275_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2277_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*1, v___y_2274_);
v___y_2129_ = v___x_2277_;
goto v___jp_2128_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_env_2305_; uint8_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2280_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2281_ = lean_io_get_num_heartbeats();
v___x_2282_ = l_Lean_firstFrontendMacroScope;
v___x_2283_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2284_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_box(0);
v___x_2287_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2288_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2289_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2290_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2124_);
v___x_2291_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2291_, 0, v_env_2124_);
lean_ctor_set(v___x_2291_, 1, v___x_2283_);
lean_ctor_set(v___x_2291_, 2, v___x_2284_);
lean_ctor_set(v___x_2291_, 3, v___x_2287_);
lean_ctor_set(v___x_2291_, 4, v___x_2288_);
lean_ctor_set(v___x_2291_, 5, v___x_2279_);
lean_ctor_set(v___x_2291_, 6, v___x_2280_);
lean_ctor_set(v___x_2291_, 7, v___x_2289_);
lean_ctor_set(v___x_2291_, 8, v___x_2290_);
v___x_2292_ = lean_st_mk_ref(v___x_2291_);
v___x_2293_ = l_Lean_inheritedTraceOptions;
v___x_2294_ = lean_st_ref_get(v___x_2293_);
v___x_2295_ = lean_st_ref_get(v___x_2292_);
v___x_2296_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2297_ = l_Lean_instInhabitedFileMap_default;
v___x_2298_ = l_Lean_Options_empty;
v___x_2299_ = lean_unsigned_to_nat(1000u);
v___x_2300_ = lean_box(0);
v___x_2301_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2302_ = 0;
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2304_, 0, v___x_2296_);
lean_ctor_set(v___x_2304_, 1, v___x_2297_);
lean_ctor_set(v___x_2304_, 2, v___x_2298_);
lean_ctor_set(v___x_2304_, 3, v___x_2278_);
lean_ctor_set(v___x_2304_, 4, v___x_2299_);
lean_ctor_set(v___x_2304_, 5, v___x_2300_);
lean_ctor_set(v___x_2304_, 6, v___x_2285_);
lean_ctor_set(v___x_2304_, 7, v___x_2286_);
lean_ctor_set(v___x_2304_, 8, v___x_2281_);
lean_ctor_set(v___x_2304_, 9, v___x_2301_);
lean_ctor_set(v___x_2304_, 10, v___x_2285_);
lean_ctor_set(v___x_2304_, 11, v___x_2282_);
lean_ctor_set(v___x_2304_, 12, v___x_2303_);
lean_ctor_set(v___x_2304_, 13, v___x_2294_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*14, v___x_2302_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*14 + 1, v___x_2302_);
v_env_2305_ = lean_ctor_get(v___x_2295_, 0);
lean_inc_ref(v_env_2305_);
lean_dec(v___x_2295_);
v___x_2306_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2307_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2305_);
lean_dec_ref(v_env_2305_);
if (v___x_2307_ == 0)
{
if (v___x_2306_ == 0)
{
v___y_2244_ = v___x_2278_;
v___y_2245_ = v___x_2298_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___x_2304_;
v___y_2248_ = v___x_2306_;
v___y_2249_ = v___x_2292_;
v___y_2250_ = v___x_2279_;
v___y_2251_ = v___x_2302_;
v___y_2252_ = v___y_2274_;
goto v___jp_2243_;
}
else
{
v___y_2244_ = v___x_2278_;
v___y_2245_ = v___x_2298_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___x_2304_;
v___y_2248_ = v___x_2306_;
v___y_2249_ = v___x_2292_;
v___y_2250_ = v___x_2279_;
v___y_2251_ = v___x_2302_;
v___y_2252_ = v___x_2307_;
goto v___jp_2243_;
}
}
else
{
v___y_2244_ = v___x_2278_;
v___y_2245_ = v___x_2298_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___x_2304_;
v___y_2248_ = v___x_2306_;
v___y_2249_ = v___x_2292_;
v___y_2250_ = v___x_2279_;
v___y_2251_ = v___x_2302_;
v___y_2252_ = v___x_2306_;
goto v___jp_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2313_, lean_object* v_linterOpts_2314_, lean_object* v_sp_2315_, lean_object* v_env_2316_, lean_object* v_pkgRoot_2317_, lean_object* v_docCheckedModules_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2313_, v_linterOpts_2314_, v_sp_2315_, v_env_2316_, v_pkgRoot_2317_, v_docCheckedModules_2318_);
lean_dec_ref(v_linterOpts_2314_);
lean_dec_ref(v_args_2313_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2321_, uint8_t v___y_2322_, lean_object* v_as_2323_, size_t v_sz_2324_, size_t v_i_2325_, lean_object* v_b_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2321_, v___y_2322_, v_as_2323_, v_sz_2324_, v_i_2325_, v_b_2326_, v___y_2327_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2331_, lean_object* v___y_2332_, lean_object* v_as_2333_, lean_object* v_sz_2334_, lean_object* v_i_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v___y_9901__boxed_2340_; size_t v_sz_boxed_2341_; size_t v_i_boxed_2342_; lean_object* v_res_2343_; 
v___y_9901__boxed_2340_ = lean_unbox(v___y_2332_);
v_sz_boxed_2341_ = lean_unbox_usize(v_sz_2334_);
lean_dec(v_sz_2334_);
v_i_boxed_2342_ = lean_unbox_usize(v_i_2335_);
lean_dec(v_i_2335_);
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2331_, v___y_9901__boxed_2340_, v_as_2333_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_as_2333_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_enable_initializer_execution();
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_compacted_region_free(v_region_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_2357_, lean_object* v_k_2358_, uint8_t v_v_2359_){
_start:
{
lean_object* v_map_2360_; uint8_t v_hasTrace_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2375_; 
v_map_2360_ = lean_ctor_get(v_o_2357_, 0);
v_hasTrace_2361_ = lean_ctor_get_uint8(v_o_2357_, sizeof(void*)*1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_o_2357_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2363_ = v_o_2357_;
v_isShared_2364_ = v_isSharedCheck_2375_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_map_2360_);
lean_dec(v_o_2357_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2375_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2365_, 0, v_v_2359_);
lean_inc(v_k_2358_);
v___x_2366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2358_, v___x_2365_, v_map_2360_);
if (v_hasTrace_2361_ == 0)
{
lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2370_; 
v___x_2367_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_2368_ = l_Lean_Name_isPrefixOf(v___x_2367_, v_k_2358_);
lean_dec(v_k_2358_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2366_);
v___x_2370_ = v___x_2363_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2366_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_ctor_set_uint8(v___x_2370_, sizeof(void*)*1, v___x_2368_);
return v___x_2370_;
}
}
else
{
lean_object* v___x_2373_; 
lean_dec(v_k_2358_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2366_);
v___x_2373_ = v___x_2363_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2366_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*1, v_hasTrace_2361_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_2376_, lean_object* v_k_2377_, lean_object* v_v_2378_){
_start:
{
uint8_t v_v_boxed_2379_; lean_object* v_res_2380_; 
v_v_boxed_2379_ = lean_unbox(v_v_2378_);
v_res_2380_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_2376_, v_k_2377_, v_v_boxed_2379_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(uint8_t v___x_2384_, lean_object* v_fst_2385_, lean_object* v_as_2386_, size_t v_sz_2387_, size_t v_i_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v_a_2392_; uint8_t v_anyUnlocated_2396_; 
v_anyUnlocated_2396_ = lean_usize_dec_lt(v_i_2388_, v_sz_2387_);
if (v_anyUnlocated_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec(v_fst_2385_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_b_2389_);
return v___x_2397_;
}
else
{
lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2436_; 
v_fst_2398_ = lean_ctor_get(v_b_2389_, 0);
v_snd_2399_ = lean_ctor_get(v_b_2389_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_b_2389_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2401_ = v_b_2389_;
v_isShared_2402_ = v_isSharedCheck_2436_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_snd_2399_);
lean_inc(v_fst_2398_);
lean_dec(v_b_2389_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2436_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v_a_2403_; lean_object* v_position_x3f_2404_; 
v_a_2403_ = lean_array_uget_borrowed(v_as_2386_, v_i_2388_);
v_position_x3f_2404_ = lean_ctor_get(v_a_2403_, 2);
if (lean_obj_tag(v_position_x3f_2404_) == 0)
{
lean_object* v_linter_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec(v_snd_2399_);
v_linter_2405_ = lean_ctor_get(v_a_2403_, 0);
v___x_2406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__0));
lean_inc(v_linter_2405_);
v___x_2407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2405_, v___x_2384_);
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__1));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
lean_inc(v_fst_2385_);
v___x_2411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2385_, v___x_2384_);
v___x_2412_ = lean_string_append(v___x_2410_, v___x_2411_);
lean_dec_ref(v___x_2411_);
v___x_2413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__2));
v___x_2414_ = lean_string_append(v___x_2412_, v___x_2413_);
v___x_2415_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
lean_dec_ref_known(v___x_2415_, 1);
v___x_2416_ = lean_box(v_anyUnlocated_2396_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v___x_2416_);
v___x_2418_ = v___x_2401_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_fst_2398_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
v_a_2392_ = v___x_2418_;
goto v___jp_2391_;
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_del_object(v___x_2401_);
lean_dec(v_fst_2398_);
lean_dec(v_fst_2385_);
v_a_2420_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2415_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2415_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_linter_2428_; lean_object* v_file_2429_; lean_object* v_val_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v_linter_2428_ = lean_ctor_get(v_a_2403_, 0);
v_file_2429_ = lean_ctor_get(v_a_2403_, 3);
v_val_2430_ = lean_ctor_get(v_position_x3f_2404_, 0);
lean_inc(v_linter_2428_);
lean_inc(v_val_2430_);
lean_inc_ref(v_file_2429_);
v___x_2431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2431_, 0, v_file_2429_);
lean_ctor_set(v___x_2431_, 1, v_val_2430_);
lean_ctor_set(v___x_2431_, 2, v_linter_2428_);
v___x_2432_ = lean_array_push(v_fst_2398_, v___x_2431_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2432_);
v___x_2434_ = v___x_2401_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_snd_2399_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
v_a_2392_ = v___x_2434_;
goto v___jp_2391_;
}
}
}
}
v___jp_2391_:
{
size_t v___x_2393_; size_t v___x_2394_; 
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2388_, v___x_2393_);
v_i_2388_ = v___x_2394_;
v_b_2389_ = v_a_2392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object* v___x_2437_, lean_object* v_fst_2438_, lean_object* v_as_2439_, lean_object* v_sz_2440_, lean_object* v_i_2441_, lean_object* v_b_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_31329__boxed_2444_; size_t v_sz_boxed_2445_; size_t v_i_boxed_2446_; lean_object* v_res_2447_; 
v___x_31329__boxed_2444_ = lean_unbox(v___x_2437_);
v_sz_boxed_2445_ = lean_unbox_usize(v_sz_2440_);
lean_dec(v_sz_2440_);
v_i_boxed_2446_ = lean_unbox_usize(v_i_2441_);
lean_dec(v_i_2441_);
v_res_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(v___x_31329__boxed_2444_, v_fst_2438_, v_as_2439_, v_sz_boxed_2445_, v_i_boxed_2446_, v_b_2442_);
lean_dec_ref(v_as_2439_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(uint8_t v___x_2448_, lean_object* v_as_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_b_2452_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2451_, v_sz_2450_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_b_2452_);
return v___x_2455_;
}
else
{
lean_object* v_a_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2483_; 
v_a_2456_ = lean_array_uget_borrowed(v_as_2449_, v_i_2451_);
v_fst_2457_ = lean_ctor_get(v_a_2456_, 0);
v_snd_2458_ = lean_ctor_get(v_a_2456_, 1);
v_fst_2459_ = lean_ctor_get(v_b_2452_, 0);
v_snd_2460_ = lean_ctor_get(v_b_2452_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_b_2452_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2462_ = v_b_2452_;
v_isShared_2463_ = v_isSharedCheck_2483_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_inc(v_fst_2459_);
lean_dec(v_b_2452_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2483_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_fst_2459_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_snd_2460_);
v___x_2465_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
size_t v_sz_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v_sz_2466_ = lean_array_size(v_snd_2458_);
v___x_2467_ = ((size_t)0ULL);
lean_inc(v_fst_2457_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(v___x_2448_, v_fst_2457_, v_snd_2458_, v_sz_2466_, v___x_2467_, v___x_2465_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v_fst_2470_; lean_object* v_snd_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2481_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v_fst_2470_ = lean_ctor_get(v_a_2469_, 0);
v_snd_2471_ = lean_ctor_get(v_a_2469_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2473_ = v_a_2469_;
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_snd_2471_);
lean_inc(v_fst_2470_);
lean_dec(v_a_2469_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_fst_2470_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_snd_2471_);
v___x_2476_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
size_t v___x_2477_; size_t v___x_2478_; 
v___x_2477_ = ((size_t)1ULL);
v___x_2478_ = lean_usize_add(v_i_2451_, v___x_2477_);
v_i_2451_ = v___x_2478_;
v_b_2452_ = v___x_2476_;
goto _start;
}
}
}
else
{
return v___x_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object* v___x_2484_, lean_object* v_as_2485_, lean_object* v_sz_2486_, lean_object* v_i_2487_, lean_object* v_b_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v___x_31418__boxed_2490_; size_t v_sz_boxed_2491_; size_t v_i_boxed_2492_; lean_object* v_res_2493_; 
v___x_31418__boxed_2490_ = lean_unbox(v___x_2484_);
v_sz_boxed_2491_ = lean_unbox_usize(v_sz_2486_);
lean_dec(v_sz_2486_);
v_i_boxed_2492_ = lean_unbox_usize(v_i_2487_);
lean_dec(v_i_2487_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_31418__boxed_2490_, v_as_2485_, v_sz_boxed_2491_, v_i_boxed_2492_, v_b_2488_);
lean_dec_ref(v_as_2485_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_2494_, lean_object* v_as_2495_, size_t v_i_2496_, size_t v_stop_2497_, lean_object* v_b_2498_){
_start:
{
lean_object* v___y_2500_; uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_eq(v_i_2496_, v_stop_2497_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v_linter_2506_; uint8_t v___x_2507_; 
v___x_2505_ = lean_array_uget_borrowed(v_as_2495_, v_i_2496_);
v_linter_2506_ = lean_ctor_get(v___x_2505_, 0);
v___x_2507_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2506_, v___x_2494_);
if (v___x_2507_ == 0)
{
v___y_2500_ = v_b_2498_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2508_; 
lean_inc(v___x_2505_);
v___x_2508_ = lean_array_push(v_b_2498_, v___x_2505_);
v___y_2500_ = v___x_2508_;
goto v___jp_2499_;
}
}
else
{
return v_b_2498_;
}
v___jp_2499_:
{
size_t v___x_2501_; size_t v___x_2502_; 
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_add(v_i_2496_, v___x_2501_);
v_i_2496_ = v___x_2502_;
v_b_2498_ = v___y_2500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_2509_, lean_object* v_as_2510_, lean_object* v_i_2511_, lean_object* v_stop_2512_, lean_object* v_b_2513_){
_start:
{
size_t v_i_boxed_2514_; size_t v_stop_boxed_2515_; lean_object* v_res_2516_; 
v_i_boxed_2514_ = lean_unbox_usize(v_i_2511_);
lean_dec(v_i_2511_);
v_stop_boxed_2515_ = lean_unbox_usize(v_stop_2512_);
lean_dec(v_stop_2512_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2509_, v_as_2510_, v_i_boxed_2514_, v_stop_boxed_2515_, v_b_2513_);
lean_dec_ref(v_as_2510_);
lean_dec_ref(v___x_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(lean_object* v___x_2519_, lean_object* v_as_2520_, size_t v_i_2521_, size_t v_stop_2522_, lean_object* v_b_2523_){
_start:
{
lean_object* v___y_2525_; uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_eq(v_i_2521_, v_stop_2522_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v_fst_2531_; lean_object* v_snd_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2555_; 
v___x_2530_ = lean_array_uget(v_as_2520_, v_i_2521_);
v_fst_2531_ = lean_ctor_get(v___x_2530_, 0);
v_snd_2532_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2534_ = v___x_2530_;
v_isShared_2535_ = v_isSharedCheck_2555_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_snd_2532_);
lean_inc(v_fst_2531_);
lean_dec(v___x_2530_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2555_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___y_2538_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v_snd_2532_);
v___x_2546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___closed__0));
v___x_2547_ = lean_nat_dec_lt(v___x_2536_, v___x_2545_);
if (v___x_2547_ == 0)
{
lean_dec(v_snd_2532_);
v___y_2538_ = v___x_2546_;
goto v___jp_2537_;
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_le(v___x_2545_, v___x_2545_);
if (v___x_2548_ == 0)
{
if (v___x_2547_ == 0)
{
lean_dec(v_snd_2532_);
v___y_2538_ = v___x_2546_;
goto v___jp_2537_;
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2545_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2519_, v_snd_2532_, v___x_2549_, v___x_2550_, v___x_2546_);
lean_dec(v_snd_2532_);
v___y_2538_ = v___x_2551_;
goto v___jp_2537_;
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2545_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2519_, v_snd_2532_, v___x_2552_, v___x_2553_, v___x_2546_);
lean_dec(v_snd_2532_);
v___y_2538_ = v___x_2554_;
goto v___jp_2537_;
}
}
v___jp_2537_:
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_array_get_size(v___y_2538_);
v___x_2540_ = lean_nat_dec_eq(v___x_2539_, v___x_2536_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2542_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___y_2538_);
v___x_2542_ = v___x_2534_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_fst_2531_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___y_2538_);
v___x_2542_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_push(v_b_2523_, v___x_2542_);
v___y_2525_ = v___x_2543_;
goto v___jp_2524_;
}
}
else
{
lean_dec_ref(v___y_2538_);
lean_del_object(v___x_2534_);
lean_dec(v_fst_2531_);
v___y_2525_ = v_b_2523_;
goto v___jp_2524_;
}
}
}
}
else
{
return v_b_2523_;
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2521_, v___x_2526_);
v_i_2521_ = v___x_2527_;
v_b_2523_ = v___y_2525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___boxed(lean_object* v___x_2556_, lean_object* v_as_2557_, lean_object* v_i_2558_, lean_object* v_stop_2559_, lean_object* v_b_2560_){
_start:
{
size_t v_i_boxed_2561_; size_t v_stop_boxed_2562_; lean_object* v_res_2563_; 
v_i_boxed_2561_ = lean_unbox_usize(v_i_2558_);
lean_dec(v_i_2558_);
v_stop_boxed_2562_ = lean_unbox_usize(v_stop_2559_);
lean_dec(v_stop_2559_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2556_, v_as_2557_, v_i_boxed_2561_, v_stop_boxed_2562_, v_b_2560_);
lean_dec_ref(v_as_2557_);
lean_dec_ref(v___x_2556_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(lean_object* v___x_2564_, lean_object* v_as_2565_, lean_object* v_start_2566_, lean_object* v_stop_2567_){
_start:
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2569_ = lean_nat_dec_lt(v_start_2566_, v_stop_2567_);
if (v___x_2569_ == 0)
{
return v___x_2568_;
}
else
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = lean_array_get_size(v_as_2565_);
v___x_2571_ = lean_nat_dec_le(v_stop_2567_, v___x_2570_);
if (v___x_2571_ == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_lt(v_start_2566_, v___x_2570_);
if (v___x_2572_ == 0)
{
return v___x_2568_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v_start_2566_);
v___x_2574_ = lean_usize_of_nat(v___x_2570_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2564_, v_as_2565_, v___x_2573_, v___x_2574_, v___x_2568_);
return v___x_2575_;
}
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_usize_of_nat(v_start_2566_);
v___x_2577_ = lean_usize_of_nat(v_stop_2567_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2564_, v_as_2565_, v___x_2576_, v___x_2577_, v___x_2568_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object* v___x_2579_, lean_object* v_as_2580_, lean_object* v_start_2581_, lean_object* v_stop_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(v___x_2579_, v_as_2580_, v_start_2581_, v_stop_2582_);
lean_dec(v_stop_2582_);
lean_dec(v_start_2581_);
lean_dec_ref(v_as_2580_);
lean_dec_ref(v___x_2579_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(lean_object* v___x_2584_, uint8_t v_anyFailed_2585_, uint8_t v___y_2586_, lean_object* v_____r_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2591_ = lean_box(v_anyFailed_2585_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2584_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = lean_box(v___y_2586_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1___boxed(lean_object* v___x_2596_, lean_object* v_anyFailed_2597_, lean_object* v___y_2598_, lean_object* v_____r_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v_anyFailed_boxed_2603_; uint8_t v___y_31596__boxed_2604_; lean_object* v_res_2605_; 
v_anyFailed_boxed_2603_ = lean_unbox(v_anyFailed_2597_);
v___y_31596__boxed_2604_ = lean_unbox(v___y_2598_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_2596_, v_anyFailed_boxed_2603_, v___y_31596__boxed_2604_, v_____r_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(lean_object* v_as_2606_, size_t v_i_2607_, size_t v_stop_2608_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_eq(v_i_2607_, v_stop_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v_snd_2611_; lean_object* v_size_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2610_ = lean_array_uget_borrowed(v_as_2606_, v_i_2607_);
v_snd_2611_ = lean_ctor_get(v___x_2610_, 1);
v_size_2612_ = lean_ctor_get(v_snd_2611_, 0);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_nat_dec_eq(v_size_2612_, v___x_2613_);
v___x_2615_ = lean_bool_not(v___x_2614_);
if (v___x_2615_ == 0)
{
size_t v___x_2616_; size_t v___x_2617_; 
v___x_2616_ = ((size_t)1ULL);
v___x_2617_ = lean_usize_add(v_i_2607_, v___x_2616_);
v_i_2607_ = v___x_2617_;
goto _start;
}
else
{
return v___x_2615_;
}
}
else
{
uint8_t v___x_2619_; 
v___x_2619_ = 0;
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v_as_2620_, lean_object* v_i_2621_, lean_object* v_stop_2622_){
_start:
{
size_t v_i_boxed_2623_; size_t v_stop_boxed_2624_; uint8_t v_res_2625_; lean_object* v_r_2626_; 
v_i_boxed_2623_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_stop_boxed_2624_ = lean_unbox_usize(v_stop_2622_);
lean_dec(v_stop_2622_);
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(v_as_2620_, v_i_boxed_2623_, v_stop_boxed_2624_);
lean_dec_ref(v_as_2620_);
v_r_2626_ = lean_box(v_res_2625_);
return v_r_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(lean_object* v___x_2627_, uint8_t v_anyFailed_2628_, lean_object* v_____r_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2633_ = lean_box(v_anyFailed_2628_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2627_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_box(v_anyFailed_2628_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0___boxed(lean_object* v___x_2638_, lean_object* v_anyFailed_2639_, lean_object* v_____r_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v_anyFailed_boxed_2644_; lean_object* v_res_2645_; 
v_anyFailed_boxed_2644_ = lean_unbox(v_anyFailed_2639_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_2638_, v_anyFailed_boxed_2644_, v_____r_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_x_2646_, lean_object* v_x_2647_){
_start:
{
if (lean_obj_tag(v_x_2647_) == 0)
{
return v_x_2646_;
}
else
{
lean_object* v_key_2648_; lean_object* v_value_2649_; lean_object* v_tail_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_key_2648_ = lean_ctor_get(v_x_2647_, 0);
v_value_2649_ = lean_ctor_get(v_x_2647_, 1);
v_tail_2650_ = lean_ctor_get(v_x_2647_, 2);
lean_inc(v_value_2649_);
lean_inc(v_key_2648_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_key_2648_);
lean_ctor_set(v___x_2651_, 1, v_value_2649_);
v___x_2652_ = lean_array_push(v_x_2646_, v___x_2651_);
v_x_2646_ = v___x_2652_;
v_x_2647_ = v_tail_2650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(v_x_2654_, v_x_2655_);
lean_dec(v_x_2655_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_2657_, size_t v_i_2658_, size_t v_stop_2659_, lean_object* v_b_2660_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = lean_usize_dec_eq(v_i_2658_, v_stop_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; size_t v___x_2664_; size_t v___x_2665_; 
v___x_2662_ = lean_array_uget_borrowed(v_as_2657_, v_i_2658_);
v___x_2663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(v_b_2660_, v___x_2662_);
v___x_2664_ = ((size_t)1ULL);
v___x_2665_ = lean_usize_add(v_i_2658_, v___x_2664_);
v_i_2658_ = v___x_2665_;
v_b_2660_ = v___x_2663_;
goto _start;
}
else
{
return v_b_2660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_2667_, lean_object* v_i_2668_, lean_object* v_stop_2669_, lean_object* v_b_2670_){
_start:
{
size_t v_i_boxed_2671_; size_t v_stop_boxed_2672_; lean_object* v_res_2673_; 
v_i_boxed_2671_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_stop_boxed_2672_ = lean_unbox_usize(v_stop_2669_);
lean_dec(v_stop_2669_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_as_2667_, v_i_boxed_2671_, v_stop_boxed_2672_, v_b_2670_);
lean_dec_ref(v_as_2667_);
return v_res_2673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2678_ = lean_unsigned_to_nat(0u);
v___x_2679_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
lean_ctor_set(v___x_2679_, 2, v___x_2678_);
lean_ctor_set(v___x_2679_, 3, v___x_2678_);
lean_ctor_set(v___x_2679_, 4, v___x_2677_);
lean_ctor_set(v___x_2679_, 5, v___x_2677_);
lean_ctor_set(v___x_2679_, 6, v___x_2677_);
lean_ctor_set(v___x_2679_, 7, v___x_2677_);
lean_ctor_set(v___x_2679_, 8, v___x_2677_);
lean_ctor_set(v___x_2679_, 9, v___x_2677_);
return v___x_2679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_unsigned_to_nat(32u);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2683_ = ((size_t)5ULL);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_unsigned_to_nat(32u);
v___x_2686_ = lean_mk_empty_array_with_capacity(v___x_2685_);
v___x_2687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_2688_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v___x_2686_);
lean_ctor_set(v___x_2688_, 2, v___x_2684_);
lean_ctor_set(v___x_2688_, 3, v___x_2684_);
lean_ctor_set_usize(v___x_2688_, 4, v___x_2683_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = lean_box(1);
v___x_2690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_2691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v___x_2690_);
lean_ctor_set(v___x_2692_, 2, v___x_2689_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_2698_ = l_Lean_stringToMessageData(v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_2701_ = l_Lean_stringToMessageData(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_2710_ = l_Lean_stringToMessageData(v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_2714_, lean_object* v_declHint_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v_env_2719_; uint8_t v___y_2721_; uint8_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2718_ = lean_st_ref_get(v___y_2716_);
v_env_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_env_2719_);
lean_dec(v___x_2718_);
v___x_2777_ = l_Lean_Name_isAnonymous(v_declHint_2715_);
v___x_2778_ = lean_bool_not(v___x_2777_);
if (v___x_2778_ == 0)
{
v___y_2721_ = v___x_2778_;
goto v___jp_2720_;
}
else
{
uint8_t v_isExporting_2779_; 
v_isExporting_2779_ = lean_ctor_get_uint8(v_env_2719_, sizeof(void*)*8);
v___y_2721_ = v_isExporting_2779_;
goto v___jp_2720_;
}
v___jp_2720_:
{
if (v___y_2721_ == 0)
{
lean_object* v___x_2722_; 
lean_dec_ref(v_env_2719_);
lean_dec(v_declHint_2715_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v_msg_2714_);
return v___x_2722_;
}
else
{
uint8_t v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2723_ = 0;
lean_inc_ref(v_env_2719_);
v___x_2724_ = l_Lean_Environment_setExporting(v_env_2719_, v___x_2723_);
lean_inc(v_declHint_2715_);
lean_inc_ref(v___x_2724_);
v___x_2725_ = l_Lean_Environment_contains(v___x_2724_, v_declHint_2715_, v___y_2721_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
lean_dec_ref(v___x_2724_);
lean_dec_ref(v_env_2719_);
lean_dec(v_declHint_2715_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_msg_2714_);
return v___x_2726_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v_c_2732_; lean_object* v___x_2733_; 
v___x_2727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_2729_ = l_Lean_Options_empty;
v___x_2730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2724_);
lean_ctor_set(v___x_2730_, 1, v___x_2727_);
lean_ctor_set(v___x_2730_, 2, v___x_2728_);
lean_ctor_set(v___x_2730_, 3, v___x_2729_);
lean_inc(v_declHint_2715_);
v___x_2731_ = l_Lean_MessageData_ofConstName(v_declHint_2715_, v___x_2723_);
v_c_2732_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2732_, 0, v___x_2730_);
lean_ctor_set(v_c_2732_, 1, v___x_2731_);
v___x_2733_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2719_, v_declHint_2715_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec_ref(v_env_2719_);
lean_dec(v_declHint_2715_);
v___x_2734_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_c_2732_);
v___x_2736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = l_Lean_MessageData_note(v___x_2737_);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v_msg_2714_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
else
{
lean_object* v_val_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2776_; 
v_val_2741_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2743_ = v___x_2733_;
v_isShared_2744_ = v_isSharedCheck_2776_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_val_2741_);
lean_dec(v___x_2733_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2776_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v_mod_2748_; uint8_t v___x_2749_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = l_Lean_Environment_header(v_env_2719_);
lean_dec_ref(v_env_2719_);
v___x_2747_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2746_);
v_mod_2748_ = lean_array_get(v___x_2745_, v___x_2747_, v_val_2741_);
lean_dec(v_val_2741_);
lean_dec_ref(v___x_2747_);
v___x_2749_ = l_Lean_isPrivateName(v_declHint_2715_);
lean_dec(v_declHint_2715_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_c_2732_);
v___x_2752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_MessageData_ofName(v_mod_2748_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_MessageData_note(v___x_2757_);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_msg_2714_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2759_);
v___x_2761_ = v___x_2743_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v_c_2732_);
v___x_2765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Lean_MessageData_ofName(v_mod_2748_);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_2770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = l_Lean_MessageData_note(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_msg_2714_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2772_);
v___x_2774_ = v___x_2743_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_2780_, lean_object* v_declHint_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2780_, v_declHint_2781_, v___y_2782_);
lean_dec(v___y_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(lean_object* v_msg_2785_, lean_object* v_declHint_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2800_; 
v___x_2790_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2785_, v_declHint_2786_, v___y_2788_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2795_ = l_Lean_unknownIdentifierMessageTag;
v___x_2796_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_a_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2796_);
v___x_2798_ = v___x_2793_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_2801_, lean_object* v_declHint_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(v_msg_2801_, v_declHint_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(lean_object* v_msgData_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; lean_object* v_env_2812_; lean_object* v_options_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2811_ = lean_st_ref_get(v___y_2809_);
v_env_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_env_2812_);
lean_dec(v___x_2811_);
v_options_2813_ = lean_ctor_get(v___y_2808_, 2);
v___x_2814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2815_ = lean_unsigned_to_nat(32u);
v___x_2816_ = lean_mk_empty_array_with_capacity(v___x_2815_);
lean_dec_ref(v___x_2816_);
v___x_2817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_2813_);
v___x_2818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2818_, 0, v_env_2812_);
lean_ctor_set(v___x_2818_, 1, v___x_2814_);
lean_ctor_set(v___x_2818_, 2, v___x_2817_);
lean_ctor_set(v___x_2818_, 3, v_options_2813_);
v___x_2819_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_msgData_2807_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23___boxed(lean_object* v_msgData_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(v_msgData_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_ref_2830_; lean_object* v___x_2831_; lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2840_; 
v_ref_2830_ = lean_ctor_get(v___y_2827_, 5);
v___x_2831_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(v_msg_2826_, v___y_2827_, v___y_2828_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_inc(v_ref_2830_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_ref_2830_);
lean_ctor_set(v___x_2836_, 1, v_a_2832_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2836_);
v___x_2838_ = v___x_2834_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_2846_, lean_object* v_msg_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_fileName_2851_; lean_object* v_fileMap_2852_; lean_object* v_options_2853_; lean_object* v_currRecDepth_2854_; lean_object* v_maxRecDepth_2855_; lean_object* v_ref_2856_; lean_object* v_currNamespace_2857_; lean_object* v_openDecls_2858_; lean_object* v_initHeartbeats_2859_; lean_object* v_maxHeartbeats_2860_; lean_object* v_quotContext_2861_; lean_object* v_currMacroScope_2862_; uint8_t v_diag_2863_; lean_object* v_cancelTk_x3f_2864_; uint8_t v_suppressElabErrors_2865_; lean_object* v_inheritedTraceOptions_2866_; lean_object* v_ref_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_fileName_2851_ = lean_ctor_get(v___y_2848_, 0);
v_fileMap_2852_ = lean_ctor_get(v___y_2848_, 1);
v_options_2853_ = lean_ctor_get(v___y_2848_, 2);
v_currRecDepth_2854_ = lean_ctor_get(v___y_2848_, 3);
v_maxRecDepth_2855_ = lean_ctor_get(v___y_2848_, 4);
v_ref_2856_ = lean_ctor_get(v___y_2848_, 5);
v_currNamespace_2857_ = lean_ctor_get(v___y_2848_, 6);
v_openDecls_2858_ = lean_ctor_get(v___y_2848_, 7);
v_initHeartbeats_2859_ = lean_ctor_get(v___y_2848_, 8);
v_maxHeartbeats_2860_ = lean_ctor_get(v___y_2848_, 9);
v_quotContext_2861_ = lean_ctor_get(v___y_2848_, 10);
v_currMacroScope_2862_ = lean_ctor_get(v___y_2848_, 11);
v_diag_2863_ = lean_ctor_get_uint8(v___y_2848_, sizeof(void*)*14);
v_cancelTk_x3f_2864_ = lean_ctor_get(v___y_2848_, 12);
v_suppressElabErrors_2865_ = lean_ctor_get_uint8(v___y_2848_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2866_ = lean_ctor_get(v___y_2848_, 13);
v_ref_2867_ = l_Lean_replaceRef(v_ref_2846_, v_ref_2856_);
lean_inc_ref(v_inheritedTraceOptions_2866_);
lean_inc(v_cancelTk_x3f_2864_);
lean_inc(v_currMacroScope_2862_);
lean_inc(v_quotContext_2861_);
lean_inc(v_maxHeartbeats_2860_);
lean_inc(v_initHeartbeats_2859_);
lean_inc(v_openDecls_2858_);
lean_inc(v_currNamespace_2857_);
lean_inc(v_maxRecDepth_2855_);
lean_inc(v_currRecDepth_2854_);
lean_inc_ref(v_options_2853_);
lean_inc_ref(v_fileMap_2852_);
lean_inc_ref(v_fileName_2851_);
v___x_2868_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2868_, 0, v_fileName_2851_);
lean_ctor_set(v___x_2868_, 1, v_fileMap_2852_);
lean_ctor_set(v___x_2868_, 2, v_options_2853_);
lean_ctor_set(v___x_2868_, 3, v_currRecDepth_2854_);
lean_ctor_set(v___x_2868_, 4, v_maxRecDepth_2855_);
lean_ctor_set(v___x_2868_, 5, v_ref_2867_);
lean_ctor_set(v___x_2868_, 6, v_currNamespace_2857_);
lean_ctor_set(v___x_2868_, 7, v_openDecls_2858_);
lean_ctor_set(v___x_2868_, 8, v_initHeartbeats_2859_);
lean_ctor_set(v___x_2868_, 9, v_maxHeartbeats_2860_);
lean_ctor_set(v___x_2868_, 10, v_quotContext_2861_);
lean_ctor_set(v___x_2868_, 11, v_currMacroScope_2862_);
lean_ctor_set(v___x_2868_, 12, v_cancelTk_x3f_2864_);
lean_ctor_set(v___x_2868_, 13, v_inheritedTraceOptions_2866_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14, v_diag_2863_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14 + 1, v_suppressElabErrors_2865_);
v___x_2869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_2847_, v___x_2868_, v___y_2849_);
lean_dec_ref_known(v___x_2868_, 14);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_2870_, lean_object* v_msg_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_2870_, v_msg_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_ref_2870_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(lean_object* v_ref_2876_, lean_object* v_msg_2877_, lean_object* v_declHint_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v_a_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(v_msg_2877_, v_declHint_2878_, v___y_2879_, v___y_2880_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_2876_, v_a_2883_, v___y_2879_, v___y_2880_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg___boxed(lean_object* v_ref_2885_, lean_object* v_msg_2886_, lean_object* v_declHint_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_2885_, v_msg_2886_, v_declHint_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v_ref_2885_);
return v_res_2891_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__0));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(lean_object* v_ref_2897_, lean_object* v_constName_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2902_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1);
v___x_2903_ = 0;
lean_inc(v_constName_2898_);
v___x_2904_ = l_Lean_MessageData_ofConstName(v_constName_2898_, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2902_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_2897_, v___x_2907_, v_constName_2898_, v___y_2899_, v___y_2900_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___boxed(lean_object* v_ref_2909_, lean_object* v_constName_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_2909_, v_constName_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v_ref_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_ref_2919_; lean_object* v___x_2920_; 
v_ref_2919_ = lean_ctor_get(v___y_2916_, 5);
v___x_2920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_2919_, v_constName_2915_, v___y_2916_, v___y_2917_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(lean_object* v_constName_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v_env_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = lean_st_ref_get(v___y_2928_);
v_env_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2930_);
v___x_2932_ = 0;
lean_inc(v_constName_2926_);
v___x_2933_ = l_Lean_Environment_find_x3f(v_env_2931_, v_constName_2926_, v___x_2932_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_2926_, v___y_2927_, v___y_2928_);
return v___x_2934_;
}
else
{
lean_object* v_val_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_constName_2926_);
v_val_2935_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2933_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_val_2935_);
lean_dec(v___x_2933_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 0);
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_val_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2___boxed(lean_object* v_constName_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(v_constName_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_declName_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
lean_inc(v_declName_2948_);
v___x_2952_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(v_declName_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2979_; 
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v___x_2952_, 0);
lean_dec(v_unused_2980_);
v___x_2954_ = v___x_2952_;
v_isShared_2955_ = v_isSharedCheck_2979_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v___x_2952_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2979_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v_env_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_st_ref_get(v___y_2950_);
v_env_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2956_);
v___x_2958_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2957_, v_declName_2948_);
lean_dec(v_declName_2948_);
lean_dec_ref(v_env_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_box(0);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2959_);
v___x_2961_ = v___x_2954_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
else
{
lean_object* v_val_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2978_; 
v_val_2963_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2965_ = v___x_2958_;
v_isShared_2966_ = v_isSharedCheck_2978_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_val_2963_);
lean_dec(v___x_2958_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2978_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v_env_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2967_ = lean_st_ref_get(v___y_2950_);
v_env_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_ref(v_env_2968_);
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = l_Lean_Environment_allImportedModuleNames(v_env_2968_);
lean_dec_ref(v_env_2968_);
v___x_2971_ = lean_array_get(v___x_2969_, v___x_2970_, v_val_2963_);
lean_dec(v_val_2963_);
lean_dec_ref(v___x_2970_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2971_);
v___x_2973_ = v___x_2965_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2973_);
v___x_2975_ = v___x_2954_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_declName_2948_);
v_a_2981_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2952_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2952_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_declName_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(v_declName_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(uint8_t v___x_2995_, lean_object* v_fst_2996_, lean_object* v___x_2997_, lean_object* v___x_2998_, lean_object* v_as_2999_, size_t v_sz_3000_, size_t v_i_3001_, lean_object* v_b_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_a_3007_; uint8_t v_anyUnlocated_3011_; 
v_anyUnlocated_3011_ = lean_usize_dec_lt(v_i_3001_, v_sz_3000_);
if (v_anyUnlocated_3011_ == 0)
{
lean_object* v___x_3012_; 
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_b_3002_);
return v___x_3012_;
}
else
{
lean_object* v_a_3013_; lean_object* v_fst_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3149_; 
v_a_3013_ = lean_array_uget(v_as_2999_, v_i_3001_);
v_fst_3014_ = lean_ctor_get(v_a_3013_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_a_3013_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_a_3013_, 1);
lean_dec(v_unused_3150_);
v___x_3016_ = v_a_3013_;
v_isShared_3017_ = v_isSharedCheck_3149_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_fst_3014_);
lean_dec(v_a_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3149_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; 
lean_inc(v_fst_3014_);
v___x_3018_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3014_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
if (lean_obj_tag(v_a_3019_) == 0)
{
lean_object* v_fst_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3054_; 
v_fst_3020_ = lean_ctor_get(v_b_3002_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_b_3002_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v_b_3002_, 1);
lean_dec(v_unused_3055_);
v___x_3022_ = v_b_3002_;
v_isShared_3023_ = v_isSharedCheck_3054_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_fst_3020_);
lean_dec(v_b_3002_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3054_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_optName_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_optName_3024_ = lean_ctor_get(v_fst_2996_, 1);
v___x_3025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0));
v___x_3026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3014_, v___x_2995_);
v___x_3027_ = lean_string_append(v___x_3025_, v___x_3026_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
lean_inc(v_optName_3024_);
v___x_3030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3024_, v___x_2995_);
v___x_3031_ = lean_string_append(v___x_3029_, v___x_3030_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3033_ = lean_string_append(v___x_3031_, v___x_3032_);
v___x_3034_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3033_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_dec_ref_known(v___x_3034_, 1);
lean_del_object(v___x_3016_);
v___x_3035_ = lean_box(v_anyUnlocated_3011_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3035_);
v___x_3037_ = v___x_3022_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_fst_3020_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
v_a_3007_ = v___x_3037_;
goto v___jp_3006_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3053_; 
lean_del_object(v___x_3022_);
lean_dec(v_fst_3020_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v_a_3039_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3041_ = v___x_3034_;
v_isShared_3042_ = v_isSharedCheck_3053_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3034_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3053_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_ref_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v_ref_3043_ = lean_ctor_get(v___y_3003_, 5);
v___x_3044_ = lean_io_error_to_string(v_a_3039_);
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
v___x_3046_ = l_Lean_MessageData_ofFormat(v___x_3045_);
lean_inc(v_ref_3043_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v___x_3046_);
lean_ctor_set(v___x_3016_, 0, v_ref_3043_);
v___x_3048_ = v___x_3016_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_ref_3043_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3048_);
v___x_3050_ = v___x_3041_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3056_; lean_object* v_snd_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3140_; 
v_fst_3056_ = lean_ctor_get(v_b_3002_, 0);
v_snd_3057_ = lean_ctor_get(v_b_3002_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_b_3002_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3059_ = v_b_3002_;
v_isShared_3060_ = v_isSharedCheck_3140_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snd_3057_);
lean_inc(v_fst_3056_);
lean_dec(v_b_3002_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3140_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_val_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3139_; 
v_val_3061_ = lean_ctor_get(v_a_3019_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_a_3019_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3063_ = v_a_3019_;
v_isShared_3064_ = v_isSharedCheck_3139_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_val_3061_);
lean_dec(v_a_3019_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3139_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(v_fst_3014_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___y_3068_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
if (lean_obj_tag(v_a_3066_) == 0)
{
lean_inc(v___x_2998_);
v___y_3068_ = v___x_2998_;
goto v___jp_3067_;
}
else
{
lean_object* v_val_3130_; 
v_val_3130_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v_a_3066_, 1);
v___y_3068_ = v_val_3130_;
goto v___jp_3067_;
}
v___jp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3068_);
lean_inc(v___x_2997_);
v___x_3070_ = l_Lean_SearchPath_findWithExt(v___x_2997_, v___x_3069_, v___y_3068_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
if (lean_obj_tag(v_a_3071_) == 0)
{
lean_object* v_optName_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec(v_val_3061_);
lean_dec(v_snd_3057_);
v_optName_3072_ = lean_ctor_get(v_fst_2996_, 1);
v___x_3073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3068_, v___x_2995_);
v___x_3075_ = lean_string_append(v___x_3073_, v___x_3074_);
lean_dec_ref(v___x_3074_);
v___x_3076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3077_ = lean_string_append(v___x_3075_, v___x_3076_);
lean_inc(v_optName_3072_);
v___x_3078_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3072_, v___x_2995_);
v___x_3079_ = lean_string_append(v___x_3077_, v___x_3078_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3081_ = lean_string_append(v___x_3079_, v___x_3080_);
v___x_3082_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3081_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec_ref_known(v___x_3082_, 1);
lean_del_object(v___x_3063_);
lean_del_object(v___x_3016_);
v___x_3083_ = lean_box(v_anyUnlocated_3011_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v___x_3083_);
v___x_3085_ = v___x_3059_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_fst_3056_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
v_a_3007_ = v___x_3085_;
goto v___jp_3006_;
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3103_; 
lean_del_object(v___x_3059_);
lean_dec(v_fst_3056_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v_a_3087_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3089_ = v___x_3082_;
v_isShared_3090_ = v_isSharedCheck_3103_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3082_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3103_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_ref_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v_ref_3091_ = lean_ctor_get(v___y_3003_, 5);
v___x_3092_ = lean_io_error_to_string(v_a_3087_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 3);
lean_ctor_set(v___x_3063_, 0, v___x_3092_);
v___x_3094_ = v___x_3063_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = l_Lean_MessageData_ofFormat(v___x_3094_);
lean_inc(v_ref_3091_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v___x_3095_);
lean_ctor_set(v___x_3016_, 0, v_ref_3091_);
v___x_3097_ = v___x_3016_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_ref_3091_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3097_);
v___x_3099_ = v___x_3089_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
else
{
lean_object* v_range_3104_; lean_object* v_val_3105_; lean_object* v_pos_3106_; lean_object* v_optName_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
lean_dec(v___y_3068_);
lean_del_object(v___x_3063_);
lean_del_object(v___x_3016_);
v_range_3104_ = lean_ctor_get(v_val_3061_, 0);
lean_inc_ref(v_range_3104_);
lean_dec(v_val_3061_);
v_val_3105_ = lean_ctor_get(v_a_3071_, 0);
lean_inc(v_val_3105_);
lean_dec_ref_known(v_a_3071_, 1);
v_pos_3106_ = lean_ctor_get(v_range_3104_, 0);
lean_inc_ref(v_pos_3106_);
lean_dec_ref(v_range_3104_);
v_optName_3107_ = lean_ctor_get(v_fst_2996_, 1);
lean_inc(v_optName_3107_);
v___x_3108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3108_, 0, v_val_3105_);
lean_ctor_set(v___x_3108_, 1, v_pos_3106_);
lean_ctor_set(v___x_3108_, 2, v_optName_3107_);
v___x_3109_ = lean_array_push(v_fst_3056_, v___x_3108_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3109_);
v___x_3111_ = v___x_3059_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_snd_3057_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
v_a_3007_ = v___x_3111_;
goto v___jp_3006_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v___y_3068_);
lean_dec(v_val_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_snd_3057_);
lean_dec(v_fst_3056_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v_a_3113_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3115_ = v___x_3070_;
v_isShared_3116_ = v_isSharedCheck_3129_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3070_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3129_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v_ref_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v_ref_3117_ = lean_ctor_get(v___y_3003_, 5);
v___x_3118_ = lean_io_error_to_string(v_a_3113_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 3);
lean_ctor_set(v___x_3063_, 0, v___x_3118_);
v___x_3120_ = v___x_3063_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = l_Lean_MessageData_ofFormat(v___x_3120_);
lean_inc(v_ref_3117_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v___x_3121_);
lean_ctor_set(v___x_3016_, 0, v_ref_3117_);
v___x_3123_ = v___x_3016_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_ref_3117_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3123_);
v___x_3125_ = v___x_3115_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_del_object(v___x_3063_);
lean_dec(v_val_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_snd_3057_);
lean_dec(v_fst_3056_);
lean_del_object(v___x_3016_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v_a_3131_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3065_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3065_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_del_object(v___x_3016_);
lean_dec(v_fst_3014_);
lean_dec_ref(v_b_3002_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
lean_dec_ref(v_fst_2996_);
v_a_3141_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3018_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3018_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
v___jp_3006_:
{
size_t v___x_3008_; size_t v___x_3009_; 
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_3001_, v___x_3008_);
v_i_3001_ = v___x_3009_;
v_b_3002_ = v_a_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_3151_, lean_object* v_fst_3152_, lean_object* v___x_3153_, lean_object* v___x_3154_, lean_object* v_as_3155_, lean_object* v_sz_3156_, lean_object* v_i_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_32281__boxed_3162_; size_t v_sz_boxed_3163_; size_t v_i_boxed_3164_; lean_object* v_res_3165_; 
v___x_32281__boxed_3162_ = lean_unbox(v___x_3151_);
v_sz_boxed_3163_ = lean_unbox_usize(v_sz_3156_);
lean_dec(v_sz_3156_);
v_i_boxed_3164_ = lean_unbox_usize(v_i_3157_);
lean_dec(v_i_3157_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_32281__boxed_3162_, v_fst_3152_, v___x_3153_, v___x_3154_, v_as_3155_, v_sz_boxed_3163_, v_i_boxed_3164_, v_b_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v_as_3155_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(uint8_t v___x_3166_, lean_object* v___x_3167_, lean_object* v___x_3168_, lean_object* v_as_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v___x_3176_; 
v___x_3176_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_b_3172_);
return v___x_3177_;
}
else
{
lean_object* v_a_3178_; lean_object* v_fst_3179_; lean_object* v_snd_3180_; lean_object* v_fst_3181_; lean_object* v_snd_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3220_; 
v_a_3178_ = lean_array_uget_borrowed(v_as_3169_, v_i_3171_);
v_fst_3179_ = lean_ctor_get(v_a_3178_, 0);
v_snd_3180_ = lean_ctor_get(v_a_3178_, 1);
v_fst_3181_ = lean_ctor_get(v_b_3172_, 0);
v_snd_3182_ = lean_ctor_get(v_b_3172_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_b_3172_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3184_ = v_b_3172_;
v_isShared_3185_ = v_isSharedCheck_3220_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_snd_3182_);
lean_inc(v_fst_3181_);
lean_dec(v_b_3172_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3220_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___y_3187_; lean_object* v_size_3207_; lean_object* v_buckets_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v_size_3207_ = lean_ctor_get(v_snd_3180_, 0);
v_buckets_3208_ = lean_ctor_get(v_snd_3180_, 1);
v___x_3209_ = lean_mk_empty_array_with_capacity(v_size_3207_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = lean_array_get_size(v_buckets_3208_);
v___x_3212_ = lean_nat_dec_lt(v___x_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
v___y_3187_ = v___x_3209_;
goto v___jp_3186_;
}
else
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_nat_dec_le(v___x_3211_, v___x_3211_);
if (v___x_3213_ == 0)
{
if (v___x_3212_ == 0)
{
v___y_3187_ = v___x_3209_;
goto v___jp_3186_;
}
else
{
size_t v___x_3214_; size_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = ((size_t)0ULL);
v___x_3215_ = lean_usize_of_nat(v___x_3211_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_buckets_3208_, v___x_3214_, v___x_3215_, v___x_3209_);
v___y_3187_ = v___x_3216_;
goto v___jp_3186_;
}
}
else
{
size_t v___x_3217_; size_t v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = ((size_t)0ULL);
v___x_3218_ = lean_usize_of_nat(v___x_3211_);
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_buckets_3208_, v___x_3217_, v___x_3218_, v___x_3209_);
v___y_3187_ = v___x_3219_;
goto v___jp_3186_;
}
}
v___jp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3185_ == 0)
{
v___x_3189_ = v___x_3184_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_fst_3181_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_snd_3182_);
v___x_3189_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
size_t v_sz_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v_sz_3190_ = lean_array_size(v___y_3187_);
v___x_3191_ = ((size_t)0ULL);
lean_inc(v___x_3168_);
lean_inc(v___x_3167_);
lean_inc(v_fst_3179_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_3166_, v_fst_3179_, v___x_3167_, v___x_3168_, v___y_3187_, v_sz_3190_, v___x_3191_, v___x_3189_, v___y_3173_, v___y_3174_);
lean_dec_ref(v___y_3187_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v_fst_3194_; lean_object* v_snd_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3205_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v_fst_3194_ = lean_ctor_get(v_a_3193_, 0);
v_snd_3195_ = lean_ctor_get(v_a_3193_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_a_3193_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3197_ = v_a_3193_;
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_snd_3195_);
lean_inc(v_fst_3194_);
lean_dec(v_a_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_fst_3194_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_snd_3195_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
size_t v___x_3201_; size_t v___x_3202_; 
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3171_, v___x_3201_);
v_i_3171_ = v___x_3202_;
v_b_3172_ = v___x_3200_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
return v___x_3192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_3221_, lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v_as_3224_, lean_object* v_sz_3225_, lean_object* v_i_3226_, lean_object* v_b_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v___x_32570__boxed_3231_; size_t v_sz_boxed_3232_; size_t v_i_boxed_3233_; lean_object* v_res_3234_; 
v___x_32570__boxed_3231_ = lean_unbox(v___x_3221_);
v_sz_boxed_3232_ = lean_unbox_usize(v_sz_3225_);
lean_dec(v_sz_3225_);
v_i_boxed_3233_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_32570__boxed_3231_, v___x_3222_, v___x_3223_, v_as_3224_, v_sz_boxed_3232_, v_i_boxed_3233_, v_b_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec_ref(v_as_3224_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(lean_object* v_as_3235_, size_t v_i_3236_, size_t v_stop_3237_, lean_object* v_b_3238_){
_start:
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_usize_dec_eq(v_i_3236_, v_stop_3237_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_fst_3241_; lean_object* v_snd_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; size_t v___x_3245_; size_t v___x_3246_; 
v___x_3240_ = lean_array_uget_borrowed(v_as_3235_, v_i_3236_);
v_fst_3241_ = lean_ctor_get(v___x_3240_, 0);
v_snd_3242_ = lean_ctor_get(v___x_3240_, 1);
v___x_3243_ = lean_unbox(v_snd_3242_);
lean_inc(v_fst_3241_);
v___x_3244_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_3238_, v_fst_3241_, v___x_3243_);
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3236_, v___x_3245_);
v_i_3236_ = v___x_3246_;
v_b_3238_ = v___x_3244_;
goto _start;
}
else
{
return v_b_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13___boxed(lean_object* v_as_3248_, lean_object* v_i_3249_, lean_object* v_stop_3250_, lean_object* v_b_3251_){
_start:
{
size_t v_i_boxed_3252_; size_t v_stop_boxed_3253_; lean_object* v_res_3254_; 
v_i_boxed_3252_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_stop_boxed_3253_ = lean_unbox_usize(v_stop_3250_);
lean_dec(v_stop_3250_);
v_res_3254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_as_3248_, v_i_boxed_3252_, v_stop_boxed_3253_, v_b_3251_);
lean_dec_ref(v_as_3248_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(lean_object* v___x_3255_, lean_object* v_as_3256_, size_t v_sz_3257_, size_t v_i_3258_, lean_object* v_b_3259_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_usize_dec_lt(v_i_3258_, v_sz_3257_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_b_3259_);
return v___x_3262_;
}
else
{
lean_object* v_a_3263_; lean_object* v_message_3264_; lean_object* v___x_3265_; uint8_t v_anyFailed_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3263_ = lean_array_uget_borrowed(v_as_3256_, v_i_3258_);
v_message_3264_ = lean_ctor_get(v_a_3263_, 1);
v___x_3265_ = lean_unsigned_to_nat(0u);
v_anyFailed_3266_ = lean_nat_dec_eq(v___x_3255_, v___x_3265_);
lean_inc_ref(v_message_3264_);
v___x_3267_ = l_Lean_SerialMessage_toString(v_message_3264_, v_anyFailed_3266_);
v___x_3268_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; size_t v___x_3270_; size_t v___x_3271_; 
lean_dec_ref_known(v___x_3268_, 1);
v___x_3269_ = lean_box(0);
v___x_3270_ = ((size_t)1ULL);
v___x_3271_ = lean_usize_add(v_i_3258_, v___x_3270_);
v_i_3258_ = v___x_3271_;
v_b_3259_ = v___x_3269_;
goto _start;
}
else
{
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object* v___x_3273_, lean_object* v_as_3274_, lean_object* v_sz_3275_, lean_object* v_i_3276_, lean_object* v_b_3277_, lean_object* v___y_3278_){
_start:
{
size_t v_sz_boxed_3279_; size_t v_i_boxed_3280_; lean_object* v_res_3281_; 
v_sz_boxed_3279_ = lean_unbox_usize(v_sz_3275_);
lean_dec(v_sz_3275_);
v_i_boxed_3280_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___x_3273_, v_as_3274_, v_sz_boxed_3279_, v_i_boxed_3280_, v_b_3277_);
lean_dec_ref(v_as_3274_);
lean_dec(v___x_3273_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(lean_object* v___x_3284_, lean_object* v_as_3285_, size_t v_sz_3286_, size_t v_i_3287_, lean_object* v_b_3288_){
_start:
{
uint8_t v___x_3290_; 
v___x_3290_ = lean_usize_dec_lt(v_i_3287_, v_sz_3286_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_b_3288_);
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v_fst_3293_; lean_object* v_snd_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3292_ = lean_array_uget_borrowed(v_as_3285_, v_i_3287_);
v_fst_3293_ = lean_ctor_get(v_a_3292_, 0);
v_snd_3294_ = lean_ctor_get(v_a_3292_, 1);
v___x_3295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__0));
lean_inc(v_fst_3293_);
v___x_3296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3293_, v___x_3290_);
v___x_3297_ = lean_string_append(v___x_3295_, v___x_3296_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__1));
v___x_3299_ = lean_string_append(v___x_3297_, v___x_3298_);
v___x_3300_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3299_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; size_t v_sz_3302_; size_t v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3300_, 1);
v___x_3301_ = lean_box(0);
v_sz_3302_ = lean_array_size(v_snd_3294_);
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___x_3284_, v_snd_3294_, v_sz_3302_, v___x_3303_, v___x_3301_);
if (lean_obj_tag(v___x_3304_) == 0)
{
size_t v___x_3305_; size_t v___x_3306_; 
lean_dec_ref_known(v___x_3304_, 1);
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = lean_usize_add(v_i_3287_, v___x_3305_);
v_i_3287_ = v___x_3306_;
v_b_3288_ = v___x_3301_;
goto _start;
}
else
{
return v___x_3304_;
}
}
else
{
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object* v___x_3308_, lean_object* v_as_3309_, lean_object* v_sz_3310_, lean_object* v_i_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_){
_start:
{
size_t v_sz_boxed_3314_; size_t v_i_boxed_3315_; lean_object* v_res_3316_; 
v_sz_boxed_3314_ = lean_unbox_usize(v_sz_3310_);
lean_dec(v_sz_3310_);
v_i_boxed_3315_ = lean_unbox_usize(v_i_3311_);
lean_dec(v_i_3311_);
v_res_3316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(v___x_3308_, v_as_3309_, v_sz_boxed_3314_, v_i_boxed_3315_, v_b_3312_);
lean_dec_ref(v_as_3309_);
lean_dec(v___x_3308_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(lean_object* v___x_3328_, lean_object* v_args_3329_, lean_object* v___x_3330_, lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_){
_start:
{
lean_object* v_a_3337_; lean_object* v_msg_3342_; lean_object* v_a_3347_; lean_object* v___x_3350_; uint8_t v_anyFailed_3351_; uint8_t v_anyUnlocated_3352_; lean_object* v_a_3354_; lean_object* v___x_3367_; lean_object* v_envLinterModule_3368_; uint8_t v___x_3369_; 
v___x_3350_ = lean_unsigned_to_nat(0u);
v_anyFailed_3351_ = lean_nat_dec_eq(v___x_3328_, v___x_3350_);
v_anyUnlocated_3352_ = 1;
v___x_3367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3));
v_envLinterModule_3368_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_3368_, 0, v___x_3367_);
lean_ctor_set_uint8(v_envLinterModule_3368_, sizeof(void*)*1, v_anyFailed_3351_);
lean_ctor_set_uint8(v_envLinterModule_3368_, sizeof(void*)*1 + 1, v_anyUnlocated_3352_);
lean_ctor_set_uint8(v_envLinterModule_3368_, sizeof(void*)*1 + 2, v_anyFailed_3351_);
v___x_3369_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_dec_ref_known(v_envLinterModule_3368_, 1);
lean_dec(v___x_3330_);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_b_3334_);
return v___x_3370_;
}
else
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
lean_dec_ref_known(v___x_3371_, 1);
v_a_3372_ = lean_array_uget_borrowed(v_as_3331_, v_i_3333_);
lean_inc(v_a_3372_);
v___x_3373_ = l_Lean_findOLean(v_a_3372_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = l_Lean_readModuleData(v_a_3374_);
lean_dec(v_a_3374_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3869_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v_fst_3377_ = lean_ctor_get(v_a_3376_, 0);
v_snd_3378_ = lean_ctor_get(v_a_3376_, 1);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3380_ = v_a_3376_;
v_isShared_3381_ = v_isSharedCheck_3869_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_a_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3869_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
uint8_t v___x_3382_; lean_object* v_snd_3383_; lean_object* v_snd_3384_; lean_object* v_fst_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3867_; 
v___x_3382_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_3377_);
lean_dec(v_fst_3377_);
v_snd_3383_ = lean_ctor_get(v_b_3334_, 1);
lean_inc(v_snd_3383_);
v_snd_3384_ = lean_ctor_get(v_snd_3383_, 1);
lean_inc(v_snd_3384_);
v_fst_3385_ = lean_ctor_get(v_b_3334_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_b_3334_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v_b_3334_, 1);
lean_dec(v_unused_3868_);
v___x_3387_ = v_b_3334_;
v_isShared_3388_ = v_isSharedCheck_3867_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_fst_3385_);
lean_dec(v_b_3334_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3867_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_fst_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3865_; 
v_fst_3389_ = lean_ctor_get(v_snd_3383_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_snd_3383_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; 
v_unused_3866_ = lean_ctor_get(v_snd_3383_, 1);
lean_dec(v_unused_3866_);
v___x_3391_ = v_snd_3383_;
v_isShared_3392_ = v_isSharedCheck_3865_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_fst_3389_);
lean_dec(v_snd_3383_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3865_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3864_; 
v_fst_3393_ = lean_ctor_get(v_snd_3384_, 0);
v_snd_3394_ = lean_ctor_get(v_snd_3384_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_snd_3384_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3396_ = v_snd_3384_;
v_isShared_3397_ = v_isSharedCheck_3864_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3393_);
lean_dec(v_snd_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3864_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; lean_object* v___y_3403_; uint8_t v_anyFailed_3404_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; uint8_t v_anyUnlocated_3474_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; uint8_t v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v_a_3484_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___x_3505_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; uint8_t v___y_3520_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; uint8_t v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3637_; uint8_t v___y_3638_; uint8_t v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3681_; lean_object* v___y_3682_; uint8_t v___y_3683_; lean_object* v___y_3684_; uint8_t v___y_3685_; lean_object* v___y_3686_; uint8_t v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; uint8_t v___y_3691_; lean_object* v___y_3692_; uint8_t v___y_3693_; uint8_t v___y_3694_; lean_object* v___y_3716_; lean_object* v___y_3717_; uint8_t v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; uint8_t v___y_3721_; uint8_t v___y_3722_; lean_object* v___y_3723_; lean_object* v_records_3724_; uint8_t v_anyUnlocated_3725_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; uint8_t v___y_3758_; uint8_t v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3795_; lean_object* v___y_3796_; uint8_t v___y_3797_; uint8_t v___y_3798_; lean_object* v___y_3799_; uint8_t v___y_3820_; 
v___x_3505_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
if (v___x_3382_ == 0)
{
uint8_t v___x_3860_; 
v___x_3860_ = 2;
v___y_3820_ = v___x_3860_;
goto v___jp_3819_;
}
else
{
uint8_t v_recordExceptions_3861_; 
v_recordExceptions_3861_ = lean_ctor_get_uint8(v_args_3329_, sizeof(void*)*3 + 1);
if (v_recordExceptions_3861_ == 0)
{
uint8_t v___x_3862_; 
v___x_3862_ = 0;
v___y_3820_ = v___x_3862_;
goto v___jp_3819_;
}
else
{
uint8_t v___x_3863_; 
v___x_3863_ = 1;
v___y_3820_ = v___x_3863_;
goto v___jp_3819_;
}
}
v___jp_3398_:
{
lean_object* v___x_3405_; 
lean_inc(v___x_3330_);
v___x_3405_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_3329_, v___y_3403_, v___x_3330_, v___y_3400_, v___y_3401_, v_snd_3394_);
lean_dec_ref(v___y_3403_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v_outcome_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v_outcome_3407_ = lean_ctor_get(v_a_3406_, 0);
if (lean_obj_tag(v_outcome_3407_) == 0)
{
uint8_t v_failed_3408_; 
v_failed_3408_ = lean_ctor_get_uint8(v_outcome_3407_, 0);
if (v_failed_3408_ == 0)
{
lean_object* v_checkedModules_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v_checkedModules_3409_ = lean_ctor_get(v_a_3406_, 1);
lean_inc(v_checkedModules_3409_);
lean_dec(v_a_3406_);
v___x_3410_ = lean_box(v___y_3402_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_checkedModules_3409_);
lean_ctor_set(v___x_3396_, 0, v___x_3410_);
v___x_3412_ = v___x_3396_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_checkedModules_3409_);
v___x_3412_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3414_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3412_);
lean_ctor_set(v___x_3391_, 0, v___y_3399_);
v___x_3414_ = v___x_3391_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___y_3399_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_box(v_anyFailed_3404_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3414_);
lean_ctor_set(v___x_3387_, 0, v___x_3415_);
v___x_3417_ = v___x_3387_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3414_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
v_a_3337_ = v___x_3417_;
goto v___jp_3336_;
}
}
}
}
else
{
lean_object* v_checkedModules_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v_checkedModules_3421_ = lean_ctor_get(v_a_3406_, 1);
lean_inc(v_checkedModules_3421_);
lean_dec(v_a_3406_);
v___x_3422_ = lean_box(v___y_3402_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_checkedModules_3421_);
lean_ctor_set(v___x_3396_, 0, v___x_3422_);
v___x_3424_ = v___x_3396_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_checkedModules_3421_);
v___x_3424_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3424_);
lean_ctor_set(v___x_3391_, 0, v___y_3399_);
v___x_3426_ = v___x_3391_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___y_3399_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_box(v_anyUnlocated_3352_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3426_);
lean_ctor_set(v___x_3387_, 0, v___x_3427_);
v___x_3429_ = v___x_3387_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3426_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
v_a_3337_ = v___x_3429_;
goto v___jp_3336_;
}
}
}
}
}
else
{
lean_object* v_checkedModules_3433_; lean_object* v_records_3434_; uint8_t v_unlocated_3435_; lean_object* v___x_3436_; 
lean_inc_ref(v_outcome_3407_);
v_checkedModules_3433_ = lean_ctor_get(v_a_3406_, 1);
lean_inc(v_checkedModules_3433_);
lean_dec(v_a_3406_);
v_records_3434_ = lean_ctor_get(v_outcome_3407_, 0);
lean_inc_ref(v_records_3434_);
v_unlocated_3435_ = lean_ctor_get_uint8(v_outcome_3407_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_3407_, 1);
v___x_3436_ = l_Array_append___redArg(v___y_3399_, v_records_3434_);
lean_dec_ref(v_records_3434_);
if (v_unlocated_3435_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_box(v___y_3402_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_checkedModules_3433_);
lean_ctor_set(v___x_3396_, 0, v___x_3437_);
v___x_3439_ = v___x_3396_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_checkedModules_3433_);
v___x_3439_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3439_);
lean_ctor_set(v___x_3391_, 0, v___x_3436_);
v___x_3441_ = v___x_3391_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_box(v_anyFailed_3404_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3441_);
lean_ctor_set(v___x_3387_, 0, v___x_3442_);
v___x_3444_ = v___x_3387_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3441_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3337_ = v___x_3444_;
goto v___jp_3336_;
}
}
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3448_ = lean_box(v_anyUnlocated_3352_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_checkedModules_3433_);
lean_ctor_set(v___x_3396_, 0, v___x_3448_);
v___x_3450_ = v___x_3396_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_checkedModules_3433_);
v___x_3450_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3450_);
lean_ctor_set(v___x_3391_, 0, v___x_3436_);
v___x_3452_ = v___x_3391_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3453_ = lean_box(v_anyFailed_3404_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3452_);
lean_ctor_set(v___x_3387_, 0, v___x_3453_);
v___x_3455_ = v___x_3387_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3452_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v_a_3337_ = v___x_3455_;
goto v___jp_3336_;
}
}
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___y_3399_);
lean_del_object(v___x_3396_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v___x_3330_);
v_a_3459_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3405_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3405_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
v___jp_3467_:
{
if (v___y_3470_ == 0)
{
if (v___y_3473_ == 0)
{
uint8_t v___x_3475_; 
v___x_3475_ = lean_unbox(v_fst_3385_);
lean_dec(v_fst_3385_);
v___y_3399_ = v___y_3468_;
v___y_3400_ = v___y_3469_;
v___y_3401_ = v___y_3471_;
v___y_3402_ = v_anyUnlocated_3474_;
v___y_3403_ = v___y_3472_;
v_anyFailed_3404_ = v___x_3475_;
goto v___jp_3398_;
}
else
{
lean_dec(v_fst_3385_);
v___y_3399_ = v___y_3468_;
v___y_3400_ = v___y_3469_;
v___y_3401_ = v___y_3471_;
v___y_3402_ = v_anyUnlocated_3474_;
v___y_3403_ = v___y_3472_;
v_anyFailed_3404_ = v_anyUnlocated_3352_;
goto v___jp_3398_;
}
}
else
{
lean_dec(v_fst_3385_);
v___y_3399_ = v___y_3468_;
v___y_3400_ = v___y_3469_;
v___y_3401_ = v___y_3471_;
v___y_3402_ = v_anyUnlocated_3474_;
v___y_3403_ = v___y_3472_;
v_anyFailed_3404_ = v_anyUnlocated_3352_;
goto v___jp_3398_;
}
}
v___jp_3476_:
{
lean_object* v___x_3485_; lean_object* v_snd_3486_; lean_object* v_fst_3487_; lean_object* v_fst_3488_; lean_object* v_snd_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3485_ = lean_st_ref_get(v___y_3478_);
lean_dec(v___y_3478_);
lean_dec(v___x_3485_);
v_snd_3486_ = lean_ctor_get(v_a_3484_, 1);
lean_inc(v_snd_3486_);
v_fst_3487_ = lean_ctor_get(v_a_3484_, 0);
lean_inc(v_fst_3487_);
lean_dec_ref(v_a_3484_);
v_fst_3488_ = lean_ctor_get(v_snd_3486_, 0);
lean_inc(v_fst_3488_);
v_snd_3489_ = lean_ctor_get(v_snd_3486_, 1);
lean_inc(v_snd_3489_);
lean_dec(v_snd_3486_);
v___x_3490_ = l_Array_append___redArg(v___y_3483_, v_fst_3488_);
lean_dec(v_fst_3488_);
v___x_3491_ = lean_unbox(v_snd_3489_);
lean_dec(v_snd_3489_);
if (v___x_3491_ == 0)
{
uint8_t v___x_3492_; 
v___x_3492_ = lean_unbox(v_fst_3487_);
lean_dec(v_fst_3487_);
v___y_3468_ = v___x_3490_;
v___y_3469_ = v___y_3477_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3479_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v___x_3492_;
v_anyUnlocated_3474_ = v___y_3481_;
goto v___jp_3467_;
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_unbox(v_fst_3487_);
lean_dec(v_fst_3487_);
v___y_3468_ = v___x_3490_;
v___y_3469_ = v___y_3477_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3479_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v___x_3493_;
v_anyUnlocated_3474_ = v_anyUnlocated_3352_;
goto v___jp_3467_;
}
}
v___jp_3494_:
{
if (lean_obj_tag(v___y_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___y_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___y_3502_, 1);
v___y_3477_ = v___y_3496_;
v___y_3478_ = v___y_3495_;
v___y_3479_ = v___y_3498_;
v___y_3480_ = v___y_3497_;
v___y_3481_ = v___y_3499_;
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3501_;
v_a_3484_ = v_a_3503_;
goto v___jp_3476_;
}
else
{
lean_object* v_a_3504_; 
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3504_ = lean_ctor_get(v___y_3502_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___y_3502_, 1);
v_a_3354_ = v_a_3504_;
goto v___jp_3353_;
}
}
v___jp_3506_:
{
if (v___y_3519_ == 0)
{
lean_del_object(v___x_3380_);
if (v___y_3520_ == 0)
{
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
if (v___y_3510_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__4));
lean_inc(v_a_3372_);
v___x_3522_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3372_, v_anyUnlocated_3352_);
v___x_3523_ = lean_string_append(v___x_3521_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5));
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
v___x_3526_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3505_, v_anyFailed_3351_, v___y_3520_, v_a_3527_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
v___y_3495_ = v___y_3509_;
v___y_3496_ = v___y_3517_;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3515_;
v___y_3501_ = v___y_3516_;
v___y_3502_ = v___x_3528_;
goto v___jp_3494_;
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3529_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3531_ = v___x_3526_;
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3526_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_io_error_to_string(v_a_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 3);
lean_ctor_set(v___x_3531_, 0, v___x_3533_);
v___x_3535_ = v___x_3531_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_MessageData_ofFormat(v___x_3535_);
v_msg_3342_ = v___x_3536_;
goto v___jp_3341_;
}
}
}
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_box(0);
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3505_, v_anyFailed_3351_, v___y_3520_, v___x_3539_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
v___y_3495_ = v___y_3509_;
v___y_3496_ = v___y_3517_;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3515_;
v___y_3501_ = v___y_3516_;
v___y_3502_ = v___x_3540_;
goto v___jp_3494_;
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; 
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__6));
lean_inc(v_a_3372_);
v___x_3542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3372_, v___y_3520_);
v___x_3543_ = lean_string_append(v___x_3541_, v___x_3542_);
lean_dec_ref(v___x_3542_);
v___x_3544_ = 1;
v___x_3545_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_3518_, v___y_3513_, v_anyUnlocated_3352_, v___x_3543_, v___x_3544_, v___y_3514_, v_anyUnlocated_3352_, v___y_3507_, v___y_3508_);
lean_dec_ref(v___y_3513_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = l_Lean_MessageData_toString(v_a_3546_);
v___x_3548_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_3547_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3505_, v_anyFailed_3351_, v___y_3520_, v_a_3549_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
v___y_3495_ = v___y_3509_;
v___y_3496_ = v___y_3517_;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3515_;
v___y_3501_ = v___y_3516_;
v___y_3502_ = v___x_3550_;
goto v___jp_3494_;
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3551_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3553_ = v___x_3548_;
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3548_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3555_ = lean_io_error_to_string(v_a_3551_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 3);
lean_ctor_set(v___x_3553_, 0, v___x_3555_);
v___x_3557_ = v___x_3553_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_MessageData_ofFormat(v___x_3557_);
v_msg_3342_ = v___x_3558_;
goto v___jp_3341_;
}
}
}
}
else
{
lean_object* v_a_3561_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3561_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3545_, 1);
v_a_3354_ = v_a_3561_;
goto v___jp_3353_;
}
}
}
else
{
lean_object* v___x_3562_; lean_object* v_env_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
v___x_3562_ = lean_st_ref_get(v___y_3508_);
v_env_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc_ref(v_env_3563_);
lean_dec(v___x_3562_);
v___x_3564_ = l_Lean_Environment_mainModule(v_env_3563_);
lean_dec_ref(v_env_3563_);
v___x_3565_ = lean_box(v_anyFailed_3351_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v___x_3565_);
lean_ctor_set(v___x_3380_, 0, v___x_3505_);
v___x_3567_ = v___x_3380_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
size_t v_sz_3568_; size_t v___x_3569_; lean_object* v___x_3570_; 
v_sz_3568_ = lean_array_size(v___y_3518_);
v___x_3569_ = ((size_t)0ULL);
lean_inc(v___x_3330_);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___y_3519_, v___x_3330_, v___x_3564_, v___y_3518_, v_sz_3568_, v___x_3569_, v___x_3567_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec_ref(v___y_3518_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v_fst_3572_; lean_object* v_snd_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3582_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v_fst_3572_ = lean_ctor_get(v_a_3571_, 0);
v_snd_3573_ = lean_ctor_get(v_a_3571_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3571_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3575_ = v_a_3571_;
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_snd_3573_);
lean_inc(v_fst_3572_);
lean_dec(v_a_3571_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_fst_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_snd_3573_);
v___x_3578_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_box(v___y_3520_);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___x_3578_);
v___y_3477_ = v___y_3517_;
v___y_3478_ = v___y_3509_;
v___y_3479_ = v___y_3511_;
v___y_3480_ = v___y_3510_;
v___y_3481_ = v___y_3512_;
v___y_3482_ = v___y_3515_;
v___y_3483_ = v___y_3516_;
v_a_3484_ = v___x_3580_;
goto v___jp_3476_;
}
}
}
else
{
lean_object* v_a_3583_; 
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec(v___y_3509_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3583_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3570_, 1);
v_a_3354_ = v_a_3583_;
goto v___jp_3353_;
}
}
}
}
v___jp_3585_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_3597_, v___y_3586_, v___y_3589_);
lean_dec(v___y_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_array_get_size(v_a_3599_);
v___x_3601_ = lean_nat_dec_eq(v___x_3600_, v___x_3350_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Linter_EnvLinter_lintCore(v___y_3593_, v_a_3599_, v___y_3586_, v___y_3589_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = lean_array_get_size(v_a_3603_);
v___x_3605_ = lean_nat_dec_lt(v___x_3350_, v___x_3604_);
if (v___x_3605_ == 0)
{
v___y_3507_ = v___y_3586_;
v___y_3508_ = v___y_3589_;
v___y_3509_ = v___y_3588_;
v___y_3510_ = v___y_3591_;
v___y_3511_ = v___y_3590_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___x_3600_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3587_;
v___y_3518_ = v_a_3603_;
v___y_3519_ = v___y_3594_;
v___y_3520_ = v___x_3601_;
goto v___jp_3506_;
}
else
{
if (v___x_3605_ == 0)
{
v___y_3507_ = v___y_3586_;
v___y_3508_ = v___y_3589_;
v___y_3509_ = v___y_3588_;
v___y_3510_ = v___y_3591_;
v___y_3511_ = v___y_3590_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___x_3600_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3587_;
v___y_3518_ = v_a_3603_;
v___y_3519_ = v___y_3594_;
v___y_3520_ = v___x_3601_;
goto v___jp_3506_;
}
else
{
size_t v___x_3606_; size_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3606_ = ((size_t)0ULL);
v___x_3607_ = lean_usize_of_nat(v___x_3604_);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(v_a_3603_, v___x_3606_, v___x_3607_);
v___y_3507_ = v___y_3586_;
v___y_3508_ = v___y_3589_;
v___y_3509_ = v___y_3588_;
v___y_3510_ = v___y_3591_;
v___y_3511_ = v___y_3590_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___x_3600_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3587_;
v___y_3518_ = v_a_3603_;
v___y_3519_ = v___y_3594_;
v___y_3520_ = v___x_3608_;
goto v___jp_3506_;
}
}
}
else
{
lean_object* v_a_3609_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3609_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3602_, 1);
v_a_3354_ = v_a_3609_;
goto v___jp_3353_;
}
}
else
{
lean_dec(v_a_3599_);
lean_dec_ref(v___y_3593_);
lean_del_object(v___x_3380_);
if (v___y_3594_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__7));
lean_inc(v_a_3372_);
v___x_3611_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3372_, v___x_3601_);
v___x_3612_ = lean_string_append(v___x_3610_, v___x_3611_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5));
v___x_3614_ = lean_string_append(v___x_3612_, v___x_3613_);
v___x_3615_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3614_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_3505_, v_anyFailed_3351_, v_a_3616_, v___y_3586_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3586_);
v___y_3495_ = v___y_3588_;
v___y_3496_ = v___y_3587_;
v___y_3497_ = v___y_3591_;
v___y_3498_ = v___y_3590_;
v___y_3499_ = v___y_3592_;
v___y_3500_ = v___y_3595_;
v___y_3501_ = v___y_3596_;
v___y_3502_ = v___x_3617_;
goto v___jp_3494_;
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3627_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_dec(v___x_3330_);
v_a_3618_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3620_ = v___x_3615_;
v_isShared_3621_ = v_isSharedCheck_3627_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3615_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3627_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = lean_io_error_to_string(v_a_3618_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 3);
lean_ctor_set(v___x_3620_, 0, v___x_3622_);
v___x_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_MessageData_ofFormat(v___x_3624_);
v_msg_3342_ = v___x_3625_;
goto v___jp_3341_;
}
}
}
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_box(0);
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_3505_, v_anyFailed_3351_, v___x_3628_, v___y_3586_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3586_);
v___y_3495_ = v___y_3588_;
v___y_3496_ = v___y_3587_;
v___y_3497_ = v___y_3591_;
v___y_3498_ = v___y_3590_;
v___y_3499_ = v___y_3592_;
v___y_3500_ = v___y_3595_;
v___y_3501_ = v___y_3596_;
v___y_3502_ = v___x_3629_;
goto v___jp_3494_;
}
}
}
else
{
lean_object* v_a_3630_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3630_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3598_, 1);
v_a_3354_ = v_a_3630_;
goto v___jp_3353_;
}
}
v___jp_3631_:
{
lean_object* v_fileName_3645_; lean_object* v_fileMap_3646_; lean_object* v_currRecDepth_3647_; lean_object* v_ref_3648_; lean_object* v_currNamespace_3649_; lean_object* v_openDecls_3650_; lean_object* v_initHeartbeats_3651_; lean_object* v_maxHeartbeats_3652_; lean_object* v_quotContext_3653_; lean_object* v_currMacroScope_3654_; lean_object* v_cancelTk_x3f_3655_; uint8_t v_suppressElabErrors_3656_; lean_object* v_inheritedTraceOptions_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3677_; 
v_fileName_3645_ = lean_ctor_get(v___y_3643_, 0);
v_fileMap_3646_ = lean_ctor_get(v___y_3643_, 1);
v_currRecDepth_3647_ = lean_ctor_get(v___y_3643_, 3);
v_ref_3648_ = lean_ctor_get(v___y_3643_, 5);
v_currNamespace_3649_ = lean_ctor_get(v___y_3643_, 6);
v_openDecls_3650_ = lean_ctor_get(v___y_3643_, 7);
v_initHeartbeats_3651_ = lean_ctor_get(v___y_3643_, 8);
v_maxHeartbeats_3652_ = lean_ctor_get(v___y_3643_, 9);
v_quotContext_3653_ = lean_ctor_get(v___y_3643_, 10);
v_currMacroScope_3654_ = lean_ctor_get(v___y_3643_, 11);
v_cancelTk_x3f_3655_ = lean_ctor_get(v___y_3643_, 12);
v_suppressElabErrors_3656_ = lean_ctor_get_uint8(v___y_3643_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3657_ = lean_ctor_get(v___y_3643_, 13);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___y_3643_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; lean_object* v_unused_3679_; 
v_unused_3678_ = lean_ctor_get(v___y_3643_, 4);
lean_dec(v_unused_3678_);
v_unused_3679_ = lean_ctor_get(v___y_3643_, 2);
lean_dec(v_unused_3679_);
v___x_3659_ = v___y_3643_;
v_isShared_3660_ = v_isSharedCheck_3677_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_inheritedTraceOptions_3657_);
lean_inc(v_cancelTk_x3f_3655_);
lean_inc(v_currMacroScope_3654_);
lean_inc(v_quotContext_3653_);
lean_inc(v_maxHeartbeats_3652_);
lean_inc(v_initHeartbeats_3651_);
lean_inc(v_openDecls_3650_);
lean_inc(v_currNamespace_3649_);
lean_inc(v_ref_3648_);
lean_inc(v_currRecDepth_3647_);
lean_inc(v_fileMap_3646_);
lean_inc(v_fileName_3645_);
lean_dec(v___y_3643_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3677_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_3636_, v___y_3644_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3675_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3675_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3675_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3666_ = l_Lean_maxRecDepth;
v___x_3667_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_3634_, v___x_3666_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 4, v___x_3667_);
lean_ctor_set(v___x_3659_, 2, v___y_3634_);
v___x_3669_ = v___x_3659_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_fileName_3645_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_fileMap_3646_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v___y_3634_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_currRecDepth_3647_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_ref_3648_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_currNamespace_3649_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_openDecls_3650_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_initHeartbeats_3651_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_maxHeartbeats_3652_);
lean_ctor_set(v_reuseFailAlloc_3674_, 10, v_quotContext_3653_);
lean_ctor_set(v_reuseFailAlloc_3674_, 11, v_currMacroScope_3654_);
lean_ctor_set(v_reuseFailAlloc_3674_, 12, v_cancelTk_x3f_3655_);
lean_ctor_set(v_reuseFailAlloc_3674_, 13, v_inheritedTraceOptions_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*14 + 1, v_suppressElabErrors_3656_);
v___x_3669_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_ctor_set_uint8(v___x_3669_, sizeof(void*)*14, v___y_3638_);
if (v___y_3639_ == 0)
{
lean_object* v___x_3670_; 
lean_del_object(v___x_3664_);
v___x_3670_ = lean_box(0);
v___y_3586_ = v___x_3669_;
v___y_3587_ = v___y_3633_;
v___y_3588_ = v___y_3632_;
v___y_3589_ = v___y_3644_;
v___y_3590_ = v___y_3636_;
v___y_3591_ = v___y_3635_;
v___y_3592_ = v___y_3637_;
v___y_3593_ = v_a_3662_;
v___y_3594_ = v___y_3640_;
v___y_3595_ = v___y_3641_;
v___y_3596_ = v___y_3642_;
v___y_3597_ = v___x_3670_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3672_; 
lean_inc_ref(v___y_3641_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 1);
lean_ctor_set(v___x_3664_, 0, v___y_3641_);
v___x_3672_ = v___x_3664_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___y_3641_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
v___y_3586_ = v___x_3669_;
v___y_3587_ = v___y_3633_;
v___y_3588_ = v___y_3632_;
v___y_3589_ = v___y_3644_;
v___y_3590_ = v___y_3636_;
v___y_3591_ = v___y_3635_;
v___y_3592_ = v___y_3637_;
v___y_3593_ = v_a_3662_;
v___y_3594_ = v___y_3640_;
v___y_3595_ = v___y_3641_;
v___y_3596_ = v___y_3642_;
v___y_3597_ = v___x_3672_;
goto v___jp_3585_;
}
}
}
}
}
else
{
lean_object* v_a_3676_; 
lean_del_object(v___x_3659_);
lean_dec_ref(v_inheritedTraceOptions_3657_);
lean_dec(v_cancelTk_x3f_3655_);
lean_dec(v_currMacroScope_3654_);
lean_dec(v_quotContext_3653_);
lean_dec(v_maxHeartbeats_3652_);
lean_dec(v_initHeartbeats_3651_);
lean_dec(v_openDecls_3650_);
lean_dec(v_currNamespace_3649_);
lean_dec(v_ref_3648_);
lean_dec(v_currRecDepth_3647_);
lean_dec_ref(v_fileMap_3646_);
lean_dec_ref(v_fileName_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3676_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v___x_3661_, 1);
v_a_3354_ = v_a_3676_;
goto v___jp_3353_;
}
}
}
v___jp_3680_:
{
uint8_t v___x_3695_; 
v___x_3695_ = lean_bool_not(v___y_3694_);
if (v___x_3695_ == 0)
{
lean_inc(v___y_3681_);
v___y_3632_ = v___y_3681_;
v___y_3633_ = v___y_3690_;
v___y_3634_ = v___y_3682_;
v___y_3635_ = v___y_3683_;
v___y_3636_ = v___y_3684_;
v___y_3637_ = v___y_3685_;
v___y_3638_ = v___y_3691_;
v___y_3639_ = v___y_3687_;
v___y_3640_ = v___y_3693_;
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3689_;
v___y_3643_ = v___y_3692_;
v___y_3644_ = v___y_3681_;
goto v___jp_3631_;
}
else
{
lean_object* v___x_3696_; lean_object* v_env_3697_; lean_object* v_nextMacroScope_3698_; lean_object* v_ngen_3699_; lean_object* v_auxDeclNGen_3700_; lean_object* v_traceState_3701_; lean_object* v_messages_3702_; lean_object* v_infoState_3703_; lean_object* v_snapshotTasks_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3713_; 
v___x_3696_ = lean_st_ref_take(v___y_3681_);
v_env_3697_ = lean_ctor_get(v___x_3696_, 0);
v_nextMacroScope_3698_ = lean_ctor_get(v___x_3696_, 1);
v_ngen_3699_ = lean_ctor_get(v___x_3696_, 2);
v_auxDeclNGen_3700_ = lean_ctor_get(v___x_3696_, 3);
v_traceState_3701_ = lean_ctor_get(v___x_3696_, 4);
v_messages_3702_ = lean_ctor_get(v___x_3696_, 6);
v_infoState_3703_ = lean_ctor_get(v___x_3696_, 7);
v_snapshotTasks_3704_ = lean_ctor_get(v___x_3696_, 8);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; 
v_unused_3714_ = lean_ctor_get(v___x_3696_, 5);
lean_dec(v_unused_3714_);
v___x_3706_ = v___x_3696_;
v_isShared_3707_ = v_isSharedCheck_3713_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_snapshotTasks_3704_);
lean_inc(v_infoState_3703_);
lean_inc(v_messages_3702_);
lean_inc(v_traceState_3701_);
lean_inc(v_auxDeclNGen_3700_);
lean_inc(v_ngen_3699_);
lean_inc(v_nextMacroScope_3698_);
lean_inc(v_env_3697_);
lean_dec(v___x_3696_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3713_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3708_ = l_Lean_Kernel_enableDiag(v_env_3697_, v___y_3691_);
lean_inc_ref(v___y_3686_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 5, v___y_3686_);
lean_ctor_set(v___x_3706_, 0, v___x_3708_);
v___x_3710_ = v___x_3706_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_nextMacroScope_3698_);
lean_ctor_set(v_reuseFailAlloc_3712_, 2, v_ngen_3699_);
lean_ctor_set(v_reuseFailAlloc_3712_, 3, v_auxDeclNGen_3700_);
lean_ctor_set(v_reuseFailAlloc_3712_, 4, v_traceState_3701_);
lean_ctor_set(v_reuseFailAlloc_3712_, 5, v___y_3686_);
lean_ctor_set(v_reuseFailAlloc_3712_, 6, v_messages_3702_);
lean_ctor_set(v_reuseFailAlloc_3712_, 7, v_infoState_3703_);
lean_ctor_set(v_reuseFailAlloc_3712_, 8, v_snapshotTasks_3704_);
v___x_3710_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_st_ref_set(v___y_3681_, v___x_3710_);
lean_inc(v___y_3681_);
v___y_3632_ = v___y_3681_;
v___y_3633_ = v___y_3690_;
v___y_3634_ = v___y_3682_;
v___y_3635_ = v___y_3683_;
v___y_3636_ = v___y_3684_;
v___y_3637_ = v___y_3685_;
v___y_3638_ = v___y_3691_;
v___y_3639_ = v___y_3687_;
v___y_3640_ = v___y_3693_;
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3689_;
v___y_3643_ = v___y_3692_;
v___y_3644_ = v___y_3681_;
goto v___jp_3631_;
}
}
}
}
v___jp_3715_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_env_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; uint8_t v___x_3752_; 
v___x_3726_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_3727_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_3728_ = lean_io_get_num_heartbeats();
v___x_3729_ = l_Lean_firstFrontendMacroScope;
v___x_3730_ = lean_unsigned_to_nat(1u);
v___x_3731_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_3732_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_3733_ = lean_box(0);
lean_inc_n(v___y_3720_, 2);
v___x_3734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3734_, 0, v___y_3720_);
lean_ctor_set(v___x_3734_, 1, v___x_3730_);
lean_ctor_set(v___x_3734_, 2, v___x_3733_);
v___x_3735_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_3736_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
lean_inc_ref(v___y_3717_);
v___x_3737_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3737_, 0, v___y_3717_);
lean_ctor_set(v___x_3737_, 1, v___x_3731_);
lean_ctor_set(v___x_3737_, 2, v___x_3732_);
lean_ctor_set(v___x_3737_, 3, v___x_3734_);
lean_ctor_set(v___x_3737_, 4, v___x_3735_);
lean_ctor_set(v___x_3737_, 5, v___x_3726_);
lean_ctor_set(v___x_3737_, 6, v___x_3727_);
lean_ctor_set(v___x_3737_, 7, v___x_3736_);
lean_ctor_set(v___x_3737_, 8, v___x_3505_);
v___x_3738_ = lean_st_mk_ref(v___x_3737_);
v___x_3739_ = l_Lean_inheritedTraceOptions;
v___x_3740_ = lean_st_ref_get(v___x_3739_);
v___x_3741_ = lean_st_ref_get(v___x_3738_);
v___x_3742_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_3743_ = l_Lean_instInhabitedFileMap_default;
v___x_3744_ = lean_unsigned_to_nat(1000u);
v___x_3745_ = lean_box(0);
v___x_3746_ = l_Lean_Core_getMaxHeartbeats(v___y_3716_);
v___x_3747_ = lean_box(0);
lean_inc_ref(v___y_3716_);
v___x_3748_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3748_, 0, v___x_3742_);
lean_ctor_set(v___x_3748_, 1, v___x_3743_);
lean_ctor_set(v___x_3748_, 2, v___y_3716_);
lean_ctor_set(v___x_3748_, 3, v___x_3350_);
lean_ctor_set(v___x_3748_, 4, v___x_3744_);
lean_ctor_set(v___x_3748_, 5, v___x_3745_);
lean_ctor_set(v___x_3748_, 6, v___y_3720_);
lean_ctor_set(v___x_3748_, 7, v___x_3733_);
lean_ctor_set(v___x_3748_, 8, v___x_3728_);
lean_ctor_set(v___x_3748_, 9, v___x_3746_);
lean_ctor_set(v___x_3748_, 10, v___y_3720_);
lean_ctor_set(v___x_3748_, 11, v___x_3729_);
lean_ctor_set(v___x_3748_, 12, v___x_3747_);
lean_ctor_set(v___x_3748_, 13, v___x_3740_);
lean_ctor_set_uint8(v___x_3748_, sizeof(void*)*14, v_anyFailed_3351_);
lean_ctor_set_uint8(v___x_3748_, sizeof(void*)*14 + 1, v_anyFailed_3351_);
v_env_3749_ = lean_ctor_get(v___x_3741_, 0);
lean_inc_ref(v_env_3749_);
lean_dec(v___x_3741_);
v___x_3750_ = l_Lean_diagnostics;
v___x_3751_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_3716_, v___x_3750_);
v___x_3752_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3749_);
lean_dec_ref(v_env_3749_);
if (v___x_3752_ == 0)
{
if (v___x_3751_ == 0)
{
v___y_3681_ = v___x_3738_;
v___y_3682_ = v___y_3716_;
v___y_3683_ = v___y_3718_;
v___y_3684_ = v___y_3719_;
v___y_3685_ = v_anyUnlocated_3725_;
v___y_3686_ = v___x_3726_;
v___y_3687_ = v___y_3721_;
v___y_3688_ = v___y_3723_;
v___y_3689_ = v_records_3724_;
v___y_3690_ = v___y_3717_;
v___y_3691_ = v___x_3751_;
v___y_3692_ = v___x_3748_;
v___y_3693_ = v___y_3722_;
v___y_3694_ = v___x_3369_;
goto v___jp_3680_;
}
else
{
v___y_3681_ = v___x_3738_;
v___y_3682_ = v___y_3716_;
v___y_3683_ = v___y_3718_;
v___y_3684_ = v___y_3719_;
v___y_3685_ = v_anyUnlocated_3725_;
v___y_3686_ = v___x_3726_;
v___y_3687_ = v___y_3721_;
v___y_3688_ = v___y_3723_;
v___y_3689_ = v_records_3724_;
v___y_3690_ = v___y_3717_;
v___y_3691_ = v___x_3751_;
v___y_3692_ = v___x_3748_;
v___y_3693_ = v___y_3722_;
v___y_3694_ = v___x_3752_;
goto v___jp_3680_;
}
}
else
{
v___y_3681_ = v___x_3738_;
v___y_3682_ = v___y_3716_;
v___y_3683_ = v___y_3718_;
v___y_3684_ = v___y_3719_;
v___y_3685_ = v_anyUnlocated_3725_;
v___y_3686_ = v___x_3726_;
v___y_3687_ = v___y_3721_;
v___y_3688_ = v___y_3723_;
v___y_3689_ = v_records_3724_;
v___y_3690_ = v___y_3717_;
v___y_3691_ = v___x_3751_;
v___y_3692_ = v___x_3748_;
v___y_3693_ = v___y_3722_;
v___y_3694_ = v___x_3751_;
goto v___jp_3680_;
}
}
v___jp_3753_:
{
lean_object* v___x_3762_; uint8_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3762_ = lean_array_get_size(v___y_3761_);
v___x_3763_ = lean_nat_dec_eq(v___x_3762_, v___x_3350_);
v___x_3764_ = lean_bool_not(v___x_3763_);
if (v___y_3759_ == 0)
{
lean_object* v___x_3765_; size_t v_sz_3766_; size_t v___x_3767_; lean_object* v___x_3768_; 
v___x_3765_ = lean_box(0);
v_sz_3766_ = lean_array_size(v___y_3761_);
v___x_3767_ = ((size_t)0ULL);
v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(v___x_3328_, v___y_3761_, v_sz_3766_, v___x_3767_, v___x_3765_);
lean_dec_ref(v___y_3761_);
if (lean_obj_tag(v___x_3768_) == 0)
{
uint8_t v___x_3769_; 
lean_dec_ref_known(v___x_3768_, 1);
v___x_3769_ = lean_unbox(v_fst_3393_);
lean_dec(v_fst_3393_);
v___y_3716_ = v___y_3755_;
v___y_3717_ = v___y_3754_;
v___y_3718_ = v___x_3764_;
v___y_3719_ = v___y_3756_;
v___y_3720_ = v___y_3757_;
v___y_3721_ = v___y_3758_;
v___y_3722_ = v___y_3759_;
v___y_3723_ = v___y_3760_;
v_records_3724_ = v_fst_3389_;
v_anyUnlocated_3725_ = v___x_3769_;
goto v___jp_3715_;
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec(v_fst_3389_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3770_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3768_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3768_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v___x_3778_; size_t v_sz_3779_; size_t v___x_3780_; lean_object* v___x_3781_; 
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_fst_3389_);
lean_ctor_set(v___x_3778_, 1, v_fst_3393_);
v_sz_3779_ = lean_array_size(v___y_3761_);
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___y_3759_, v___y_3761_, v_sz_3779_, v___x_3780_, v___x_3778_);
lean_dec_ref(v___y_3761_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v_fst_3783_; lean_object* v_snd_3784_; uint8_t v___x_3785_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v_fst_3783_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_fst_3783_);
v_snd_3784_ = lean_ctor_get(v_a_3782_, 1);
lean_inc(v_snd_3784_);
lean_dec(v_a_3782_);
v___x_3785_ = lean_unbox(v_snd_3784_);
lean_dec(v_snd_3784_);
v___y_3716_ = v___y_3755_;
v___y_3717_ = v___y_3754_;
v___y_3718_ = v___x_3764_;
v___y_3719_ = v___y_3756_;
v___y_3720_ = v___y_3757_;
v___y_3721_ = v___y_3758_;
v___y_3722_ = v___y_3759_;
v___y_3723_ = v___y_3760_;
v_records_3724_ = v_fst_3783_;
v_anyUnlocated_3725_ = v___x_3785_;
goto v___jp_3715_;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_del_object(v___x_3391_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3786_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3781_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3781_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3800_; lean_object* v_toEnvExtension_3801_; lean_object* v_asyncMode_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v_merged_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3817_; 
v___x_3800_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3801_ = lean_ctor_get(v___x_3800_, 0);
v_asyncMode_3802_ = lean_ctor_get(v_toEnvExtension_3801_, 2);
v___x_3803_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3804_ = lean_box(0);
lean_inc_ref(v___y_3796_);
v___x_3805_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3803_, v___x_3800_, v___y_3796_, v_asyncMode_3802_, v___x_3804_);
v_merged_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; 
v_unused_3818_ = lean_ctor_get(v___x_3805_, 1);
lean_dec(v_unused_3818_);
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_merged_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 1, v_merged_3806_);
lean_ctor_set(v___x_3808_, 0, v___y_3799_);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___y_3799_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_merged_3806_);
v___x_3811_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = l_Lean_Name_getRoot(v_a_3372_);
v___x_3813_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v___y_3796_, v___x_3812_);
if (v___y_3797_ == 0)
{
v___y_3754_ = v___y_3796_;
v___y_3755_ = v___y_3795_;
v___y_3756_ = v___x_3812_;
v___y_3757_ = v___x_3804_;
v___y_3758_ = v___y_3797_;
v___y_3759_ = v___y_3798_;
v___y_3760_ = v___x_3811_;
v___y_3761_ = v___x_3813_;
goto v___jp_3753_;
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_array_get_size(v___x_3813_);
v___x_3815_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(v___x_3811_, v___x_3813_, v___x_3350_, v___x_3814_);
lean_dec_ref(v___x_3813_);
v___y_3754_ = v___y_3796_;
v___y_3755_ = v___y_3795_;
v___y_3756_ = v___x_3812_;
v___y_3757_ = v___x_3804_;
v___y_3758_ = v___y_3797_;
v___y_3759_ = v___y_3798_;
v___y_3760_ = v___x_3811_;
v___y_3761_ = v___x_3815_;
goto v___jp_3753_;
}
}
}
}
v___jp_3819_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_compacted_region_free(v_snd_3378_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint32_t v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec_ref_known(v___x_3821_, 1);
lean_inc(v_a_3372_);
v___x_3822_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3822_, 0, v_a_3372_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*1, v_anyFailed_3351_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*1 + 1, v_anyUnlocated_3352_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*1 + 2, v_anyFailed_3351_);
v___x_3823_ = lean_unsigned_to_nat(2u);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___x_3825_ = lean_array_push(v___x_3824_, v___x_3822_);
v___x_3826_ = lean_array_push(v___x_3825_, v_envLinterModule_3368_);
v___x_3827_ = l_Lean_Options_empty;
v___x_3828_ = 1024;
v___x_3829_ = lean_box(1);
v___x_3830_ = l_Lean_importModules(v___x_3826_, v___x_3827_, v___x_3828_, v___x_3505_, v_anyFailed_3351_, v_anyUnlocated_3352_, v___y_3820_, v___x_3829_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v_linterOverrides_3832_; uint8_t v_lintOnly_3833_; uint8_t v_recordExceptions_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v_linterOverrides_3832_ = lean_ctor_get(v_args_3329_, 0);
v_lintOnly_3833_ = lean_ctor_get_uint8(v_args_3329_, sizeof(void*)*3);
v_recordExceptions_3834_ = lean_ctor_get_uint8(v_args_3329_, sizeof(void*)*3 + 1);
v___x_3835_ = lean_array_get_size(v_linterOverrides_3832_);
v___x_3836_ = lean_nat_dec_lt(v___x_3350_, v___x_3835_);
if (v___x_3836_ == 0)
{
v___y_3795_ = v___x_3827_;
v___y_3796_ = v_a_3831_;
v___y_3797_ = v_lintOnly_3833_;
v___y_3798_ = v_recordExceptions_3834_;
v___y_3799_ = v___x_3827_;
goto v___jp_3794_;
}
else
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_nat_dec_le(v___x_3835_, v___x_3835_);
if (v___x_3837_ == 0)
{
if (v___x_3836_ == 0)
{
v___y_3795_ = v___x_3827_;
v___y_3796_ = v_a_3831_;
v___y_3797_ = v_lintOnly_3833_;
v___y_3798_ = v_recordExceptions_3834_;
v___y_3799_ = v___x_3827_;
goto v___jp_3794_;
}
else
{
size_t v___x_3838_; size_t v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = ((size_t)0ULL);
v___x_3839_ = lean_usize_of_nat(v___x_3835_);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_linterOverrides_3832_, v___x_3838_, v___x_3839_, v___x_3827_);
v___y_3795_ = v___x_3827_;
v___y_3796_ = v_a_3831_;
v___y_3797_ = v_lintOnly_3833_;
v___y_3798_ = v_recordExceptions_3834_;
v___y_3799_ = v___x_3840_;
goto v___jp_3794_;
}
}
else
{
size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = ((size_t)0ULL);
v___x_3842_ = lean_usize_of_nat(v___x_3835_);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_linterOverrides_3832_, v___x_3841_, v___x_3842_, v___x_3827_);
v___y_3795_ = v___x_3827_;
v___y_3796_ = v_a_3831_;
v___y_3797_ = v_lintOnly_3833_;
v___y_3798_ = v_recordExceptions_3834_;
v___y_3799_ = v___x_3843_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec(v_fst_3389_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec(v___x_3330_);
v_a_3844_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3830_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3830_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3391_);
lean_dec(v_fst_3389_);
lean_del_object(v___x_3387_);
lean_dec(v_fst_3385_);
lean_del_object(v___x_3380_);
lean_dec_ref_known(v_envLinterModule_3368_, 1);
lean_dec(v___x_3330_);
v_a_3852_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3821_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3821_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
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
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec_ref_known(v_envLinterModule_3368_, 1);
lean_dec_ref(v_b_3334_);
lean_dec(v___x_3330_);
v_a_3870_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3375_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3375_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref_known(v_envLinterModule_3368_, 1);
lean_dec_ref(v_b_3334_);
lean_dec(v___x_3330_);
v_a_3878_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3373_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3373_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref_known(v_envLinterModule_3368_, 1);
lean_dec_ref(v_b_3334_);
lean_dec(v___x_3330_);
v_a_3886_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3371_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3371_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
v___jp_3336_:
{
size_t v___x_3338_; size_t v___x_3339_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3333_, v___x_3338_);
v_i_3333_ = v___x_3339_;
v_b_3334_ = v_a_3337_;
goto _start;
}
v___jp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = l_Lean_MessageData_toString(v_msg_3342_);
v___x_3344_ = lean_mk_io_user_error(v___x_3343_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
return v___x_3345_;
}
v___jp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_mk_io_user_error(v_a_3347_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
v___jp_3353_:
{
if (lean_obj_tag(v_a_3354_) == 0)
{
lean_object* v_msg_3355_; 
v_msg_3355_ = lean_ctor_get(v_a_3354_, 1);
lean_inc_ref(v_msg_3355_);
lean_dec_ref_known(v_a_3354_, 2);
v_msg_3342_ = v_msg_3355_;
goto v___jp_3341_;
}
else
{
lean_object* v_id_3356_; lean_object* v___x_3357_; 
v_id_3356_ = lean_ctor_get(v_a_3354_, 0);
lean_inc(v_id_3356_);
lean_dec_ref_known(v_a_3354_, 2);
v___x_3357_ = l_Lean_InternalExceptionId_getName(v_id_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v_id_3356_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_3360_ = l_Lean_Name_toString(v_a_3358_, v_anyUnlocated_3352_);
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
lean_dec_ref(v___x_3360_);
v_a_3347_ = v___x_3361_;
goto v___jp_3346_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref_known(v___x_3357_, 1);
v___x_3362_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_3363_ = l_Nat_reprFast(v_id_3356_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
v_a_3347_ = v___x_3366_;
goto v___jp_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___boxed(lean_object* v___x_3894_, lean_object* v_args_3895_, lean_object* v___x_3896_, lean_object* v_as_3897_, lean_object* v_sz_3898_, lean_object* v_i_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3898_);
lean_dec(v_sz_3898_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___x_3894_, v_args_3895_, v___x_3896_, v_as_3897_, v_sz_boxed_3902_, v_i_boxed_3903_, v_b_3900_);
lean_dec_ref(v_as_3897_);
lean_dec_ref(v_args_3895_);
lean_dec(v___x_3894_);
return v_res_3904_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = 0;
v___x_3907_ = lean_box_uint32(v___x_3906_);
return v___x_3907_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = 1;
v___x_3909_ = lean_box_uint32(v___x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_3910_){
_start:
{
lean_object* v_mods_3912_; uint8_t v_recordExceptions_3913_; lean_object* v_srcSearchPath_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v_anyFailed_3917_; 
v_mods_3912_ = lean_ctor_get(v_args_3910_, 1);
lean_inc_ref(v_mods_3912_);
v_recordExceptions_3913_ = lean_ctor_get_uint8(v_args_3910_, sizeof(void*)*3 + 1);
v_srcSearchPath_3914_ = lean_ctor_get(v_args_3910_, 2);
v___x_3915_ = lean_array_get_size(v_mods_3912_);
v___x_3916_ = lean_unsigned_to_nat(0u);
v_anyFailed_3917_ = lean_nat_dec_eq(v___x_3915_, v___x_3916_);
if (v_anyFailed_3917_ == 0)
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; size_t v_sz_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
lean_inc(v_srcSearchPath_3914_);
v___x_3920_ = l_List_appendTR___redArg(v_srcSearchPath_3914_, v_a_3919_);
v___x_3921_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_3922_ = l_Lean_NameSet_empty;
v___x_3923_ = lean_box(v_anyFailed_3917_);
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3922_);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3921_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = lean_box(v_anyFailed_3917_);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v___x_3925_);
v_sz_3928_ = lean_array_size(v_mods_3912_);
v___x_3929_ = ((size_t)0ULL);
v___x_3930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___x_3915_, v_args_3910_, v___x_3920_, v_mods_3912_, v_sz_3928_, v___x_3929_, v___x_3927_);
lean_dec_ref(v_mods_3912_);
lean_dec_ref(v_args_3910_);
if (lean_obj_tag(v___x_3930_) == 0)
{
if (v_recordExceptions_3913_ == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3945_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3945_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3945_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_fst_3935_; uint8_t v___x_3936_; 
v_fst_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_fst_3935_);
lean_dec(v_a_3931_);
v___x_3936_ = lean_unbox(v_fst_3935_);
lean_dec(v_fst_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3937_);
v___x_3939_ = v___x_3933_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3941_);
v___x_3943_ = v___x_3933_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v_snd_3947_; lean_object* v_fst_3948_; lean_object* v_snd_3949_; lean_object* v___x_3950_; 
v_a_3946_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3930_, 1);
v_snd_3947_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_snd_3947_);
lean_dec(v_a_3946_);
v_fst_3948_ = lean_ctor_get(v_snd_3947_, 0);
lean_inc(v_fst_3948_);
v_snd_3949_ = lean_ctor_get(v_snd_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec(v_snd_3947_);
v___x_3950_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_3948_);
lean_dec(v_fst_3948_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3964_; 
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___x_3950_, 0);
lean_dec(v_unused_3965_);
v___x_3952_ = v___x_3950_;
v_isShared_3953_ = v_isSharedCheck_3964_;
goto v_resetjp_3951_;
}
else
{
lean_dec(v___x_3950_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3964_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v_fst_3954_; uint8_t v___x_3955_; 
v_fst_3954_ = lean_ctor_get(v_snd_3949_, 0);
lean_inc(v_fst_3954_);
lean_dec(v_snd_3949_);
v___x_3955_ = lean_unbox(v_fst_3954_);
lean_dec(v_fst_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3956_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3960_);
v___x_3962_ = v___x_3952_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_snd_3949_);
v_a_3966_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3950_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3950_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
v_a_3974_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3930_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3930_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_mods_3912_);
lean_dec_ref(v_args_3910_);
v_a_3982_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3918_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3918_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec_ref(v_mods_3912_);
lean_dec_ref(v_args_3910_);
v___x_3990_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_3991_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3990_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3999_; 
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3991_, 0);
lean_dec(v_unused_4000_);
v___x_3993_ = v___x_3991_;
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
else
{
lean_dec(v___x_3991_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3999_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3995_);
v___x_3997_ = v___x_3993_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3991_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lake_BuiltinLint_run(v_args_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_4012_, lean_object* v_constName_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_4013_, v___y_4014_, v___y_4015_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4018_, lean_object* v_constName_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3(v_00_u03b1_4018_, v_constName_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16(lean_object* v_00_u03b1_4024_, lean_object* v_ref_4025_, lean_object* v_constName_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_4025_, v_constName_4026_, v___y_4027_, v___y_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___boxed(lean_object* v_00_u03b1_4031_, lean_object* v_ref_4032_, lean_object* v_constName_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16(v_00_u03b1_4031_, v_ref_4032_, v_constName_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v_ref_4032_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18(lean_object* v_00_u03b1_4038_, lean_object* v_ref_4039_, lean_object* v_msg_4040_, lean_object* v_declHint_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_4039_, v_msg_4040_, v_declHint_4041_, v___y_4042_, v___y_4043_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___boxed(lean_object* v_00_u03b1_4046_, lean_object* v_ref_4047_, lean_object* v_msg_4048_, lean_object* v_declHint_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18(v_00_u03b1_4046_, v_ref_4047_, v_msg_4048_, v_declHint_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v_ref_4047_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_4054_, lean_object* v_declHint_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_4054_, v_declHint_4055_, v___y_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_4060_, lean_object* v_declHint_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20(v_msg_4060_, v_declHint_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_4066_, lean_object* v_ref_4067_, lean_object* v_msg_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_4067_, v_msg_4068_, v___y_4069_, v___y_4070_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_4073_, lean_object* v_ref_4074_, lean_object* v_msg_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20(v_00_u03b1_4073_, v_ref_4074_, v_msg_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v_ref_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_4080_, lean_object* v_msg_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_4081_, v___y_4082_, v___y_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_msg_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_4086_, v_msg_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4091_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin);
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
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
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
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin);
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
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
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
