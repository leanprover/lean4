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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
extern lean_object* l_Lean_linter_doc_deferred;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_924_, v___y_925_, v___y_923_, v___y_927_);
lean_dec(v___y_927_);
lean_dec(v___y_924_);
v___y_895_ = v___y_926_;
v___y_896_ = v___x_928_;
goto v___jp_894_;
}
v___jp_929_:
{
uint8_t v___x_935_; 
v___x_935_ = lean_nat_dec_le(v___y_934_, v___y_932_);
if (v___x_935_ == 0)
{
lean_dec(v___y_932_);
lean_inc(v___y_934_);
v___y_923_ = v___y_934_;
v___y_924_ = v___y_930_;
v___y_925_ = v___y_931_;
v___y_926_ = v___y_933_;
v___y_927_ = v___y_934_;
goto v___jp_922_;
}
else
{
v___y_923_ = v___y_934_;
v___y_924_ = v___y_930_;
v___y_925_ = v___y_931_;
v___y_926_ = v___y_933_;
v___y_927_ = v___y_932_;
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
v___y_930_ = v___x_939_;
v___y_931_ = v___y_937_;
v___y_932_ = v___x_941_;
v___y_933_ = v___x_938_;
v___y_934_ = v___x_941_;
goto v___jp_929_;
}
else
{
v___y_930_ = v___x_939_;
v___y_931_ = v___y_937_;
v___y_932_ = v___x_941_;
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
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_env_1435_; lean_object* v___x_1436_; lean_object* v_env_1437_; lean_object* v___x_1438_; lean_object* v_toEnvExtension_1439_; lean_object* v_asyncMode_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1434_ = lean_st_ref_get(v___y_1432_);
v_env_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_ref(v_env_1435_);
lean_dec(v___x_1434_);
v___x_1436_ = lean_st_ref_get(v___y_1432_);
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = l_Lean_declRangeExt;
v_toEnvExtension_1439_ = lean_ctor_get(v___x_1438_, 0);
v_asyncMode_1440_ = lean_ctor_get(v_toEnvExtension_1439_, 2);
v___x_1441_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1442_ = 0;
lean_inc(v_declName_1431_);
v___x_1443_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1441_, v___x_1438_, v_env_1435_, v_declName_1431_, v_asyncMode_1440_, v___x_1442_);
if (lean_obj_tag(v___x_1443_) == 0)
{
uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = 1;
v___x_1445_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1441_, v___x_1438_, v_env_1437_, v_declName_1431_, v_asyncMode_1440_, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v_env_1437_);
lean_dec(v_declName_1431_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1443_);
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1448_, v___y_1449_);
lean_dec(v___y_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v_env_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1455_ = lean_st_ref_get(v___y_1453_);
v_env_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc_ref(v_env_1456_);
lean_dec(v___x_1455_);
v___x_1457_ = l_Lean_isRecCore(v_env_1456_, v_declName_1452_);
v___x_1458_ = lean_box(v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1460_, v___y_1461_);
lean_dec(v___y_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_ranges_1469_; lean_object* v___x_1475_; lean_object* v_env_1476_; lean_object* v___x_1477_; lean_object* v_a_1478_; uint8_t v___y_1484_; uint8_t v___x_1488_; 
v___x_1475_ = lean_st_ref_get(v___y_1466_);
v_env_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc_ref_n(v_env_1476_, 2);
lean_dec(v___x_1475_);
lean_inc_n(v_declName_1464_, 2);
v___x_1477_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1464_, v___y_1466_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___x_1488_ = l_Lean_isAuxRecursor(v_env_1476_, v_declName_1464_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; 
lean_inc(v_declName_1464_);
v___x_1489_ = l_Lean_isNoConfusion(v_env_1476_, v_declName_1464_);
v___y_1484_ = v___x_1489_;
goto v___jp_1483_;
}
else
{
lean_dec_ref(v_env_1476_);
v___y_1484_ = v___x_1488_;
goto v___jp_1483_;
}
v___jp_1468_:
{
if (lean_obj_tag(v_ranges_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1470_ = l_Lean_builtinDeclRanges;
v___x_1471_ = lean_st_ref_get(v___x_1470_);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1471_, v_declName_1464_);
lean_dec(v_declName_1464_);
lean_dec(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; 
lean_dec(v_declName_1464_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_ranges_1469_);
return v___x_1474_;
}
}
v___jp_1479_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_a_1482_; 
v___x_1480_ = l_Lean_Name_getPrefix(v_declName_1464_);
v___x_1481_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1480_, v___y_1466_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v_ranges_1469_ = v_a_1482_;
goto v___jp_1468_;
}
v___jp_1483_:
{
if (v___y_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v_a_1487_; 
lean_inc(v_declName_1464_);
v___x_1486_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1464_, v___y_1466_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v_ranges_1469_ = v_a_1487_;
goto v___jp_1468_;
}
else
{
goto v___jp_1479_;
}
}
else
{
lean_dec(v_a_1478_);
goto v___jp_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1495_, lean_object* v_site_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
if (lean_obj_tag(v_site_1496_) == 0)
{
lean_object* v_name_1500_; lean_object* v___x_1501_; 
v_name_1500_ = lean_ctor_get(v_site_1496_, 0);
lean_inc(v_name_1500_);
lean_dec_ref_known(v_site_1496_, 1);
v___x_1501_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1500_, v_a_1497_, v_a_1498_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1523_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1523_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1523_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
if (lean_obj_tag(v_a_1502_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1506_);
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1522_; 
v_val_1510_ = lean_ctor_get(v_a_1502_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_a_1502_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1512_ = v_a_1502_;
v_isShared_1513_ = v_isSharedCheck_1522_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_val_1510_);
lean_dec(v_a_1502_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1522_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_range_1514_; lean_object* v_pos_1515_; lean_object* v___x_1517_; 
v_range_1514_ = lean_ctor_get(v_val_1510_, 0);
lean_inc_ref(v_range_1514_);
lean_dec(v_val_1510_);
v_pos_1515_ = lean_ctor_get(v_range_1514_, 0);
lean_inc_ref(v_pos_1515_);
lean_dec_ref(v_range_1514_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_pos_1515_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_pos_1515_);
v___x_1517_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1517_);
v___x_1519_ = v___x_1504_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1501_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1501_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_n_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1563_; 
v_n_1532_ = lean_ctor_get(v_site_1496_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_site_1496_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1534_ = v_site_1496_;
v_isShared_1535_ = v_isSharedCheck_1563_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_n_1532_);
lean_dec(v_site_1496_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1563_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v_env_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_st_ref_get(v_a_1498_);
v_env_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc_ref(v_env_1537_);
lean_dec(v___x_1536_);
v___x_1538_ = l_Lean_getVersoModuleDoc_x3f(v_env_1537_, v_failMod_1495_);
lean_dec_ref(v_env_1537_);
if (lean_obj_tag(v___x_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1558_; 
v_val_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1558_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_val_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1558_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = lean_array_get_size(v_val_1539_);
v___x_1544_ = lean_nat_dec_lt(v_n_1532_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_del_object(v___x_1541_);
lean_dec(v_val_1539_);
lean_dec(v_n_1532_);
v___x_1545_ = lean_box(0);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1545_);
v___x_1547_ = v___x_1534_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
lean_object* v___x_1549_; lean_object* v_declarationRange_1550_; lean_object* v_pos_1551_; lean_object* v___x_1553_; 
v___x_1549_ = lean_array_fget(v_val_1539_, v_n_1532_);
lean_dec(v_n_1532_);
lean_dec(v_val_1539_);
v_declarationRange_1550_ = lean_ctor_get(v___x_1549_, 2);
lean_inc_ref(v_declarationRange_1550_);
lean_dec(v___x_1549_);
v_pos_1551_ = lean_ctor_get(v_declarationRange_1550_, 0);
lean_inc_ref(v_pos_1551_);
lean_dec_ref(v_declarationRange_1550_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_pos_1551_);
v___x_1553_ = v___x_1541_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_pos_1551_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1553_);
v___x_1555_ = v___x_1534_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v___x_1538_);
lean_dec(v_n_1532_);
v___x_1559_ = lean_box(0);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1559_);
v___x_1561_ = v___x_1534_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1564_, lean_object* v_site_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1564_, v_site_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_failMod_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1570_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1580_, v___y_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 0)
{
lean_object* v_name_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_name_1594_ = lean_ctor_get(v_x_1593_, 0);
lean_inc(v_name_1594_);
lean_dec_ref_known(v_x_1593_, 1);
v___x_1595_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1596_ = 1;
v___x_1597_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1594_, v___x_1596_);
v___x_1598_ = lean_string_append(v___x_1595_, v___x_1597_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1600_ = lean_string_append(v___x_1598_, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v_n_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_n_1601_ = lean_ctor_get(v_x_1593_, 0);
lean_inc(v_n_1601_);
lean_dec_ref_known(v_x_1593_, 1);
v___x_1602_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_add(v_n_1601_, v___x_1603_);
lean_dec(v_n_1601_);
v___x_1605_ = l_Nat_reprFast(v___x_1604_);
v___x_1606_ = lean_string_append(v___x_1602_, v___x_1605_);
lean_dec_ref(v___x_1605_);
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(lean_object* v_x_1607_){
_start:
{
if (lean_obj_tag(v_x_1607_) == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_unsigned_to_nat(1u);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___boxed(lean_object* v_x_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(v_x_1610_);
lean_dec_ref(v_x_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_1612_, lean_object* v_k_1613_){
_start:
{
if (lean_obj_tag(v_t_1612_) == 0)
{
uint8_t v_failed_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_failed_1614_ = lean_ctor_get_uint8(v_t_1612_, 0);
lean_dec_ref_known(v_t_1612_, 0);
v___x_1615_ = lean_box(v_failed_1614_);
v___x_1616_ = lean_apply_1(v_k_1613_, v___x_1615_);
return v___x_1616_;
}
else
{
lean_object* v_records_1617_; uint8_t v_unlocated_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_records_1617_ = lean_ctor_get(v_t_1612_, 0);
lean_inc_ref(v_records_1617_);
v_unlocated_1618_ = lean_ctor_get_uint8(v_t_1612_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1612_, 1);
v___x_1619_ = lean_box(v_unlocated_1618_);
v___x_1620_ = lean_apply_2(v_k_1613_, v_records_1617_, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_1621_, lean_object* v_ctorIdx_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1623_, v_k_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_1627_, lean_object* v_ctorIdx_1628_, lean_object* v_t_1629_, lean_object* v_h_1630_, lean_object* v_k_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_1627_, v_ctorIdx_1628_, v_t_1629_, v_h_1630_, v_k_1631_);
lean_dec(v_ctorIdx_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_1633_, lean_object* v_reported_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1633_, v_reported_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_, lean_object* v_reported_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1637_, v_reported_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_1641_, lean_object* v_recorded_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1641_, v_recorded_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_recorded_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_1645_, v_recorded_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v_env_1653_; lean_object* v___x_1654_; lean_object* v_toEnvExtension_1655_; lean_object* v_asyncMode_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_merged_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
v___x_1652_ = lean_st_ref_get(v___y_1650_);
v_env_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1653_);
lean_dec(v___x_1652_);
v___x_1654_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1655_ = lean_ctor_get(v___x_1654_, 0);
v_asyncMode_1656_ = lean_ctor_get(v_toEnvExtension_1655_, 2);
v___x_1657_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1657_, v___x_1654_, v_env_1653_, v_asyncMode_1656_, v___x_1658_);
v_merged_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1659_, 1);
lean_dec(v_unused_1669_);
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_merged_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_merged_1660_);
lean_ctor_set(v___x_1662_, 0, v_o_1649_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_o_1649_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_merged_1660_);
v___x_1665_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1670_, v___y_1671_);
lean_dec(v___y_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1674_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1684_, lean_object* v_opt_1685_){
_start:
{
lean_object* v_name_1686_; lean_object* v_defValue_1687_; lean_object* v_map_1688_; lean_object* v___x_1689_; 
v_name_1686_ = lean_ctor_get(v_opt_1685_, 0);
v_defValue_1687_ = lean_ctor_get(v_opt_1685_, 1);
v_map_1688_ = lean_ctor_get(v_opts_1684_, 0);
v___x_1689_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1688_, v_name_1686_);
if (lean_obj_tag(v___x_1689_) == 0)
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_unbox(v_defValue_1687_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; 
v_val_1691_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___x_1689_, 1);
if (lean_obj_tag(v_val_1691_) == 1)
{
uint8_t v_v_1692_; 
v_v_1692_ = lean_ctor_get_uint8(v_val_1691_, 0);
lean_dec_ref_known(v_val_1691_, 0);
return v_v_1692_;
}
else
{
uint8_t v___x_1693_; 
lean_dec(v_val_1691_);
v___x_1693_ = lean_unbox(v_defValue_1687_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1694_, lean_object* v_opt_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1694_, v_opt_1695_);
lean_dec_ref(v_opt_1695_);
lean_dec_ref(v_opts_1694_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1698_, lean_object* v_opt_1699_){
_start:
{
lean_object* v_name_1700_; lean_object* v_defValue_1701_; lean_object* v_map_1702_; lean_object* v___x_1703_; 
v_name_1700_ = lean_ctor_get(v_opt_1699_, 0);
v_defValue_1701_ = lean_ctor_get(v_opt_1699_, 1);
v_map_1702_ = lean_ctor_get(v_opts_1698_, 0);
v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1702_, v_name_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_inc(v_defValue_1701_);
return v_defValue_1701_;
}
else
{
lean_object* v_val_1704_; 
v_val_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v___x_1703_, 1);
if (lean_obj_tag(v_val_1704_) == 3)
{
lean_object* v_v_1705_; 
v_v_1705_ = lean_ctor_get(v_val_1704_, 0);
lean_inc(v_v_1705_);
lean_dec_ref_known(v_val_1704_, 1);
return v_v_1705_;
}
else
{
lean_dec(v_val_1704_);
lean_inc(v_defValue_1701_);
return v_defValue_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1706_, lean_object* v_opt_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1706_, v_opt_1707_);
lean_dec_ref(v_opt_1707_);
lean_dec_ref(v_opts_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_options_1713_; lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_options_1713_ = lean_ctor_get(v_c_1709_, 6);
lean_inc_ref(v_options_1713_);
lean_dec_ref(v_c_1709_);
v___x_1714_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1713_, v___y_1711_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1719_ = l_Lean_linter_doc_deferred;
v___x_1720_ = l_Lean_Linter_getLinterValue(v___x_1719_, v_a_1715_);
lean_dec(v_a_1715_);
v___x_1721_ = lean_box(v___x_1720_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1721_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1731_, lean_object* v_docCheckedModules_1732_, lean_object* v_m_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1731_, v_m_1733_);
if (v___x_1734_ == 0)
{
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_NameSet_contains(v_docCheckedModules_1732_, v_m_1733_);
if (v___x_1735_ == 0)
{
return v___x_1734_;
}
else
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1737_, lean_object* v_docCheckedModules_1738_, lean_object* v_m_1739_){
_start:
{
uint8_t v_res_1740_; lean_object* v_r_1741_; 
v_res_1740_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1737_, v_docCheckedModules_1738_, v_m_1739_);
lean_dec(v_m_1739_);
lean_dec(v_docCheckedModules_1738_);
lean_dec(v_pkgRoot_1737_);
v_r_1741_ = lean_box(v_res_1740_);
return v_r_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_1749_, lean_object* v_sp_1750_, lean_object* v_as_1751_, size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_a_1759_; uint8_t v_unlocated_1763_; 
v_unlocated_1763_ = lean_usize_dec_lt(v_i_1753_, v_sz_1752_);
if (v_unlocated_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_dec(v_sp_1750_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_b_1754_);
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v_snd_1766_; lean_object* v_fst_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1896_; 
v_a_1765_ = lean_array_uget_borrowed(v_as_1751_, v_i_1753_);
v_snd_1766_ = lean_ctor_get(v_a_1765_, 1);
lean_inc(v_snd_1766_);
v_fst_1767_ = lean_ctor_get(v_snd_1766_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_snd_1766_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v_snd_1766_, 1);
lean_dec(v_unused_1897_);
v___x_1769_ = v_snd_1766_;
v_isShared_1770_ = v_isSharedCheck_1896_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_fst_1767_);
lean_dec(v_snd_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1896_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_fst_1771_; lean_object* v_site_1772_; lean_object* v___x_1773_; 
v_fst_1771_ = lean_ctor_get(v_a_1765_, 0);
v_site_1772_ = lean_ctor_get(v_fst_1767_, 0);
lean_inc_ref_n(v_site_1772_, 2);
lean_dec(v_fst_1767_);
v___x_1773_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_1771_, v_site_1772_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
if (lean_obj_tag(v_a_1774_) == 0)
{
lean_object* v_fst_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1814_; 
v_fst_1775_ = lean_ctor_get(v_b_1754_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_b_1754_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_b_1754_, 1);
lean_dec(v_unused_1815_);
v___x_1777_ = v_b_1754_;
v_isShared_1778_ = v_isSharedCheck_1814_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_fst_1775_);
lean_dec(v_b_1754_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1814_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v_name_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1779_ = l_Lean_linter_doc_deferred;
v_name_1780_ = lean_ctor_get(v___x_1779_, 0);
v___x_1781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_1782_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1772_);
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_1785_ = lean_string_append(v___x_1783_, v___x_1784_);
lean_inc(v_fst_1771_);
v___x_1786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1771_, v___x_1749_);
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_inc(v_name_1780_);
v___x_1790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1780_, v___x_1749_);
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
v___x_1794_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec_ref_known(v___x_1794_, 1);
lean_del_object(v___x_1769_);
v___x_1795_ = lean_box(v_unlocated_1763_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1795_);
v___x_1797_ = v___x_1777_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_fst_1775_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v_a_1759_ = v___x_1797_;
goto v___jp_1758_;
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1813_; 
lean_del_object(v___x_1777_);
lean_dec(v_fst_1775_);
lean_dec(v_sp_1750_);
v_a_1799_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1801_ = v___x_1794_;
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1794_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1813_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_ref_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v_ref_1803_ = lean_ctor_get(v___y_1755_, 5);
v___x_1804_ = lean_io_error_to_string(v_a_1799_);
v___x_1805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
v___x_1806_ = l_Lean_MessageData_ofFormat(v___x_1805_);
lean_inc(v_ref_1803_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___x_1806_);
lean_ctor_set(v___x_1769_, 0, v_ref_1803_);
v___x_1808_ = v___x_1769_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_ref_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1808_);
v___x_1810_ = v___x_1801_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1816_; lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_site_1772_);
v_fst_1816_ = lean_ctor_get(v_b_1754_, 0);
v_snd_1817_ = lean_ctor_get(v_b_1754_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_b_1754_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1819_ = v_b_1754_;
v_isShared_1820_ = v_isSharedCheck_1887_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_inc(v_fst_1816_);
lean_dec(v_b_1754_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1887_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_val_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1886_; 
v_val_1821_ = lean_ctor_get(v_a_1774_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1823_ = v_a_1774_;
v_isShared_1824_ = v_isSharedCheck_1886_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_val_1821_);
lean_dec(v_a_1774_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1886_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1771_);
lean_inc(v_sp_1750_);
v___x_1826_ = l_Lean_SearchPath_findWithExt(v_sp_1750_, v___x_1825_, v_fst_1771_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
if (lean_obj_tag(v_a_1827_) == 0)
{
lean_object* v___x_1828_; lean_object* v_name_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_val_1821_);
lean_dec(v_snd_1817_);
v___x_1828_ = l_Lean_linter_doc_deferred;
v_name_1829_ = lean_ctor_get(v___x_1828_, 0);
v___x_1830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_1771_);
v___x_1831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1771_, v___x_1749_);
v___x_1832_ = lean_string_append(v___x_1830_, v___x_1831_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_1834_ = lean_string_append(v___x_1832_, v___x_1833_);
lean_inc(v_name_1829_);
v___x_1835_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1829_, v___x_1749_);
v___x_1836_ = lean_string_append(v___x_1834_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
v___x_1839_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1838_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec_ref_known(v___x_1839_, 1);
lean_del_object(v___x_1823_);
lean_del_object(v___x_1769_);
v___x_1840_ = lean_box(v_unlocated_1763_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1840_);
v___x_1842_ = v___x_1819_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fst_1816_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
v_a_1759_ = v___x_1842_;
goto v___jp_1758_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1860_; 
lean_del_object(v___x_1819_);
lean_dec(v_fst_1816_);
lean_dec(v_sp_1750_);
v_a_1844_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1846_ = v___x_1839_;
v_isShared_1847_ = v_isSharedCheck_1860_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1839_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1860_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_ref_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v_ref_1848_ = lean_ctor_get(v___y_1755_, 5);
v___x_1849_ = lean_io_error_to_string(v_a_1844_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 3);
lean_ctor_set(v___x_1823_, 0, v___x_1849_);
v___x_1851_ = v___x_1823_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_MessageData_ofFormat(v___x_1851_);
lean_inc(v_ref_1848_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___x_1852_);
lean_ctor_set(v___x_1769_, 0, v_ref_1848_);
v___x_1854_ = v___x_1769_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_ref_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1854_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
else
{
lean_object* v_val_1861_; lean_object* v___x_1862_; lean_object* v_name_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_del_object(v___x_1823_);
lean_del_object(v___x_1769_);
v_val_1861_ = lean_ctor_get(v_a_1827_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_a_1827_, 1);
v___x_1862_ = l_Lean_linter_doc_deferred;
v_name_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_name_1863_);
v___x_1864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1864_, 0, v_val_1861_);
lean_ctor_set(v___x_1864_, 1, v_val_1821_);
lean_ctor_set(v___x_1864_, 2, v_name_1863_);
v___x_1865_ = lean_array_push(v_fst_1816_, v___x_1864_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1865_);
v___x_1867_ = v___x_1819_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_snd_1817_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v_a_1759_ = v___x_1867_;
goto v___jp_1758_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_val_1821_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_fst_1816_);
lean_dec(v_sp_1750_);
v_a_1869_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1871_ = v___x_1826_;
v_isShared_1872_ = v_isSharedCheck_1885_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1826_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1885_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_ref_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v_ref_1873_ = lean_ctor_get(v___y_1755_, 5);
v___x_1874_ = lean_io_error_to_string(v_a_1869_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 3);
lean_ctor_set(v___x_1823_, 0, v___x_1874_);
v___x_1876_ = v___x_1823_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = l_Lean_MessageData_ofFormat(v___x_1876_);
lean_inc(v_ref_1873_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___x_1877_);
lean_ctor_set(v___x_1769_, 0, v_ref_1873_);
v___x_1879_ = v___x_1769_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_ref_1873_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1879_);
v___x_1881_ = v___x_1871_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
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
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_site_1772_);
lean_del_object(v___x_1769_);
lean_dec_ref(v_b_1754_);
lean_dec(v_sp_1750_);
v_a_1888_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1773_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1773_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
v___jp_1758_:
{
size_t v___x_1760_; size_t v___x_1761_; 
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1753_, v___x_1760_);
v_i_1753_ = v___x_1761_;
v_b_1754_ = v_a_1759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_1898_, lean_object* v_sp_1899_, lean_object* v_as_1900_, lean_object* v_sz_1901_, lean_object* v_i_1902_, lean_object* v_b_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_8962__boxed_1907_; size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v___x_8962__boxed_1907_ = lean_unbox(v___x_1898_);
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1901_);
lean_dec(v_sz_1901_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1902_);
lean_dec(v_i_1902_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_8962__boxed_1907_, v_sp_1899_, v_as_1900_, v_sz_boxed_1908_, v_i_boxed_1909_, v_b_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_as_1900_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_1917_, uint8_t v___y_1918_, lean_object* v_as_1919_, size_t v_sz_1920_, size_t v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_a_1926_; uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_lt(v_i_1921_, v_sz_1920_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v_sp_1917_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_b_1922_);
return v___x_1931_;
}
else
{
lean_object* v_a_1932_; lean_object* v_snd_1933_; lean_object* v_fst_1934_; lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_2031_; 
v_a_1932_ = lean_array_uget_borrowed(v_as_1919_, v_i_1921_);
v_snd_1933_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1933_);
v_fst_1934_ = lean_ctor_get(v_snd_1933_, 0);
lean_inc(v_fst_1934_);
v_fst_1935_ = lean_ctor_get(v_a_1932_, 0);
v_snd_1936_ = lean_ctor_get(v_snd_1933_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_snd_1933_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v_snd_1933_, 0);
lean_dec(v_unused_2032_);
v___x_1938_ = v_snd_1933_;
v_isShared_1939_ = v_isSharedCheck_2031_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snd_1936_);
lean_dec(v_snd_1933_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_2031_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_site_1940_; lean_object* v_sourceString_1941_; lean_object* v___x_1942_; lean_object* v___y_1944_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_site_1940_ = lean_ctor_get(v_fst_1934_, 0);
lean_inc_ref(v_site_1940_);
v_sourceString_1941_ = lean_ctor_get(v_fst_1934_, 2);
lean_inc_ref(v_sourceString_1941_);
lean_dec(v_fst_1934_);
v___x_1942_ = lean_box(0);
v___x_2023_ = lean_string_utf8_byte_size(v_sourceString_1941_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_nat_dec_eq(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2027_ = lean_string_append(v___x_2026_, v_sourceString_1941_);
lean_dec_ref(v_sourceString_1941_);
v___x_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2029_ = lean_string_append(v___x_2027_, v___x_2028_);
v___y_1944_ = v___x_2029_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_2030_; 
lean_dec_ref(v_sourceString_1941_);
v___x_2030_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1944_ = v___x_2030_;
goto v___jp_1943_;
}
v___jp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1935_);
lean_inc(v_sp_1917_);
v___x_1946_ = l_Lean_SearchPath_findWithExt(v_sp_1917_, v___x_1945_, v_fst_1935_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
if (lean_obj_tag(v_a_1947_) == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1948_ = l_Lean_MessageData_toString(v_snd_1936_);
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_1935_);
v___x_1950_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1935_, v___y_1918_);
v___x_1951_ = lean_string_append(v___x_1949_, v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_1953_ = lean_string_append(v___x_1951_, v___x_1952_);
v___x_1954_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1940_);
v___x_1955_ = lean_string_append(v___x_1953_, v___x_1954_);
lean_dec_ref(v___x_1954_);
v___x_1956_ = lean_string_append(v___x_1955_, v___y_1944_);
lean_dec_ref(v___y_1944_);
v___x_1957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_1958_ = lean_string_append(v___x_1956_, v___x_1957_);
v___x_1959_ = lean_string_append(v___x_1958_, v___x_1948_);
lean_dec_ref(v___x_1948_);
v___x_1960_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1959_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
lean_del_object(v___x_1938_);
v_a_1926_ = v___x_1942_;
goto v___jp_1925_;
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_sp_1917_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_ref_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v_ref_1965_ = lean_ctor_get(v___y_1923_, 5);
v___x_1966_ = lean_io_error_to_string(v_a_1961_);
v___x_1967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
v___x_1968_ = l_Lean_MessageData_ofFormat(v___x_1967_);
lean_inc(v_ref_1965_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_1968_);
lean_ctor_set(v___x_1938_, 0, v_ref_1965_);
v___x_1970_ = v___x_1938_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_ref_1965_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1970_);
v___x_1972_ = v___x_1963_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2007_; 
v_val_1976_ = lean_ctor_get(v_a_1947_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1978_ = v_a_1947_;
v_isShared_1979_ = v_isSharedCheck_2007_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v_a_1947_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2007_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1980_ = l_Lean_MessageData_toString(v_snd_1936_);
v___x_1981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_1982_ = lean_string_append(v_val_1976_, v___x_1981_);
v___x_1983_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1940_);
v___x_1984_ = lean_string_append(v___x_1982_, v___x_1983_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = lean_string_append(v___x_1984_, v___y_1944_);
lean_dec_ref(v___y_1944_);
v___x_1986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
v___x_1988_ = lean_string_append(v___x_1987_, v___x_1980_);
lean_dec_ref(v___x_1980_);
v___x_1989_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref_known(v___x_1989_, 1);
lean_del_object(v___x_1978_);
lean_del_object(v___x_1938_);
v_a_1926_ = v___x_1942_;
goto v___jp_1925_;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_sp_1917_);
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2006_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2006_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_ref_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v_ref_1994_ = lean_ctor_get(v___y_1923_, 5);
v___x_1995_ = lean_io_error_to_string(v_a_1990_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 3);
lean_ctor_set(v___x_1978_, 0, v___x_1995_);
v___x_1997_ = v___x_1978_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = l_Lean_MessageData_ofFormat(v___x_1997_);
lean_inc(v_ref_1994_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_1998_);
lean_ctor_set(v___x_1938_, 0, v_ref_1994_);
v___x_2000_ = v___x_1938_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_ref_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2000_);
v___x_2002_ = v___x_1992_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
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
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_site_1940_);
lean_dec(v_snd_1936_);
lean_dec(v_sp_1917_);
v_a_2008_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2010_ = v___x_1946_;
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1946_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_ref_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v_ref_2012_ = lean_ctor_get(v___y_1923_, 5);
v___x_2013_ = lean_io_error_to_string(v_a_2008_);
v___x_2014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
v___x_2015_ = l_Lean_MessageData_ofFormat(v___x_2014_);
lean_inc(v_ref_2012_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_2015_);
lean_ctor_set(v___x_1938_, 0, v_ref_2012_);
v___x_2017_ = v___x_1938_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_ref_2012_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2017_);
v___x_2019_ = v___x_2010_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
}
v___jp_1925_:
{
size_t v___x_1927_; size_t v___x_1928_; 
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_i_1921_, v___x_1927_);
v_i_1921_ = v___x_1928_;
v_b_1922_ = v_a_1926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2033_, lean_object* v___y_2034_, lean_object* v_as_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v___y_9254__boxed_2041_; size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v___y_9254__boxed_2041_ = lean_unbox(v___y_2034_);
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2033_, v___y_9254__boxed_2041_, v_as_2035_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2038_, v___y_2039_);
lean_dec_ref(v___y_2039_);
lean_dec_ref(v_as_2035_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2045_, lean_object* v_as_2046_, size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_b_2049_){
_start:
{
lean_object* v_a_2052_; uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_b_2049_);
return v___x_2057_;
}
else
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_array_uget_borrowed(v_as_2046_, v_i_2048_);
v___x_2059_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2045_, v_a_2058_);
if (v___x_2059_ == 0)
{
v_a_2052_ = v_b_2049_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2060_; 
lean_inc(v_a_2058_);
v___x_2060_ = l_Lean_NameSet_insert(v_b_2049_, v_a_2058_);
v_a_2052_ = v___x_2060_;
goto v___jp_2051_;
}
}
v___jp_2051_:
{
size_t v___x_2053_; size_t v___x_2054_; 
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2048_, v___x_2053_);
v_i_2048_ = v___x_2054_;
v_b_2049_ = v_a_2052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2061_, lean_object* v_as_2062_, lean_object* v_sz_2063_, lean_object* v_i_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2063_);
lean_dec(v_sz_2063_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2064_);
lean_dec(v_i_2064_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2061_, v_as_2062_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2065_);
lean_dec_ref(v_as_2062_);
lean_dec(v_pkgRoot_2061_);
return v_res_2069_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_unsigned_to_nat(32u);
v___x_2077_ = lean_mk_empty_array_with_capacity(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2079_ = ((size_t)5ULL);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_unsigned_to_nat(32u);
v___x_2082_ = lean_mk_empty_array_with_capacity(v___x_2081_);
v___x_2083_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2084_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2080_);
lean_ctor_set(v___x_2084_, 3, v___x_2080_);
lean_ctor_set_usize(v___x_2084_, 4, v___x_2079_);
return v___x_2084_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2085_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = l_Lean_NameSet_empty;
v___x_2091_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
lean_ctor_set(v___x_2092_, 2, v___x_2090_);
return v___x_2092_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_firstFrontendMacroScope;
v___x_2095_ = lean_nat_add(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2106_; uint64_t v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2107_ = 0ULL;
v___x_2108_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set_uint64(v___x_2108_, sizeof(void*)*1, v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v_unlocated_2111_; lean_object* v___x_2112_; 
v___x_2109_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2110_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2111_ = 1;
v___x_2112_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2110_);
lean_ctor_set(v___x_2112_, 2, v___x_2109_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*3, v_unlocated_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l_Lean_Options_empty;
v___x_2116_ = l_Lean_Core_getMaxHeartbeats(v___x_2115_);
return v___x_2116_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2117_ = l_Lean_diagnostics;
v___x_2118_ = l_Lean_Options_empty;
v___x_2119_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2118_, v___x_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2120_, lean_object* v_linterOpts_2121_, lean_object* v_sp_2122_, lean_object* v_env_2123_, lean_object* v_pkgRoot_2124_, lean_object* v_docCheckedModules_2125_){
_start:
{
lean_object* v___y_2128_; lean_object* v_a_2129_; lean_object* v___y_2154_; uint8_t v___y_2155_; lean_object* v_a_2158_; uint8_t v___y_2162_; lean_object* v_a_2163_; lean_object* v___y_2180_; uint8_t v_lintOnly_2183_; uint8_t v_recordExceptions_2184_; lean_object* v___f_2185_; lean_object* v___f_2186_; lean_object* v___y_2188_; uint8_t v___y_2189_; uint8_t v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; uint8_t v___y_2193_; lean_object* v___y_2194_; lean_object* v_fileName_2195_; lean_object* v_fileMap_2196_; lean_object* v_currRecDepth_2197_; lean_object* v_ref_2198_; lean_object* v_currNamespace_2199_; lean_object* v_openDecls_2200_; lean_object* v_initHeartbeats_2201_; lean_object* v_maxHeartbeats_2202_; lean_object* v_quotContext_2203_; lean_object* v_currMacroScope_2204_; lean_object* v_cancelTk_x3f_2205_; uint8_t v_suppressElabErrors_2206_; lean_object* v_inheritedTraceOptions_2207_; lean_object* v___y_2208_; lean_object* v___y_2236_; uint8_t v___y_2237_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; uint8_t v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; uint8_t v___y_2259_; uint8_t v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint8_t v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; uint8_t v___y_2267_; uint8_t v___y_2288_; 
v_lintOnly_2183_ = lean_ctor_get_uint8(v_args_2120_, sizeof(void*)*3);
v_recordExceptions_2184_ = lean_ctor_get_uint8(v_args_2120_, sizeof(void*)*3 + 1);
v___f_2185_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
lean_inc(v_docCheckedModules_2125_);
lean_inc(v_pkgRoot_2124_);
v___f_2186_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2186_, 0, v_pkgRoot_2124_);
lean_closure_set(v___f_2186_, 1, v_docCheckedModules_2125_);
if (v_lintOnly_2183_ == 0)
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = l_Lean_linter_doc_deferred;
v___x_2323_ = l_Lean_Linter_getLinterValue(v___x_2322_, v_linterOpts_2121_);
v___y_2288_ = v___x_2323_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2324_; lean_object* v_name_2325_; uint8_t v___x_2326_; 
v___x_2324_ = l_Lean_linter_doc_deferred;
v_name_2325_ = lean_ctor_get(v___x_2324_, 0);
v___x_2326_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2325_, v_linterOpts_2121_);
v___y_2288_ = v___x_2326_;
goto v___jp_2287_;
}
v___jp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2130_ = lean_st_ref_get(v___y_2128_);
lean_dec(v___y_2128_);
lean_dec(v___x_2130_);
v___x_2131_ = l_Lean_Environment_header(v_env_2123_);
lean_dec_ref(v_env_2123_);
v___x_2132_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2131_);
v_sz_2133_ = lean_array_size(v___x_2132_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2124_, v___x_2132_, v_sz_2133_, v___x_2134_, v_docCheckedModules_2125_);
lean_dec_ref(v___x_2132_);
lean_dec(v_pkgRoot_2124_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2129_);
lean_ctor_set(v___x_2140_, 1, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_a_2129_);
v_a_2145_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2135_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2135_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
v___jp_2153_:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2156_, 0, v___y_2155_);
v___y_2128_ = v___y_2154_;
v_a_2129_ = v___x_2156_;
goto v___jp_2127_;
}
v___jp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_mk_io_user_error(v_a_2158_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
v___jp_2161_:
{
if (lean_obj_tag(v_a_2163_) == 0)
{
lean_object* v_msg_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_msg_2164_ = lean_ctor_get(v_a_2163_, 1);
lean_inc_ref(v_msg_2164_);
lean_dec_ref_known(v_a_2163_, 2);
v___x_2165_ = l_Lean_MessageData_toString(v_msg_2164_);
v___x_2166_ = lean_mk_io_user_error(v___x_2165_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v_id_2168_; lean_object* v___x_2169_; 
v_id_2168_ = lean_ctor_get(v_a_2163_, 0);
lean_inc(v_id_2168_);
lean_dec_ref_known(v_a_2163_, 2);
v___x_2169_ = l_Lean_InternalExceptionId_getName(v_id_2168_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v_id_2168_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2172_ = l_Lean_Name_toString(v_a_2170_, v___y_2162_);
v___x_2173_ = lean_string_append(v___x_2171_, v___x_2172_);
lean_dec_ref(v___x_2172_);
v_a_2158_ = v___x_2173_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2174_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2175_ = l_Nat_reprFast(v_id_2168_);
v___x_2176_ = lean_string_append(v___x_2174_, v___x_2175_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2178_ = lean_string_append(v___x_2176_, v___x_2177_);
v_a_2158_ = v___x_2178_;
goto v___jp_2157_;
}
}
}
v___jp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2180_);
lean_ctor_set(v___x_2181_, 1, v_docCheckedModules_2125_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
v___jp_2187_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2209_ = l_Lean_maxRecDepth;
v___x_2210_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2191_, v___x_2209_);
lean_inc_ref(v___y_2191_);
v___x_2211_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2211_, 0, v_fileName_2195_);
lean_ctor_set(v___x_2211_, 1, v_fileMap_2196_);
lean_ctor_set(v___x_2211_, 2, v___y_2191_);
lean_ctor_set(v___x_2211_, 3, v_currRecDepth_2197_);
lean_ctor_set(v___x_2211_, 4, v___x_2210_);
lean_ctor_set(v___x_2211_, 5, v_ref_2198_);
lean_ctor_set(v___x_2211_, 6, v_currNamespace_2199_);
lean_ctor_set(v___x_2211_, 7, v_openDecls_2200_);
lean_ctor_set(v___x_2211_, 8, v_initHeartbeats_2201_);
lean_ctor_set(v___x_2211_, 9, v_maxHeartbeats_2202_);
lean_ctor_set(v___x_2211_, 10, v_quotContext_2203_);
lean_ctor_set(v___x_2211_, 11, v_currMacroScope_2204_);
lean_ctor_set(v___x_2211_, 12, v_cancelTk_x3f_2205_);
lean_ctor_set(v___x_2211_, 13, v_inheritedTraceOptions_2207_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*14, v___y_2193_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*14 + 1, v_suppressElabErrors_2206_);
lean_inc_ref(v___y_2188_);
v___x_2212_ = l_Lean_Doc_DeferredCheck_run(v___f_2186_, v___y_2188_, v___x_2211_, v___y_2208_);
if (lean_obj_tag(v___x_2212_) == 0)
{
if (v_recordExceptions_2184_ == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v___y_2208_);
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = lean_box(0);
v_sz_2215_ = lean_array_size(v_a_2213_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2122_, v___y_2189_, v_a_2213_, v_sz_2215_, v___x_2216_, v___x_2214_, v___x_2211_);
lean_dec_ref_known(v___x_2211_, 14);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
lean_dec_ref_known(v___x_2217_, 1);
v___x_2218_ = lean_array_get_size(v_a_2213_);
lean_dec(v_a_2213_);
v___x_2219_ = lean_nat_dec_eq(v___x_2218_, v___y_2194_);
lean_dec(v___y_2194_);
if (v___x_2219_ == 0)
{
v___y_2154_ = v___y_2192_;
v___y_2155_ = v___y_2189_;
goto v___jp_2153_;
}
else
{
v___y_2154_ = v___y_2192_;
v___y_2155_ = v_recordExceptions_2184_;
goto v___jp_2153_;
}
}
else
{
lean_object* v_a_2220_; 
lean_dec(v_a_2213_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec(v_docCheckedModules_2125_);
lean_dec(v_pkgRoot_2124_);
lean_dec_ref(v_env_2123_);
v_a_2220_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2217_, 1);
v___y_2162_ = v___y_2189_;
v_a_2163_ = v_a_2220_;
goto v___jp_2161_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v_a_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2222_ = lean_mk_empty_array_with_capacity(v___y_2194_);
lean_dec(v___y_2194_);
v___x_2223_ = lean_box(v___y_2190_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v_sz_2225_ = lean_array_size(v_a_2221_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v_recordExceptions_2184_, v_sp_2122_, v_a_2221_, v_sz_2225_, v___x_2226_, v___x_2224_, v___x_2211_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref_known(v___x_2211_, 14);
lean_dec(v_a_2221_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v_fst_2229_; lean_object* v_snd_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v_fst_2229_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_fst_2229_);
v_snd_2230_ = lean_ctor_get(v_a_2228_, 1);
lean_inc(v_snd_2230_);
lean_dec(v_a_2228_);
v___x_2231_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2231_, 0, v_fst_2229_);
v___x_2232_ = lean_unbox(v_snd_2230_);
lean_dec(v_snd_2230_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1, v___x_2232_);
v___y_2128_ = v___y_2192_;
v_a_2129_ = v___x_2231_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2233_; 
lean_dec(v___y_2192_);
lean_dec(v_docCheckedModules_2125_);
lean_dec(v_pkgRoot_2124_);
lean_dec_ref(v_env_2123_);
v_a_2233_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2227_, 1);
v___y_2162_ = v___y_2189_;
v_a_2163_ = v_a_2233_;
goto v___jp_2161_;
}
}
}
else
{
lean_object* v_a_2234_; 
lean_dec_ref_known(v___x_2211_, 14);
lean_dec(v___y_2208_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec(v_docCheckedModules_2125_);
lean_dec(v_pkgRoot_2124_);
lean_dec_ref(v_env_2123_);
lean_dec(v_sp_2122_);
v_a_2234_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2212_, 1);
v___y_2162_ = v___y_2189_;
v_a_2163_ = v_a_2234_;
goto v___jp_2161_;
}
}
v___jp_2235_:
{
lean_object* v_fileName_2245_; lean_object* v_fileMap_2246_; lean_object* v_currRecDepth_2247_; lean_object* v_ref_2248_; lean_object* v_currNamespace_2249_; lean_object* v_openDecls_2250_; lean_object* v_initHeartbeats_2251_; lean_object* v_maxHeartbeats_2252_; lean_object* v_quotContext_2253_; lean_object* v_currMacroScope_2254_; lean_object* v_cancelTk_x3f_2255_; uint8_t v_suppressElabErrors_2256_; lean_object* v_inheritedTraceOptions_2257_; 
v_fileName_2245_ = lean_ctor_get(v___y_2243_, 0);
lean_inc_ref(v_fileName_2245_);
v_fileMap_2246_ = lean_ctor_get(v___y_2243_, 1);
lean_inc_ref(v_fileMap_2246_);
v_currRecDepth_2247_ = lean_ctor_get(v___y_2243_, 3);
lean_inc(v_currRecDepth_2247_);
v_ref_2248_ = lean_ctor_get(v___y_2243_, 5);
lean_inc(v_ref_2248_);
v_currNamespace_2249_ = lean_ctor_get(v___y_2243_, 6);
lean_inc(v_currNamespace_2249_);
v_openDecls_2250_ = lean_ctor_get(v___y_2243_, 7);
lean_inc(v_openDecls_2250_);
v_initHeartbeats_2251_ = lean_ctor_get(v___y_2243_, 8);
lean_inc(v_initHeartbeats_2251_);
v_maxHeartbeats_2252_ = lean_ctor_get(v___y_2243_, 9);
lean_inc(v_maxHeartbeats_2252_);
v_quotContext_2253_ = lean_ctor_get(v___y_2243_, 10);
lean_inc(v_quotContext_2253_);
v_currMacroScope_2254_ = lean_ctor_get(v___y_2243_, 11);
lean_inc(v_currMacroScope_2254_);
v_cancelTk_x3f_2255_ = lean_ctor_get(v___y_2243_, 12);
lean_inc(v_cancelTk_x3f_2255_);
v_suppressElabErrors_2256_ = lean_ctor_get_uint8(v___y_2243_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2257_ = lean_ctor_get(v___y_2243_, 13);
lean_inc_ref(v_inheritedTraceOptions_2257_);
lean_dec_ref(v___y_2243_);
v___y_2188_ = v___y_2236_;
v___y_2189_ = v___y_2237_;
v___y_2190_ = v___y_2238_;
v___y_2191_ = v___y_2239_;
v___y_2192_ = v___y_2240_;
v___y_2193_ = v___y_2241_;
v___y_2194_ = v___y_2242_;
v_fileName_2195_ = v_fileName_2245_;
v_fileMap_2196_ = v_fileMap_2246_;
v_currRecDepth_2197_ = v_currRecDepth_2247_;
v_ref_2198_ = v_ref_2248_;
v_currNamespace_2199_ = v_currNamespace_2249_;
v_openDecls_2200_ = v_openDecls_2250_;
v_initHeartbeats_2201_ = v_initHeartbeats_2251_;
v_maxHeartbeats_2202_ = v_maxHeartbeats_2252_;
v_quotContext_2203_ = v_quotContext_2253_;
v_currMacroScope_2204_ = v_currMacroScope_2254_;
v_cancelTk_x3f_2205_ = v_cancelTk_x3f_2255_;
v_suppressElabErrors_2206_ = v_suppressElabErrors_2256_;
v_inheritedTraceOptions_2207_ = v_inheritedTraceOptions_2257_;
v___y_2208_ = v___y_2244_;
goto v___jp_2187_;
}
v___jp_2258_:
{
if (v___y_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v_env_2269_; lean_object* v_nextMacroScope_2270_; lean_object* v_ngen_2271_; lean_object* v_auxDeclNGen_2272_; lean_object* v_traceState_2273_; lean_object* v_messages_2274_; lean_object* v_infoState_2275_; lean_object* v_snapshotTasks_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2285_; 
v___x_2268_ = lean_st_ref_take(v___y_2263_);
v_env_2269_ = lean_ctor_get(v___x_2268_, 0);
v_nextMacroScope_2270_ = lean_ctor_get(v___x_2268_, 1);
v_ngen_2271_ = lean_ctor_get(v___x_2268_, 2);
v_auxDeclNGen_2272_ = lean_ctor_get(v___x_2268_, 3);
v_traceState_2273_ = lean_ctor_get(v___x_2268_, 4);
v_messages_2274_ = lean_ctor_get(v___x_2268_, 6);
v_infoState_2275_ = lean_ctor_get(v___x_2268_, 7);
v_snapshotTasks_2276_ = lean_ctor_get(v___x_2268_, 8);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2268_, 5);
lean_dec(v_unused_2286_);
v___x_2278_ = v___x_2268_;
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_snapshotTasks_2276_);
lean_inc(v_infoState_2275_);
lean_inc(v_messages_2274_);
lean_inc(v_traceState_2273_);
lean_inc(v_auxDeclNGen_2272_);
lean_inc(v_ngen_2271_);
lean_inc(v_nextMacroScope_2270_);
lean_inc(v_env_2269_);
lean_dec(v___x_2268_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = l_Lean_Kernel_enableDiag(v_env_2269_, v___y_2264_);
lean_inc_ref(v___y_2262_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 5, v___y_2262_);
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_nextMacroScope_2270_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_ngen_2271_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_auxDeclNGen_2272_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_traceState_2273_);
lean_ctor_set(v_reuseFailAlloc_2284_, 5, v___y_2262_);
lean_ctor_set(v_reuseFailAlloc_2284_, 6, v_messages_2274_);
lean_ctor_set(v_reuseFailAlloc_2284_, 7, v_infoState_2275_);
lean_ctor_set(v_reuseFailAlloc_2284_, 8, v_snapshotTasks_2276_);
v___x_2282_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_st_ref_set(v___y_2263_, v___x_2282_);
lean_inc(v___y_2263_);
v___y_2236_ = v___f_2185_;
v___y_2237_ = v___y_2259_;
v___y_2238_ = v___y_2260_;
v___y_2239_ = v___y_2261_;
v___y_2240_ = v___y_2263_;
v___y_2241_ = v___y_2264_;
v___y_2242_ = v___y_2265_;
v___y_2243_ = v___y_2266_;
v___y_2244_ = v___y_2263_;
goto v___jp_2235_;
}
}
}
else
{
lean_inc(v___y_2263_);
v___y_2236_ = v___f_2185_;
v___y_2237_ = v___y_2259_;
v___y_2238_ = v___y_2260_;
v___y_2239_ = v___y_2261_;
v___y_2240_ = v___y_2263_;
v___y_2241_ = v___y_2264_;
v___y_2242_ = v___y_2265_;
v___y_2243_ = v___y_2266_;
v___y_2244_ = v___y_2263_;
goto v___jp_2235_;
}
}
v___jp_2287_:
{
if (v___y_2288_ == 0)
{
lean_dec_ref(v___f_2186_);
lean_dec(v_pkgRoot_2124_);
lean_dec_ref(v_env_2123_);
lean_dec(v_sp_2122_);
if (v_recordExceptions_2184_ == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2289_, 0, v___y_2288_);
v___y_2180_ = v___x_2289_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2291_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*1, v___y_2288_);
v___y_2180_ = v___x_2291_;
goto v___jp_2179_;
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_env_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2294_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2295_ = lean_io_get_num_heartbeats();
v___x_2296_ = l_Lean_firstFrontendMacroScope;
v___x_2297_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2298_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2299_ = lean_box(0);
v___x_2300_ = lean_box(0);
v___x_2301_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2302_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2303_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2304_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2123_);
v___x_2305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2305_, 0, v_env_2123_);
lean_ctor_set(v___x_2305_, 1, v___x_2297_);
lean_ctor_set(v___x_2305_, 2, v___x_2298_);
lean_ctor_set(v___x_2305_, 3, v___x_2301_);
lean_ctor_set(v___x_2305_, 4, v___x_2302_);
lean_ctor_set(v___x_2305_, 5, v___x_2293_);
lean_ctor_set(v___x_2305_, 6, v___x_2294_);
lean_ctor_set(v___x_2305_, 7, v___x_2303_);
lean_ctor_set(v___x_2305_, 8, v___x_2304_);
v___x_2306_ = lean_st_mk_ref(v___x_2305_);
v___x_2307_ = l_Lean_inheritedTraceOptions;
v___x_2308_ = lean_st_ref_get(v___x_2307_);
v___x_2309_ = lean_st_ref_get(v___x_2306_);
v___x_2310_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2311_ = l_Lean_instInhabitedFileMap_default;
v___x_2312_ = l_Lean_Options_empty;
v___x_2313_ = lean_unsigned_to_nat(1000u);
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2316_ = 0;
v___x_2317_ = lean_box(0);
lean_inc(v___x_2308_);
lean_inc(v___x_2295_);
v___x_2318_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2318_, 0, v___x_2310_);
lean_ctor_set(v___x_2318_, 1, v___x_2311_);
lean_ctor_set(v___x_2318_, 2, v___x_2312_);
lean_ctor_set(v___x_2318_, 3, v___x_2292_);
lean_ctor_set(v___x_2318_, 4, v___x_2313_);
lean_ctor_set(v___x_2318_, 5, v___x_2314_);
lean_ctor_set(v___x_2318_, 6, v___x_2299_);
lean_ctor_set(v___x_2318_, 7, v___x_2300_);
lean_ctor_set(v___x_2318_, 8, v___x_2295_);
lean_ctor_set(v___x_2318_, 9, v___x_2315_);
lean_ctor_set(v___x_2318_, 10, v___x_2299_);
lean_ctor_set(v___x_2318_, 11, v___x_2296_);
lean_ctor_set(v___x_2318_, 12, v___x_2317_);
lean_ctor_set(v___x_2318_, 13, v___x_2308_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*14, v___x_2316_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*14 + 1, v___x_2316_);
v_env_2319_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_env_2319_);
lean_dec(v___x_2309_);
v___x_2320_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2321_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2319_);
lean_dec_ref(v_env_2319_);
if (v___x_2321_ == 0)
{
if (v___x_2320_ == 0)
{
lean_dec_ref_known(v___x_2318_, 14);
lean_inc(v___x_2306_);
v___y_2188_ = v___f_2185_;
v___y_2189_ = v___y_2288_;
v___y_2190_ = v___x_2316_;
v___y_2191_ = v___x_2312_;
v___y_2192_ = v___x_2306_;
v___y_2193_ = v___x_2320_;
v___y_2194_ = v___x_2292_;
v_fileName_2195_ = v___x_2310_;
v_fileMap_2196_ = v___x_2311_;
v_currRecDepth_2197_ = v___x_2292_;
v_ref_2198_ = v___x_2314_;
v_currNamespace_2199_ = v___x_2299_;
v_openDecls_2200_ = v___x_2300_;
v_initHeartbeats_2201_ = v___x_2295_;
v_maxHeartbeats_2202_ = v___x_2315_;
v_quotContext_2203_ = v___x_2299_;
v_currMacroScope_2204_ = v___x_2296_;
v_cancelTk_x3f_2205_ = v___x_2317_;
v_suppressElabErrors_2206_ = v___x_2316_;
v_inheritedTraceOptions_2207_ = v___x_2308_;
v___y_2208_ = v___x_2306_;
goto v___jp_2187_;
}
else
{
lean_dec(v___x_2308_);
lean_dec(v___x_2295_);
v___y_2259_ = v___y_2288_;
v___y_2260_ = v___x_2316_;
v___y_2261_ = v___x_2312_;
v___y_2262_ = v___x_2293_;
v___y_2263_ = v___x_2306_;
v___y_2264_ = v___x_2320_;
v___y_2265_ = v___x_2292_;
v___y_2266_ = v___x_2318_;
v___y_2267_ = v___x_2321_;
goto v___jp_2258_;
}
}
else
{
lean_dec(v___x_2308_);
lean_dec(v___x_2295_);
v___y_2259_ = v___y_2288_;
v___y_2260_ = v___x_2316_;
v___y_2261_ = v___x_2312_;
v___y_2262_ = v___x_2293_;
v___y_2263_ = v___x_2306_;
v___y_2264_ = v___x_2320_;
v___y_2265_ = v___x_2292_;
v___y_2266_ = v___x_2318_;
v___y_2267_ = v___x_2320_;
goto v___jp_2258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2327_, lean_object* v_linterOpts_2328_, lean_object* v_sp_2329_, lean_object* v_env_2330_, lean_object* v_pkgRoot_2331_, lean_object* v_docCheckedModules_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2327_, v_linterOpts_2328_, v_sp_2329_, v_env_2330_, v_pkgRoot_2331_, v_docCheckedModules_2332_);
lean_dec_ref(v_linterOpts_2328_);
lean_dec_ref(v_args_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2335_, uint8_t v___y_2336_, lean_object* v_as_2337_, size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2335_, v___y_2336_, v_as_2337_, v_sz_2338_, v_i_2339_, v_b_2340_, v___y_2341_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2345_, lean_object* v___y_2346_, lean_object* v_as_2347_, lean_object* v_sz_2348_, lean_object* v_i_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v___y_9973__boxed_2354_; size_t v_sz_boxed_2355_; size_t v_i_boxed_2356_; lean_object* v_res_2357_; 
v___y_9973__boxed_2354_ = lean_unbox(v___y_2346_);
v_sz_boxed_2355_ = lean_unbox_usize(v_sz_2348_);
lean_dec(v_sz_2348_);
v_i_boxed_2356_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2345_, v___y_9973__boxed_2354_, v_as_2347_, v_sz_boxed_2355_, v_i_boxed_2356_, v_b_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec_ref(v_as_2347_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_enable_initializer_execution();
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_compacted_region_free(v_region_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_2371_, lean_object* v_k_2372_, uint8_t v_v_2373_){
_start:
{
lean_object* v_map_2374_; uint8_t v_hasTrace_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2389_; 
v_map_2374_ = lean_ctor_get(v_o_2371_, 0);
v_hasTrace_2375_ = lean_ctor_get_uint8(v_o_2371_, sizeof(void*)*1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_o_2371_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2377_ = v_o_2371_;
v_isShared_2378_ = v_isSharedCheck_2389_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_map_2374_);
lean_dec(v_o_2371_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2389_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2379_, 0, v_v_2373_);
lean_inc(v_k_2372_);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2372_, v___x_2379_, v_map_2374_);
if (v_hasTrace_2375_ == 0)
{
lean_object* v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2384_; 
v___x_2381_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_2382_ = l_Lean_Name_isPrefixOf(v___x_2381_, v_k_2372_);
lean_dec(v_k_2372_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2384_ = v___x_2377_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2380_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*1, v___x_2382_);
return v___x_2384_;
}
}
else
{
lean_object* v___x_2387_; 
lean_dec(v_k_2372_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2387_ = v___x_2377_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2388_, sizeof(void*)*1, v_hasTrace_2375_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_2390_, lean_object* v_k_2391_, lean_object* v_v_2392_){
_start:
{
uint8_t v_v_boxed_2393_; lean_object* v_res_2394_; 
v_v_boxed_2393_ = lean_unbox(v_v_2392_);
v_res_2394_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_2390_, v_k_2391_, v_v_boxed_2393_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(uint8_t v___x_2398_, lean_object* v_fst_2399_, lean_object* v_as_2400_, size_t v_sz_2401_, size_t v_i_2402_, lean_object* v_b_2403_){
_start:
{
lean_object* v_a_2406_; uint8_t v_anyUnlocated_2410_; 
v_anyUnlocated_2410_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
if (v_anyUnlocated_2410_ == 0)
{
lean_object* v___x_2411_; 
lean_dec(v_fst_2399_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_b_2403_);
return v___x_2411_;
}
else
{
lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2450_; 
v_fst_2412_ = lean_ctor_get(v_b_2403_, 0);
v_snd_2413_ = lean_ctor_get(v_b_2403_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_b_2403_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2415_ = v_b_2403_;
v_isShared_2416_ = v_isSharedCheck_2450_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_snd_2413_);
lean_inc(v_fst_2412_);
lean_dec(v_b_2403_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2450_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v_a_2417_; lean_object* v_position_x3f_2418_; 
v_a_2417_ = lean_array_uget_borrowed(v_as_2400_, v_i_2402_);
v_position_x3f_2418_ = lean_ctor_get(v_a_2417_, 2);
if (lean_obj_tag(v_position_x3f_2418_) == 0)
{
lean_object* v_linter_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v_snd_2413_);
v_linter_2419_ = lean_ctor_get(v_a_2417_, 0);
v___x_2420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__0));
lean_inc(v_linter_2419_);
v___x_2421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2419_, v___x_2398_);
v___x_2422_ = lean_string_append(v___x_2420_, v___x_2421_);
lean_dec_ref(v___x_2421_);
v___x_2423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__1));
v___x_2424_ = lean_string_append(v___x_2422_, v___x_2423_);
lean_inc(v_fst_2399_);
v___x_2425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2399_, v___x_2398_);
v___x_2426_ = lean_string_append(v___x_2424_, v___x_2425_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___closed__2));
v___x_2428_ = lean_string_append(v___x_2426_, v___x_2427_);
v___x_2429_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_dec_ref_known(v___x_2429_, 1);
v___x_2430_ = lean_box(v_anyUnlocated_2410_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2430_);
v___x_2432_ = v___x_2415_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_fst_2412_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
v_a_2406_ = v___x_2432_;
goto v___jp_2405_;
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_del_object(v___x_2415_);
lean_dec(v_fst_2412_);
lean_dec(v_fst_2399_);
v_a_2434_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2429_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2429_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_linter_2442_; lean_object* v_file_2443_; lean_object* v_val_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v_linter_2442_ = lean_ctor_get(v_a_2417_, 0);
v_file_2443_ = lean_ctor_get(v_a_2417_, 3);
v_val_2444_ = lean_ctor_get(v_position_x3f_2418_, 0);
lean_inc(v_linter_2442_);
lean_inc(v_val_2444_);
lean_inc_ref(v_file_2443_);
v___x_2445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2445_, 0, v_file_2443_);
lean_ctor_set(v___x_2445_, 1, v_val_2444_);
lean_ctor_set(v___x_2445_, 2, v_linter_2442_);
v___x_2446_ = lean_array_push(v_fst_2412_, v___x_2445_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2446_);
v___x_2448_ = v___x_2415_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_snd_2413_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v_a_2406_ = v___x_2448_;
goto v___jp_2405_;
}
}
}
}
v___jp_2405_:
{
size_t v___x_2407_; size_t v___x_2408_; 
v___x_2407_ = ((size_t)1ULL);
v___x_2408_ = lean_usize_add(v_i_2402_, v___x_2407_);
v_i_2402_ = v___x_2408_;
v_b_2403_ = v_a_2406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object* v___x_2451_, lean_object* v_fst_2452_, lean_object* v_as_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_b_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v___x_31293__boxed_2458_; size_t v_sz_boxed_2459_; size_t v_i_boxed_2460_; lean_object* v_res_2461_; 
v___x_31293__boxed_2458_ = lean_unbox(v___x_2451_);
v_sz_boxed_2459_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2460_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(v___x_31293__boxed_2458_, v_fst_2452_, v_as_2453_, v_sz_boxed_2459_, v_i_boxed_2460_, v_b_2456_);
lean_dec_ref(v_as_2453_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(uint8_t v___x_2462_, lean_object* v_as_2463_, size_t v_sz_2464_, size_t v_i_2465_, lean_object* v_b_2466_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_lt(v_i_2465_, v_sz_2464_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_b_2466_);
return v___x_2469_;
}
else
{
lean_object* v_a_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v_fst_2473_; lean_object* v_snd_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2497_; 
v_a_2470_ = lean_array_uget_borrowed(v_as_2463_, v_i_2465_);
v_fst_2471_ = lean_ctor_get(v_a_2470_, 0);
v_snd_2472_ = lean_ctor_get(v_a_2470_, 1);
v_fst_2473_ = lean_ctor_get(v_b_2466_, 0);
v_snd_2474_ = lean_ctor_get(v_b_2466_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_b_2466_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2476_ = v_b_2466_;
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_snd_2474_);
lean_inc(v_fst_2473_);
lean_dec(v_b_2466_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_fst_2473_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_snd_2474_);
v___x_2479_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
size_t v_sz_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v_sz_2480_ = lean_array_size(v_snd_2472_);
v___x_2481_ = ((size_t)0ULL);
lean_inc(v_fst_2471_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__8(v___x_2462_, v_fst_2471_, v_snd_2472_, v_sz_2480_, v___x_2481_, v___x_2479_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v_fst_2484_; lean_object* v_snd_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2495_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v_fst_2484_ = lean_ctor_get(v_a_2483_, 0);
v_snd_2485_ = lean_ctor_get(v_a_2483_, 1);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_a_2483_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2487_ = v_a_2483_;
v_isShared_2488_ = v_isSharedCheck_2495_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_snd_2485_);
lean_inc(v_fst_2484_);
lean_dec(v_a_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2495_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_fst_2484_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_snd_2485_);
v___x_2490_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
size_t v___x_2491_; size_t v___x_2492_; 
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_add(v_i_2465_, v___x_2491_);
v_i_2465_ = v___x_2492_;
v_b_2466_ = v___x_2490_;
goto _start;
}
}
}
else
{
return v___x_2482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object* v___x_2498_, lean_object* v_as_2499_, lean_object* v_sz_2500_, lean_object* v_i_2501_, lean_object* v_b_2502_, lean_object* v___y_2503_){
_start:
{
uint8_t v___x_31382__boxed_2504_; size_t v_sz_boxed_2505_; size_t v_i_boxed_2506_; lean_object* v_res_2507_; 
v___x_31382__boxed_2504_ = lean_unbox(v___x_2498_);
v_sz_boxed_2505_ = lean_unbox_usize(v_sz_2500_);
lean_dec(v_sz_2500_);
v_i_boxed_2506_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_res_2507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_31382__boxed_2504_, v_as_2499_, v_sz_boxed_2505_, v_i_boxed_2506_, v_b_2502_);
lean_dec_ref(v_as_2499_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_2508_, lean_object* v_as_2509_, size_t v_i_2510_, size_t v_stop_2511_, lean_object* v_b_2512_){
_start:
{
lean_object* v___y_2514_; uint8_t v___x_2518_; 
v___x_2518_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v_linter_2520_; uint8_t v___x_2521_; 
v___x_2519_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
v_linter_2520_ = lean_ctor_get(v___x_2519_, 0);
v___x_2521_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2520_, v___x_2508_);
if (v___x_2521_ == 0)
{
v___y_2514_ = v_b_2512_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2522_; 
lean_inc(v___x_2519_);
v___x_2522_ = lean_array_push(v_b_2512_, v___x_2519_);
v___y_2514_ = v___x_2522_;
goto v___jp_2513_;
}
}
else
{
return v_b_2512_;
}
v___jp_2513_:
{
size_t v___x_2515_; size_t v___x_2516_; 
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2510_, v___x_2515_);
v_i_2510_ = v___x_2516_;
v_b_2512_ = v___y_2514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_2523_, lean_object* v_as_2524_, lean_object* v_i_2525_, lean_object* v_stop_2526_, lean_object* v_b_2527_){
_start:
{
size_t v_i_boxed_2528_; size_t v_stop_boxed_2529_; lean_object* v_res_2530_; 
v_i_boxed_2528_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_stop_boxed_2529_ = lean_unbox_usize(v_stop_2526_);
lean_dec(v_stop_2526_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2523_, v_as_2524_, v_i_boxed_2528_, v_stop_boxed_2529_, v_b_2527_);
lean_dec_ref(v_as_2524_);
lean_dec_ref(v___x_2523_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(lean_object* v___x_2533_, lean_object* v_as_2534_, size_t v_i_2535_, size_t v_stop_2536_, lean_object* v_b_2537_){
_start:
{
lean_object* v___y_2539_; uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_eq(v_i_2535_, v_stop_2536_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2569_; 
v___x_2544_ = lean_array_uget(v_as_2534_, v_i_2535_);
v_fst_2545_ = lean_ctor_get(v___x_2544_, 0);
v_snd_2546_ = lean_ctor_get(v___x_2544_, 1);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2548_ = v___x_2544_;
v_isShared_2549_ = v_isSharedCheck_2569_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_snd_2546_);
lean_inc(v_fst_2545_);
lean_dec(v___x_2544_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2569_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___y_2552_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_array_get_size(v_snd_2546_);
v___x_2560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___closed__0));
v___x_2561_ = lean_nat_dec_lt(v___x_2550_, v___x_2559_);
if (v___x_2561_ == 0)
{
lean_dec(v_snd_2546_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
else
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_le(v___x_2559_, v___x_2559_);
if (v___x_2562_ == 0)
{
if (v___x_2561_ == 0)
{
lean_dec(v_snd_2546_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2559_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2533_, v_snd_2546_, v___x_2563_, v___x_2564_, v___x_2560_);
lean_dec(v_snd_2546_);
v___y_2552_ = v___x_2565_;
goto v___jp_2551_;
}
}
else
{
size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2559_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_2533_, v_snd_2546_, v___x_2566_, v___x_2567_, v___x_2560_);
lean_dec(v_snd_2546_);
v___y_2552_ = v___x_2568_;
goto v___jp_2551_;
}
}
v___jp_2551_:
{
lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2553_ = lean_array_get_size(v___y_2552_);
v___x_2554_ = lean_nat_dec_eq(v___x_2553_, v___x_2550_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2556_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___y_2552_);
v___x_2556_ = v___x_2548_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_fst_2545_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___y_2552_);
v___x_2556_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_array_push(v_b_2537_, v___x_2556_);
v___y_2539_ = v___x_2557_;
goto v___jp_2538_;
}
}
else
{
lean_dec_ref(v___y_2552_);
lean_del_object(v___x_2548_);
lean_dec(v_fst_2545_);
v___y_2539_ = v_b_2537_;
goto v___jp_2538_;
}
}
}
}
else
{
return v_b_2537_;
}
v___jp_2538_:
{
size_t v___x_2540_; size_t v___x_2541_; 
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2535_, v___x_2540_);
v_i_2535_ = v___x_2541_;
v_b_2537_ = v___y_2539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13___boxed(lean_object* v___x_2570_, lean_object* v_as_2571_, lean_object* v_i_2572_, lean_object* v_stop_2573_, lean_object* v_b_2574_){
_start:
{
size_t v_i_boxed_2575_; size_t v_stop_boxed_2576_; lean_object* v_res_2577_; 
v_i_boxed_2575_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_stop_boxed_2576_ = lean_unbox_usize(v_stop_2573_);
lean_dec(v_stop_2573_);
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2570_, v_as_2571_, v_i_boxed_2575_, v_stop_boxed_2576_, v_b_2574_);
lean_dec_ref(v_as_2571_);
lean_dec_ref(v___x_2570_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(lean_object* v___x_2578_, lean_object* v_as_2579_, lean_object* v_start_2580_, lean_object* v_stop_2581_){
_start:
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2583_ = lean_nat_dec_lt(v_start_2580_, v_stop_2581_);
if (v___x_2583_ == 0)
{
return v___x_2582_;
}
else
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_array_get_size(v_as_2579_);
v___x_2585_ = lean_nat_dec_le(v_stop_2581_, v___x_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
v___x_2586_ = lean_nat_dec_lt(v_start_2580_, v___x_2584_);
if (v___x_2586_ == 0)
{
return v___x_2582_;
}
else
{
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_usize_of_nat(v_start_2580_);
v___x_2588_ = lean_usize_of_nat(v___x_2584_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2578_, v_as_2579_, v___x_2587_, v___x_2588_, v___x_2582_);
return v___x_2589_;
}
}
else
{
size_t v___x_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_usize_of_nat(v_start_2580_);
v___x_2591_ = lean_usize_of_nat(v_stop_2581_);
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_2578_, v_as_2579_, v___x_2590_, v___x_2591_, v___x_2582_);
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object* v___x_2593_, lean_object* v_as_2594_, lean_object* v_start_2595_, lean_object* v_stop_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(v___x_2593_, v_as_2594_, v_start_2595_, v_stop_2596_);
lean_dec(v_stop_2596_);
lean_dec(v_start_2595_);
lean_dec_ref(v_as_2594_);
lean_dec_ref(v___x_2593_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(lean_object* v___x_2598_, uint8_t v_anyFailed_2599_, uint8_t v___y_2600_, lean_object* v_____r_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2605_ = lean_box(v_anyFailed_2599_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2598_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_box(v___y_2600_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2606_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1___boxed(lean_object* v___x_2610_, lean_object* v_anyFailed_2611_, lean_object* v___y_2612_, lean_object* v_____r_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
uint8_t v_anyFailed_boxed_2617_; uint8_t v___y_31560__boxed_2618_; lean_object* v_res_2619_; 
v_anyFailed_boxed_2617_ = lean_unbox(v_anyFailed_2611_);
v___y_31560__boxed_2618_ = lean_unbox(v___y_2612_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_2610_, v_anyFailed_boxed_2617_, v___y_31560__boxed_2618_, v_____r_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(lean_object* v___x_2620_, lean_object* v_as_2621_, size_t v_i_2622_, size_t v_stop_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_eq(v_i_2622_, v_stop_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v_snd_2626_; lean_object* v_size_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2625_ = lean_array_uget_borrowed(v_as_2621_, v_i_2622_);
v_snd_2626_ = lean_ctor_get(v___x_2625_, 1);
v_size_2627_ = lean_ctor_get(v_snd_2626_, 0);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = 1;
v___x_2630_ = lean_nat_dec_eq(v_size_2627_, v___x_2628_);
if (v___x_2630_ == 0)
{
return v___x_2629_;
}
else
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_nat_dec_eq(v___x_2620_, v___x_2628_);
if (v___x_2631_ == 0)
{
size_t v___x_2632_; size_t v___x_2633_; 
v___x_2632_ = ((size_t)1ULL);
v___x_2633_ = lean_usize_add(v_i_2622_, v___x_2632_);
v_i_2622_ = v___x_2633_;
goto _start;
}
else
{
return v___x_2629_;
}
}
}
else
{
uint8_t v___x_2635_; 
v___x_2635_ = 0;
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v___x_2636_, lean_object* v_as_2637_, lean_object* v_i_2638_, lean_object* v_stop_2639_){
_start:
{
size_t v_i_boxed_2640_; size_t v_stop_boxed_2641_; uint8_t v_res_2642_; lean_object* v_r_2643_; 
v_i_boxed_2640_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_stop_boxed_2641_ = lean_unbox_usize(v_stop_2639_);
lean_dec(v_stop_2639_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(v___x_2636_, v_as_2637_, v_i_boxed_2640_, v_stop_boxed_2641_);
lean_dec_ref(v_as_2637_);
lean_dec(v___x_2636_);
v_r_2643_ = lean_box(v_res_2642_);
return v_r_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(lean_object* v___x_2644_, uint8_t v_anyFailed_2645_, lean_object* v_____r_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2650_ = lean_box(v_anyFailed_2645_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2644_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = lean_box(v_anyFailed_2645_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v___x_2651_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0___boxed(lean_object* v___x_2655_, lean_object* v_anyFailed_2656_, lean_object* v_____r_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v_anyFailed_boxed_2661_; lean_object* v_res_2662_; 
v_anyFailed_boxed_2661_ = lean_unbox(v_anyFailed_2656_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_2655_, v_anyFailed_boxed_2661_, v_____r_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_x_2663_, lean_object* v_x_2664_){
_start:
{
if (lean_obj_tag(v_x_2664_) == 0)
{
return v_x_2663_;
}
else
{
lean_object* v_key_2665_; lean_object* v_value_2666_; lean_object* v_tail_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_key_2665_ = lean_ctor_get(v_x_2664_, 0);
v_value_2666_ = lean_ctor_get(v_x_2664_, 1);
v_tail_2667_ = lean_ctor_get(v_x_2664_, 2);
lean_inc(v_value_2666_);
lean_inc(v_key_2665_);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_key_2665_);
lean_ctor_set(v___x_2668_, 1, v_value_2666_);
v___x_2669_ = lean_array_push(v_x_2663_, v___x_2668_);
v_x_2663_ = v___x_2669_;
v_x_2664_ = v_tail_2667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(v_x_2671_, v_x_2672_);
lean_dec(v_x_2672_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_2674_, size_t v_i_2675_, size_t v_stop_2676_, lean_object* v_b_2677_){
_start:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_usize_dec_eq(v_i_2675_, v_stop_2676_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; 
v___x_2679_ = lean_array_uget_borrowed(v_as_2674_, v_i_2675_);
v___x_2680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_BuiltinLint_run_spec__4(v_b_2677_, v___x_2679_);
v___x_2681_ = ((size_t)1ULL);
v___x_2682_ = lean_usize_add(v_i_2675_, v___x_2681_);
v_i_2675_ = v___x_2682_;
v_b_2677_ = v___x_2680_;
goto _start;
}
else
{
return v_b_2677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_2684_, lean_object* v_i_2685_, lean_object* v_stop_2686_, lean_object* v_b_2687_){
_start:
{
size_t v_i_boxed_2688_; size_t v_stop_boxed_2689_; lean_object* v_res_2690_; 
v_i_boxed_2688_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_stop_boxed_2689_ = lean_unbox_usize(v_stop_2686_);
lean_dec(v_stop_2686_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_as_2684_, v_i_boxed_2688_, v_stop_boxed_2689_, v_b_2687_);
lean_dec_ref(v_as_2684_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
lean_ctor_set(v___x_2696_, 2, v___x_2695_);
lean_ctor_set(v___x_2696_, 3, v___x_2695_);
lean_ctor_set(v___x_2696_, 4, v___x_2694_);
lean_ctor_set(v___x_2696_, 5, v___x_2694_);
lean_ctor_set(v___x_2696_, 6, v___x_2694_);
lean_ctor_set(v___x_2696_, 7, v___x_2694_);
lean_ctor_set(v___x_2696_, 8, v___x_2694_);
lean_ctor_set(v___x_2696_, 9, v___x_2694_);
return v___x_2696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_unsigned_to_nat(32u);
v___x_2698_ = lean_mk_empty_array_with_capacity(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2700_ = ((size_t)5ULL);
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_unsigned_to_nat(32u);
v___x_2703_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_2705_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2703_);
lean_ctor_set(v___x_2705_, 2, v___x_2701_);
lean_ctor_set(v___x_2705_, 3, v___x_2701_);
lean_ctor_set_usize(v___x_2705_, 4, v___x_2700_);
return v___x_2705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = lean_box(1);
v___x_2707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_2708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2706_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_2727_ = l_Lean_stringToMessageData(v___x_2726_);
return v___x_2727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_2730_ = l_Lean_stringToMessageData(v___x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_2731_, lean_object* v_declHint_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v_env_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_st_ref_get(v___y_2733_);
v_env_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2735_);
v___x_2737_ = l_Lean_Name_isAnonymous(v_declHint_2732_);
if (v___x_2737_ == 0)
{
uint8_t v_isExporting_2738_; 
v_isExporting_2738_ = lean_ctor_get_uint8(v_env_2736_, sizeof(void*)*8);
if (v_isExporting_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec_ref(v_env_2736_);
lean_dec(v_declHint_2732_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_msg_2731_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
lean_inc_ref(v_env_2736_);
v___x_2740_ = l_Lean_Environment_setExporting(v_env_2736_, v___x_2737_);
lean_inc(v_declHint_2732_);
lean_inc_ref(v___x_2740_);
v___x_2741_ = l_Lean_Environment_contains(v___x_2740_, v_declHint_2732_, v_isExporting_2738_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_env_2736_);
lean_dec(v_declHint_2732_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_msg_2731_);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v_c_2748_; lean_object* v___x_2749_; 
v___x_2743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_2745_ = l_Lean_Options_empty;
v___x_2746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2740_);
lean_ctor_set(v___x_2746_, 1, v___x_2743_);
lean_ctor_set(v___x_2746_, 2, v___x_2744_);
lean_ctor_set(v___x_2746_, 3, v___x_2745_);
lean_inc(v_declHint_2732_);
v___x_2747_ = l_Lean_MessageData_ofConstName(v_declHint_2732_, v___x_2737_);
v_c_2748_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2748_, 0, v___x_2746_);
lean_ctor_set(v_c_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2736_, v_declHint_2732_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec_ref(v_env_2736_);
lean_dec(v_declHint_2732_);
v___x_2750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_c_2748_);
v___x_2752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_MessageData_note(v___x_2753_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_msg_2731_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
else
{
lean_object* v_val_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2792_; 
v_val_2757_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2759_ = v___x_2749_;
v_isShared_2760_ = v_isSharedCheck_2792_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_val_2757_);
lean_dec(v___x_2749_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2792_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_mod_2764_; uint8_t v___x_2765_; 
v___x_2761_ = lean_box(0);
v___x_2762_ = l_Lean_Environment_header(v_env_2736_);
lean_dec_ref(v_env_2736_);
v___x_2763_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2762_);
v_mod_2764_ = lean_array_get(v___x_2761_, v___x_2763_, v_val_2757_);
lean_dec(v_val_2757_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = l_Lean_isPrivateName(v_declHint_2732_);
lean_dec(v_declHint_2732_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_c_2748_);
v___x_2768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Lean_MessageData_ofName(v_mod_2764_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = l_Lean_MessageData_note(v___x_2773_);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_msg_2731_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2775_);
v___x_2777_ = v___x_2759_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v_c_2748_);
v___x_2781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_MessageData_ofName(v_mod_2764_);
v___x_2784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_2786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = l_Lean_MessageData_note(v___x_2786_);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_msg_2731_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2788_);
v___x_2790_ = v___x_2759_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec_ref(v_env_2736_);
lean_dec(v_declHint_2732_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_msg_2731_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_2794_, lean_object* v_declHint_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2794_, v_declHint_2795_, v___y_2796_);
lean_dec(v___y_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(lean_object* v_msg_2799_, lean_object* v_declHint_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2814_; 
v___x_2804_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_2799_, v_declHint_2800_, v___y_2802_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = l_Lean_unknownIdentifierMessageTag;
v___x_2810_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v_a_2805_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_2815_, lean_object* v_declHint_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(v_msg_2815_, v_declHint_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(lean_object* v_msgData_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v_env_2826_; lean_object* v_options_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2825_ = lean_st_ref_get(v___y_2823_);
v_env_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_ref(v_env_2826_);
lean_dec(v___x_2825_);
v_options_2827_ = lean_ctor_get(v___y_2822_, 2);
v___x_2828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_2829_ = lean_unsigned_to_nat(32u);
v___x_2830_ = lean_mk_empty_array_with_capacity(v___x_2829_);
lean_dec_ref(v___x_2830_);
v___x_2831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_2827_);
v___x_2832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2832_, 0, v_env_2826_);
lean_ctor_set(v___x_2832_, 1, v___x_2828_);
lean_ctor_set(v___x_2832_, 2, v___x_2831_);
lean_ctor_set(v___x_2832_, 3, v_options_2827_);
v___x_2833_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v_msgData_2821_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23___boxed(lean_object* v_msgData_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(v_msgData_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_ref_2844_; lean_object* v___x_2845_; lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2854_; 
v_ref_2844_ = lean_ctor_get(v___y_2841_, 5);
v___x_2845_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22_spec__23(v_msg_2840_, v___y_2841_, v___y_2842_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2854_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2854_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_inc(v_ref_2844_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_ref_2844_);
lean_ctor_set(v___x_2850_, 1, v_a_2846_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 1);
lean_ctor_set(v___x_2848_, 0, v___x_2850_);
v___x_2852_ = v___x_2848_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_2860_, lean_object* v_msg_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_fileName_2865_; lean_object* v_fileMap_2866_; lean_object* v_options_2867_; lean_object* v_currRecDepth_2868_; lean_object* v_maxRecDepth_2869_; lean_object* v_ref_2870_; lean_object* v_currNamespace_2871_; lean_object* v_openDecls_2872_; lean_object* v_initHeartbeats_2873_; lean_object* v_maxHeartbeats_2874_; lean_object* v_quotContext_2875_; lean_object* v_currMacroScope_2876_; uint8_t v_diag_2877_; lean_object* v_cancelTk_x3f_2878_; uint8_t v_suppressElabErrors_2879_; lean_object* v_inheritedTraceOptions_2880_; lean_object* v_ref_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_fileName_2865_ = lean_ctor_get(v___y_2862_, 0);
v_fileMap_2866_ = lean_ctor_get(v___y_2862_, 1);
v_options_2867_ = lean_ctor_get(v___y_2862_, 2);
v_currRecDepth_2868_ = lean_ctor_get(v___y_2862_, 3);
v_maxRecDepth_2869_ = lean_ctor_get(v___y_2862_, 4);
v_ref_2870_ = lean_ctor_get(v___y_2862_, 5);
v_currNamespace_2871_ = lean_ctor_get(v___y_2862_, 6);
v_openDecls_2872_ = lean_ctor_get(v___y_2862_, 7);
v_initHeartbeats_2873_ = lean_ctor_get(v___y_2862_, 8);
v_maxHeartbeats_2874_ = lean_ctor_get(v___y_2862_, 9);
v_quotContext_2875_ = lean_ctor_get(v___y_2862_, 10);
v_currMacroScope_2876_ = lean_ctor_get(v___y_2862_, 11);
v_diag_2877_ = lean_ctor_get_uint8(v___y_2862_, sizeof(void*)*14);
v_cancelTk_x3f_2878_ = lean_ctor_get(v___y_2862_, 12);
v_suppressElabErrors_2879_ = lean_ctor_get_uint8(v___y_2862_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2880_ = lean_ctor_get(v___y_2862_, 13);
v_ref_2881_ = l_Lean_replaceRef(v_ref_2860_, v_ref_2870_);
lean_inc_ref(v_inheritedTraceOptions_2880_);
lean_inc(v_cancelTk_x3f_2878_);
lean_inc(v_currMacroScope_2876_);
lean_inc(v_quotContext_2875_);
lean_inc(v_maxHeartbeats_2874_);
lean_inc(v_initHeartbeats_2873_);
lean_inc(v_openDecls_2872_);
lean_inc(v_currNamespace_2871_);
lean_inc(v_maxRecDepth_2869_);
lean_inc(v_currRecDepth_2868_);
lean_inc_ref(v_options_2867_);
lean_inc_ref(v_fileMap_2866_);
lean_inc_ref(v_fileName_2865_);
v___x_2882_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2882_, 0, v_fileName_2865_);
lean_ctor_set(v___x_2882_, 1, v_fileMap_2866_);
lean_ctor_set(v___x_2882_, 2, v_options_2867_);
lean_ctor_set(v___x_2882_, 3, v_currRecDepth_2868_);
lean_ctor_set(v___x_2882_, 4, v_maxRecDepth_2869_);
lean_ctor_set(v___x_2882_, 5, v_ref_2881_);
lean_ctor_set(v___x_2882_, 6, v_currNamespace_2871_);
lean_ctor_set(v___x_2882_, 7, v_openDecls_2872_);
lean_ctor_set(v___x_2882_, 8, v_initHeartbeats_2873_);
lean_ctor_set(v___x_2882_, 9, v_maxHeartbeats_2874_);
lean_ctor_set(v___x_2882_, 10, v_quotContext_2875_);
lean_ctor_set(v___x_2882_, 11, v_currMacroScope_2876_);
lean_ctor_set(v___x_2882_, 12, v_cancelTk_x3f_2878_);
lean_ctor_set(v___x_2882_, 13, v_inheritedTraceOptions_2880_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*14, v_diag_2877_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*14 + 1, v_suppressElabErrors_2879_);
v___x_2883_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_2861_, v___x_2882_, v___y_2863_);
lean_dec_ref_known(v___x_2882_, 14);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_2884_, lean_object* v_msg_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_2884_, v_msg_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v_ref_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(lean_object* v_ref_2890_, lean_object* v_msg_2891_, lean_object* v_declHint_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v_a_2897_; lean_object* v___x_2898_; 
v___x_2896_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19(v_msg_2891_, v_declHint_2892_, v___y_2893_, v___y_2894_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_2890_, v_a_2897_, v___y_2893_, v___y_2894_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg___boxed(lean_object* v_ref_2899_, lean_object* v_msg_2900_, lean_object* v_declHint_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_2899_, v_msg_2900_, v_declHint_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v_ref_2899_);
return v_res_2905_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__0));
v___x_2908_ = l_Lean_stringToMessageData(v___x_2907_);
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_2910_ = l_Lean_stringToMessageData(v___x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(lean_object* v_ref_2911_, lean_object* v_constName_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2916_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__1);
v___x_2917_ = 0;
lean_inc(v_constName_2912_);
v___x_2918_ = l_Lean_MessageData_ofConstName(v_constName_2912_, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2916_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___closed__2);
v___x_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_2911_, v___x_2921_, v_constName_2912_, v___y_2913_, v___y_2914_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg___boxed(lean_object* v_ref_2923_, lean_object* v_constName_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_2923_, v_constName_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_ref_2923_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_ref_2933_; lean_object* v___x_2934_; 
v_ref_2933_ = lean_ctor_get(v___y_2930_, 5);
v___x_2934_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_2933_, v_constName_2929_, v___y_2930_, v___y_2931_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(lean_object* v_constName_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v_env_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2944_ = lean_st_ref_get(v___y_2942_);
v_env_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc_ref(v_env_2945_);
lean_dec(v___x_2944_);
v___x_2946_ = 0;
lean_inc(v_constName_2940_);
v___x_2947_ = l_Lean_Environment_find_x3f(v_env_2945_, v_constName_2940_, v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_2940_, v___y_2941_, v___y_2942_);
return v___x_2948_;
}
else
{
lean_object* v_val_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_constName_2940_);
v_val_2949_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2947_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_val_2949_);
lean_dec(v___x_2947_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_val_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2___boxed(lean_object* v_constName_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(v_constName_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_declName_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
lean_inc(v_declName_2962_);
v___x_2966_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2(v_declName_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2993_; 
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v___x_2966_, 0);
lean_dec(v_unused_2994_);
v___x_2968_ = v___x_2966_;
v_isShared_2969_ = v_isSharedCheck_2993_;
goto v_resetjp_2967_;
}
else
{
lean_dec(v___x_2966_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2993_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v_env_2971_; lean_object* v___x_2972_; 
v___x_2970_ = lean_st_ref_get(v___y_2964_);
v_env_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc_ref(v_env_2971_);
lean_dec(v___x_2970_);
v___x_2972_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2971_, v_declName_2962_);
lean_dec(v_declName_2962_);
lean_dec_ref(v_env_2971_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = lean_box(0);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2973_);
v___x_2975_ = v___x_2968_;
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
else
{
lean_object* v_val_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2992_; 
v_val_2977_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2979_ = v___x_2972_;
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_val_2977_);
lean_dec(v___x_2972_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v_env_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2981_ = lean_st_ref_get(v___y_2964_);
v_env_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref(v_env_2982_);
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v___x_2984_ = l_Lean_Environment_allImportedModuleNames(v_env_2982_);
lean_dec_ref(v_env_2982_);
v___x_2985_ = lean_array_get(v___x_2983_, v___x_2984_, v_val_2977_);
lean_dec(v_val_2977_);
lean_dec_ref(v___x_2984_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2985_);
v___x_2987_ = v___x_2979_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2987_);
v___x_2989_ = v___x_2968_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
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
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_declName_2962_);
v_a_2995_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2966_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2966_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_declName_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(v_declName_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(uint8_t v___x_3009_, lean_object* v_fst_3010_, lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v_as_3013_, size_t v_sz_3014_, size_t v_i_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_a_3021_; uint8_t v_anyUnlocated_3025_; 
v_anyUnlocated_3025_ = lean_usize_dec_lt(v_i_3015_, v_sz_3014_);
if (v_anyUnlocated_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_b_3016_);
return v___x_3026_;
}
else
{
lean_object* v_a_3027_; lean_object* v_fst_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3163_; 
v_a_3027_ = lean_array_uget(v_as_3013_, v_i_3015_);
v_fst_3028_ = lean_ctor_get(v_a_3027_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_a_3027_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v_a_3027_, 1);
lean_dec(v_unused_3164_);
v___x_3030_ = v_a_3027_;
v_isShared_3031_ = v_isSharedCheck_3163_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_fst_3028_);
lean_dec(v_a_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3163_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; 
lean_inc(v_fst_3028_);
v___x_3032_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3028_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
if (lean_obj_tag(v_a_3033_) == 0)
{
lean_object* v_fst_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3068_; 
v_fst_3034_ = lean_ctor_get(v_b_3016_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_b_3016_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v_b_3016_, 1);
lean_dec(v_unused_3069_);
v___x_3036_ = v_b_3016_;
v_isShared_3037_ = v_isSharedCheck_3068_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_fst_3034_);
lean_dec(v_b_3016_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3068_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_optName_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_optName_3038_ = lean_ctor_get(v_fst_3010_, 1);
v___x_3039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0));
v___x_3040_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3028_, v___x_3009_);
v___x_3041_ = lean_string_append(v___x_3039_, v___x_3040_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3043_ = lean_string_append(v___x_3041_, v___x_3042_);
lean_inc(v_optName_3038_);
v___x_3044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3038_, v___x_3009_);
v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3047_ = lean_string_append(v___x_3045_, v___x_3046_);
v___x_3048_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_dec_ref_known(v___x_3048_, 1);
lean_del_object(v___x_3030_);
v___x_3049_ = lean_box(v_anyUnlocated_3025_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v___x_3049_);
v___x_3051_ = v___x_3036_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_fst_3034_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
v_a_3021_ = v___x_3051_;
goto v___jp_3020_;
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_3036_);
lean_dec(v_fst_3034_);
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v_a_3053_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3055_ = v___x_3048_;
v_isShared_3056_ = v_isSharedCheck_3067_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3048_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3067_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_ref_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v_ref_3057_ = lean_ctor_get(v___y_3017_, 5);
v___x_3058_ = lean_io_error_to_string(v_a_3053_);
v___x_3059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
v___x_3060_ = l_Lean_MessageData_ofFormat(v___x_3059_);
lean_inc(v_ref_3057_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3060_);
lean_ctor_set(v___x_3030_, 0, v_ref_3057_);
v___x_3062_ = v___x_3030_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_ref_3057_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3064_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3062_);
v___x_3064_ = v___x_3055_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3070_; lean_object* v_snd_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3154_; 
v_fst_3070_ = lean_ctor_get(v_b_3016_, 0);
v_snd_3071_ = lean_ctor_get(v_b_3016_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_b_3016_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3073_ = v_b_3016_;
v_isShared_3074_ = v_isSharedCheck_3154_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_snd_3071_);
lean_inc(v_fst_3070_);
lean_dec(v_b_3016_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3154_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_val_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3153_; 
v_val_3075_ = lean_ctor_get(v_a_3033_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_a_3033_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3077_ = v_a_3033_;
v_isShared_3078_ = v_isSharedCheck_3153_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_val_3075_);
lean_dec(v_a_3033_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3153_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2(v_fst_3028_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___y_3082_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
if (lean_obj_tag(v_a_3080_) == 0)
{
lean_inc(v___x_3012_);
v___y_3082_ = v___x_3012_;
goto v___jp_3081_;
}
else
{
lean_object* v_val_3144_; 
v_val_3144_ = lean_ctor_get(v_a_3080_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v_a_3080_, 1);
v___y_3082_ = v_val_3144_;
goto v___jp_3081_;
}
v___jp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3082_);
lean_inc(v___x_3011_);
v___x_3084_ = l_Lean_SearchPath_findWithExt(v___x_3011_, v___x_3083_, v___y_3082_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
if (lean_obj_tag(v_a_3085_) == 0)
{
lean_object* v_optName_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_dec(v_val_3075_);
lean_dec(v_snd_3071_);
v_optName_3086_ = lean_ctor_get(v_fst_3010_, 1);
v___x_3087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3088_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3082_, v___x_3009_);
v___x_3089_ = lean_string_append(v___x_3087_, v___x_3088_);
lean_dec_ref(v___x_3088_);
v___x_3090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
lean_inc(v_optName_3086_);
v___x_3092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3086_, v___x_3009_);
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
v___x_3096_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
lean_dec_ref_known(v___x_3096_, 1);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3030_);
v___x_3097_ = lean_box(v_anyUnlocated_3025_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3097_);
v___x_3099_ = v___x_3073_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_fst_3070_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
v_a_3021_ = v___x_3099_;
goto v___jp_3020_;
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3073_);
lean_dec(v_fst_3070_);
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v_a_3101_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3103_ = v___x_3096_;
v_isShared_3104_ = v_isSharedCheck_3117_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3096_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3117_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v_ref_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v_ref_3105_ = lean_ctor_get(v___y_3017_, 5);
v___x_3106_ = lean_io_error_to_string(v_a_3101_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 3);
lean_ctor_set(v___x_3077_, 0, v___x_3106_);
v___x_3108_ = v___x_3077_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = l_Lean_MessageData_ofFormat(v___x_3108_);
lean_inc(v_ref_3105_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3109_);
lean_ctor_set(v___x_3030_, 0, v_ref_3105_);
v___x_3111_ = v___x_3030_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_ref_3105_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3111_);
v___x_3113_ = v___x_3103_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
else
{
lean_object* v_range_3118_; lean_object* v_val_3119_; lean_object* v_pos_3120_; lean_object* v_optName_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
lean_dec(v___y_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3030_);
v_range_3118_ = lean_ctor_get(v_val_3075_, 0);
lean_inc_ref(v_range_3118_);
lean_dec(v_val_3075_);
v_val_3119_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_a_3085_, 1);
v_pos_3120_ = lean_ctor_get(v_range_3118_, 0);
lean_inc_ref(v_pos_3120_);
lean_dec_ref(v_range_3118_);
v_optName_3121_ = lean_ctor_get(v_fst_3010_, 1);
lean_inc(v_optName_3121_);
v___x_3122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3122_, 0, v_val_3119_);
lean_ctor_set(v___x_3122_, 1, v_pos_3120_);
lean_ctor_set(v___x_3122_, 2, v_optName_3121_);
v___x_3123_ = lean_array_push(v_fst_3070_, v___x_3122_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3123_);
v___x_3125_ = v___x_3073_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_snd_3071_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
v_a_3021_ = v___x_3125_;
goto v___jp_3020_;
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v___y_3082_);
lean_dec(v_val_3075_);
lean_del_object(v___x_3073_);
lean_dec(v_snd_3071_);
lean_dec(v_fst_3070_);
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v_a_3127_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3129_ = v___x_3084_;
v_isShared_3130_ = v_isSharedCheck_3143_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3084_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3143_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v_ref_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v_ref_3131_ = lean_ctor_get(v___y_3017_, 5);
v___x_3132_ = lean_io_error_to_string(v_a_3127_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set_tag(v___x_3077_, 3);
lean_ctor_set(v___x_3077_, 0, v___x_3132_);
v___x_3134_ = v___x_3077_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = l_Lean_MessageData_ofFormat(v___x_3134_);
lean_inc(v_ref_3131_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3135_);
lean_ctor_set(v___x_3030_, 0, v_ref_3131_);
v___x_3137_ = v___x_3030_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_ref_3131_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3139_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3137_);
v___x_3139_ = v___x_3129_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_del_object(v___x_3077_);
lean_dec(v_val_3075_);
lean_del_object(v___x_3073_);
lean_dec(v_snd_3071_);
lean_dec(v_fst_3070_);
lean_del_object(v___x_3030_);
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v_a_3145_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3079_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3079_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_del_object(v___x_3030_);
lean_dec(v_fst_3028_);
lean_dec_ref(v_b_3016_);
lean_dec(v___x_3012_);
lean_dec(v___x_3011_);
lean_dec_ref(v_fst_3010_);
v_a_3155_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3032_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3032_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
v___jp_3020_:
{
size_t v___x_3022_; size_t v___x_3023_; 
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_add(v_i_3015_, v___x_3022_);
v_i_3015_ = v___x_3023_;
v_b_3016_ = v_a_3021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_3165_, lean_object* v_fst_3166_, lean_object* v___x_3167_, lean_object* v___x_3168_, lean_object* v_as_3169_, lean_object* v_sz_3170_, lean_object* v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v___x_32244__boxed_3176_; size_t v_sz_boxed_3177_; size_t v_i_boxed_3178_; lean_object* v_res_3179_; 
v___x_32244__boxed_3176_ = lean_unbox(v___x_3165_);
v_sz_boxed_3177_ = lean_unbox_usize(v_sz_3170_);
lean_dec(v_sz_3170_);
v_i_boxed_3178_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_res_3179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_32244__boxed_3176_, v_fst_3166_, v___x_3167_, v___x_3168_, v_as_3169_, v_sz_boxed_3177_, v_i_boxed_3178_, v_b_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_as_3169_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(uint8_t v___x_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v_as_3183_, size_t v_sz_3184_, size_t v_i_3185_, lean_object* v_b_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_usize_dec_lt(v_i_3185_, v_sz_3184_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_b_3186_);
return v___x_3191_;
}
else
{
lean_object* v_a_3192_; lean_object* v_fst_3193_; lean_object* v_snd_3194_; lean_object* v_fst_3195_; lean_object* v_snd_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3234_; 
v_a_3192_ = lean_array_uget_borrowed(v_as_3183_, v_i_3185_);
v_fst_3193_ = lean_ctor_get(v_a_3192_, 0);
v_snd_3194_ = lean_ctor_get(v_a_3192_, 1);
v_fst_3195_ = lean_ctor_get(v_b_3186_, 0);
v_snd_3196_ = lean_ctor_get(v_b_3186_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_b_3186_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3198_ = v_b_3186_;
v_isShared_3199_ = v_isSharedCheck_3234_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_snd_3196_);
lean_inc(v_fst_3195_);
lean_dec(v_b_3186_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3234_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___y_3201_; lean_object* v_size_3221_; lean_object* v_buckets_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_size_3221_ = lean_ctor_get(v_snd_3194_, 0);
v_buckets_3222_ = lean_ctor_get(v_snd_3194_, 1);
v___x_3223_ = lean_mk_empty_array_with_capacity(v_size_3221_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_array_get_size(v_buckets_3222_);
v___x_3226_ = lean_nat_dec_lt(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
v___y_3201_ = v___x_3223_;
goto v___jp_3200_;
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_nat_dec_le(v___x_3225_, v___x_3225_);
if (v___x_3227_ == 0)
{
if (v___x_3226_ == 0)
{
v___y_3201_ = v___x_3223_;
goto v___jp_3200_;
}
else
{
size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = ((size_t)0ULL);
v___x_3229_ = lean_usize_of_nat(v___x_3225_);
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_buckets_3222_, v___x_3228_, v___x_3229_, v___x_3223_);
v___y_3201_ = v___x_3230_;
goto v___jp_3200_;
}
}
else
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = lean_usize_of_nat(v___x_3225_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__5(v_buckets_3222_, v___x_3231_, v___x_3232_, v___x_3223_);
v___y_3201_ = v___x_3233_;
goto v___jp_3200_;
}
}
v___jp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3199_ == 0)
{
v___x_3203_ = v___x_3198_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_fst_3195_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_snd_3196_);
v___x_3203_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
size_t v_sz_3204_; size_t v___x_3205_; lean_object* v___x_3206_; 
v_sz_3204_ = lean_array_size(v___y_3201_);
v___x_3205_ = ((size_t)0ULL);
lean_inc(v___x_3182_);
lean_inc(v___x_3181_);
lean_inc(v_fst_3193_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_3180_, v_fst_3193_, v___x_3181_, v___x_3182_, v___y_3201_, v_sz_3204_, v___x_3205_, v___x_3203_, v___y_3187_, v___y_3188_);
lean_dec_ref(v___y_3201_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v_fst_3208_; lean_object* v_snd_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3219_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3206_, 1);
v_fst_3208_ = lean_ctor_get(v_a_3207_, 0);
v_snd_3209_ = lean_ctor_get(v_a_3207_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_a_3207_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3211_ = v_a_3207_;
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_snd_3209_);
lean_inc(v_fst_3208_);
lean_dec(v_a_3207_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_fst_3208_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_snd_3209_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
size_t v___x_3215_; size_t v___x_3216_; 
v___x_3215_ = ((size_t)1ULL);
v___x_3216_ = lean_usize_add(v_i_3185_, v___x_3215_);
v_i_3185_ = v___x_3216_;
v_b_3186_ = v___x_3214_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
return v___x_3206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v_as_3238_, lean_object* v_sz_3239_, lean_object* v_i_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
uint8_t v___x_32533__boxed_3245_; size_t v_sz_boxed_3246_; size_t v_i_boxed_3247_; lean_object* v_res_3248_; 
v___x_32533__boxed_3245_ = lean_unbox(v___x_3235_);
v_sz_boxed_3246_ = lean_unbox_usize(v_sz_3239_);
lean_dec(v_sz_3239_);
v_i_boxed_3247_ = lean_unbox_usize(v_i_3240_);
lean_dec(v_i_3240_);
v_res_3248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_32533__boxed_3245_, v___x_3236_, v___x_3237_, v_as_3238_, v_sz_boxed_3246_, v_i_boxed_3247_, v_b_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_as_3238_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(lean_object* v_as_3249_, size_t v_i_3250_, size_t v_stop_3251_, lean_object* v_b_3252_){
_start:
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_usize_dec_eq(v_i_3250_, v_stop_3251_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v_fst_3255_; lean_object* v_snd_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; size_t v___x_3259_; size_t v___x_3260_; 
v___x_3254_ = lean_array_uget_borrowed(v_as_3249_, v_i_3250_);
v_fst_3255_ = lean_ctor_get(v___x_3254_, 0);
v_snd_3256_ = lean_ctor_get(v___x_3254_, 1);
v___x_3257_ = lean_unbox(v_snd_3256_);
lean_inc(v_fst_3255_);
v___x_3258_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_3252_, v_fst_3255_, v___x_3257_);
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3250_, v___x_3259_);
v_i_3250_ = v___x_3260_;
v_b_3252_ = v___x_3258_;
goto _start;
}
else
{
return v_b_3252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13___boxed(lean_object* v_as_3262_, lean_object* v_i_3263_, lean_object* v_stop_3264_, lean_object* v_b_3265_){
_start:
{
size_t v_i_boxed_3266_; size_t v_stop_boxed_3267_; lean_object* v_res_3268_; 
v_i_boxed_3266_ = lean_unbox_usize(v_i_3263_);
lean_dec(v_i_3263_);
v_stop_boxed_3267_ = lean_unbox_usize(v_stop_3264_);
lean_dec(v_stop_3264_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_as_3262_, v_i_boxed_3266_, v_stop_boxed_3267_, v_b_3265_);
lean_dec_ref(v_as_3262_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(lean_object* v___x_3269_, lean_object* v_as_3270_, size_t v_sz_3271_, size_t v_i_3272_, lean_object* v_b_3273_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_usize_dec_lt(v_i_3272_, v_sz_3271_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_b_3273_);
return v___x_3276_;
}
else
{
lean_object* v_a_3277_; lean_object* v_message_3278_; lean_object* v___x_3279_; uint8_t v_anyFailed_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_a_3277_ = lean_array_uget_borrowed(v_as_3270_, v_i_3272_);
v_message_3278_ = lean_ctor_get(v_a_3277_, 1);
v___x_3279_ = lean_unsigned_to_nat(0u);
v_anyFailed_3280_ = lean_nat_dec_eq(v___x_3269_, v___x_3279_);
lean_inc_ref(v_message_3278_);
v___x_3281_ = l_Lean_SerialMessage_toString(v_message_3278_, v_anyFailed_3280_);
v___x_3282_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v___x_3283_; size_t v___x_3284_; size_t v___x_3285_; 
lean_dec_ref_known(v___x_3282_, 1);
v___x_3283_ = lean_box(0);
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3272_, v___x_3284_);
v_i_3272_ = v___x_3285_;
v_b_3273_ = v___x_3283_;
goto _start;
}
else
{
return v___x_3282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object* v___x_3287_, lean_object* v_as_3288_, lean_object* v_sz_3289_, lean_object* v_i_3290_, lean_object* v_b_3291_, lean_object* v___y_3292_){
_start:
{
size_t v_sz_boxed_3293_; size_t v_i_boxed_3294_; lean_object* v_res_3295_; 
v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3289_);
lean_dec(v_sz_3289_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3290_);
lean_dec(v_i_3290_);
v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___x_3287_, v_as_3288_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3291_);
lean_dec_ref(v_as_3288_);
lean_dec(v___x_3287_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(lean_object* v___x_3298_, lean_object* v_as_3299_, size_t v_sz_3300_, size_t v_i_3301_, lean_object* v_b_3302_){
_start:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_usize_dec_lt(v_i_3301_, v_sz_3300_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v_b_3302_);
return v___x_3305_;
}
else
{
lean_object* v_a_3306_; lean_object* v_fst_3307_; lean_object* v_snd_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3306_ = lean_array_uget_borrowed(v_as_3299_, v_i_3301_);
v_fst_3307_ = lean_ctor_get(v_a_3306_, 0);
v_snd_3308_ = lean_ctor_get(v_a_3306_, 1);
v___x_3309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__0));
lean_inc(v_fst_3307_);
v___x_3310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3307_, v___x_3304_);
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___closed__1));
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
v___x_3314_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3313_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v___x_3315_; size_t v_sz_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref_known(v___x_3314_, 1);
v___x_3315_ = lean_box(0);
v_sz_3316_ = lean_array_size(v_snd_3308_);
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__9(v___x_3298_, v_snd_3308_, v_sz_3316_, v___x_3317_, v___x_3315_);
if (lean_obj_tag(v___x_3318_) == 0)
{
size_t v___x_3319_; size_t v___x_3320_; 
lean_dec_ref_known(v___x_3318_, 1);
v___x_3319_ = ((size_t)1ULL);
v___x_3320_ = lean_usize_add(v_i_3301_, v___x_3319_);
v_i_3301_ = v___x_3320_;
v_b_3302_ = v___x_3315_;
goto _start;
}
else
{
return v___x_3318_;
}
}
else
{
return v___x_3314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object* v___x_3322_, lean_object* v_as_3323_, lean_object* v_sz_3324_, lean_object* v_i_3325_, lean_object* v_b_3326_, lean_object* v___y_3327_){
_start:
{
size_t v_sz_boxed_3328_; size_t v_i_boxed_3329_; lean_object* v_res_3330_; 
v_sz_boxed_3328_ = lean_unbox_usize(v_sz_3324_);
lean_dec(v_sz_3324_);
v_i_boxed_3329_ = lean_unbox_usize(v_i_3325_);
lean_dec(v_i_3325_);
v_res_3330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(v___x_3322_, v_as_3323_, v_sz_boxed_3328_, v_i_boxed_3329_, v_b_3326_);
lean_dec_ref(v_as_3323_);
lean_dec(v___x_3322_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(lean_object* v___x_3342_, lean_object* v_args_3343_, lean_object* v___x_3344_, lean_object* v_as_3345_, size_t v_sz_3346_, size_t v_i_3347_, lean_object* v_b_3348_){
_start:
{
lean_object* v_a_3351_; lean_object* v_a_3356_; lean_object* v_msg_3360_; lean_object* v___x_3364_; uint8_t v_anyFailed_3365_; uint8_t v_anyUnlocated_3366_; lean_object* v_a_3368_; lean_object* v___x_3381_; lean_object* v_envLinterModule_3382_; uint8_t v___x_3383_; 
v___x_3364_ = lean_unsigned_to_nat(0u);
v_anyFailed_3365_ = lean_nat_dec_eq(v___x_3342_, v___x_3364_);
v_anyUnlocated_3366_ = 1;
v___x_3381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__3));
v_envLinterModule_3382_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_3382_, 0, v___x_3381_);
lean_ctor_set_uint8(v_envLinterModule_3382_, sizeof(void*)*1, v_anyFailed_3365_);
lean_ctor_set_uint8(v_envLinterModule_3382_, sizeof(void*)*1 + 1, v_anyUnlocated_3366_);
lean_ctor_set_uint8(v_envLinterModule_3382_, sizeof(void*)*1 + 2, v_anyFailed_3365_);
v___x_3383_ = lean_usize_dec_lt(v_i_3347_, v_sz_3346_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref_known(v_envLinterModule_3382_, 1);
lean_dec(v___x_3344_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_b_3348_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v_a_3386_; lean_object* v___x_3387_; 
v___x_3385_ = lean_enable_initializer_execution();
v_a_3386_ = lean_array_uget_borrowed(v_as_3345_, v_i_3347_);
lean_inc(v_a_3386_);
v___x_3387_ = l_Lean_findOLean(v_a_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = l_Lean_readModuleData(v_a_3388_);
lean_dec(v_a_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v_fst_3391_; lean_object* v_snd_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3889_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v_fst_3391_ = lean_ctor_get(v_a_3390_, 0);
v_snd_3392_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3394_ = v_a_3390_;
v_isShared_3395_ = v_isSharedCheck_3889_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_snd_3392_);
lean_inc(v_fst_3391_);
lean_dec(v_a_3390_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3889_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
uint8_t v___x_3396_; lean_object* v_snd_3397_; lean_object* v_snd_3398_; lean_object* v_fst_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3887_; 
v___x_3396_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_3391_);
lean_dec(v_fst_3391_);
v_snd_3397_ = lean_ctor_get(v_b_3348_, 1);
lean_inc(v_snd_3397_);
v_snd_3398_ = lean_ctor_get(v_snd_3397_, 1);
lean_inc(v_snd_3398_);
v_fst_3399_ = lean_ctor_get(v_b_3348_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_b_3348_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v_b_3348_, 1);
lean_dec(v_unused_3888_);
v___x_3401_ = v_b_3348_;
v_isShared_3402_ = v_isSharedCheck_3887_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_fst_3399_);
lean_dec(v_b_3348_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3887_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_fst_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3885_; 
v_fst_3403_ = lean_ctor_get(v_snd_3397_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_snd_3397_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v_snd_3397_, 1);
lean_dec(v_unused_3886_);
v___x_3405_ = v_snd_3397_;
v_isShared_3406_ = v_isSharedCheck_3885_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_fst_3403_);
lean_dec(v_snd_3397_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3885_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_fst_3407_; lean_object* v_snd_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3884_; 
v_fst_3407_ = lean_ctor_get(v_snd_3398_, 0);
v_snd_3408_ = lean_ctor_get(v_snd_3398_, 1);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_snd_3398_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3410_ = v_snd_3398_;
v_isShared_3411_ = v_isSharedCheck_3884_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_snd_3408_);
lean_inc(v_fst_3407_);
lean_dec(v_snd_3398_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3884_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; uint8_t v_anyFailed_3418_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; uint8_t v___y_3487_; uint8_t v_anyUnlocated_3488_; lean_object* v___y_3491_; uint8_t v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; lean_object* v_a_3498_; lean_object* v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3516_; lean_object* v___x_3519_; lean_object* v___y_3521_; uint8_t v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; uint8_t v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3648_; uint8_t v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; uint8_t v___y_3653_; lean_object* v___y_3654_; uint8_t v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; uint8_t v___y_3701_; lean_object* v___y_3702_; uint8_t v___y_3703_; uint8_t v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; uint8_t v___y_3707_; uint8_t v___y_3708_; uint8_t v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; uint8_t v___y_3734_; lean_object* v___y_3735_; uint8_t v___y_3736_; lean_object* v_records_3737_; uint8_t v_anyUnlocated_3738_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; uint8_t v___y_3773_; lean_object* v___y_3774_; uint8_t v___y_3775_; uint8_t v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; uint8_t v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; uint8_t v___y_3820_; lean_object* v___y_3821_; uint8_t v___y_3842_; 
v___x_3519_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
if (v___x_3396_ == 0)
{
uint8_t v___x_3882_; 
v___x_3882_ = 2;
v___y_3842_ = v___x_3882_;
goto v___jp_3841_;
}
else
{
uint8_t v___x_3883_; 
v___x_3883_ = 1;
v___y_3842_ = v___x_3883_;
goto v___jp_3841_;
}
v___jp_3412_:
{
lean_object* v___x_3419_; 
lean_inc(v___x_3344_);
v___x_3419_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_3343_, v___y_3417_, v___x_3344_, v___y_3414_, v___y_3413_, v_snd_3408_);
lean_dec_ref(v___y_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v_outcome_3421_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v_outcome_3421_ = lean_ctor_get(v_a_3420_, 0);
if (lean_obj_tag(v_outcome_3421_) == 0)
{
uint8_t v_failed_3422_; 
v_failed_3422_ = lean_ctor_get_uint8(v_outcome_3421_, 0);
if (v_failed_3422_ == 0)
{
lean_object* v_checkedModules_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v_checkedModules_3423_ = lean_ctor_get(v_a_3420_, 1);
lean_inc(v_checkedModules_3423_);
lean_dec(v_a_3420_);
v___x_3424_ = lean_box(v___y_3415_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_checkedModules_3423_);
lean_ctor_set(v___x_3410_, 0, v___x_3424_);
v___x_3426_ = v___x_3410_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_checkedModules_3423_);
v___x_3426_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3426_);
lean_ctor_set(v___x_3405_, 0, v___y_3416_);
v___x_3428_ = v___x_3405_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___y_3416_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_box(v_anyFailed_3418_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3428_);
lean_ctor_set(v___x_3401_, 0, v___x_3429_);
v___x_3431_ = v___x_3401_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3428_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
v_a_3351_ = v___x_3431_;
goto v___jp_3350_;
}
}
}
}
else
{
lean_object* v_checkedModules_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v_checkedModules_3435_ = lean_ctor_get(v_a_3420_, 1);
lean_inc(v_checkedModules_3435_);
lean_dec(v_a_3420_);
v___x_3436_ = lean_box(v___y_3415_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_checkedModules_3435_);
lean_ctor_set(v___x_3410_, 0, v___x_3436_);
v___x_3438_ = v___x_3410_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_checkedModules_3435_);
v___x_3438_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3438_);
lean_ctor_set(v___x_3405_, 0, v___y_3416_);
v___x_3440_ = v___x_3405_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___y_3416_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = lean_box(v_anyUnlocated_3366_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3440_);
lean_ctor_set(v___x_3401_, 0, v___x_3441_);
v___x_3443_ = v___x_3401_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3440_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
v_a_3351_ = v___x_3443_;
goto v___jp_3350_;
}
}
}
}
}
else
{
lean_object* v_checkedModules_3447_; lean_object* v_records_3448_; uint8_t v_unlocated_3449_; lean_object* v___x_3450_; 
lean_inc_ref(v_outcome_3421_);
v_checkedModules_3447_ = lean_ctor_get(v_a_3420_, 1);
lean_inc(v_checkedModules_3447_);
lean_dec(v_a_3420_);
v_records_3448_ = lean_ctor_get(v_outcome_3421_, 0);
lean_inc_ref(v_records_3448_);
v_unlocated_3449_ = lean_ctor_get_uint8(v_outcome_3421_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_3421_, 1);
v___x_3450_ = l_Array_append___redArg(v___y_3416_, v_records_3448_);
lean_dec_ref(v_records_3448_);
if (v_unlocated_3449_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(v___y_3415_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_checkedModules_3447_);
lean_ctor_set(v___x_3410_, 0, v___x_3451_);
v___x_3453_ = v___x_3410_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_checkedModules_3447_);
v___x_3453_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3453_);
lean_ctor_set(v___x_3405_, 0, v___x_3450_);
v___x_3455_ = v___x_3405_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = lean_box(v_anyFailed_3418_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3455_);
lean_ctor_set(v___x_3401_, 0, v___x_3456_);
v___x_3458_ = v___x_3401_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3455_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
v_a_3351_ = v___x_3458_;
goto v___jp_3350_;
}
}
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_box(v_anyUnlocated_3366_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v_checkedModules_3447_);
lean_ctor_set(v___x_3410_, 0, v___x_3462_);
v___x_3464_ = v___x_3410_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_checkedModules_3447_);
v___x_3464_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3464_);
lean_ctor_set(v___x_3405_, 0, v___x_3450_);
v___x_3466_ = v___x_3405_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_box(v_anyFailed_3418_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3466_);
lean_ctor_set(v___x_3401_, 0, v___x_3467_);
v___x_3469_ = v___x_3401_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3466_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_a_3351_ = v___x_3469_;
goto v___jp_3350_;
}
}
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v___y_3416_);
lean_del_object(v___x_3410_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v___x_3344_);
v_a_3473_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3419_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3419_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
v___jp_3481_:
{
if (v___y_3487_ == 0)
{
if (v___y_3485_ == 0)
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_unbox(v_fst_3399_);
lean_dec(v_fst_3399_);
v___y_3413_ = v___y_3482_;
v___y_3414_ = v___y_3483_;
v___y_3415_ = v_anyUnlocated_3488_;
v___y_3416_ = v___y_3484_;
v___y_3417_ = v___y_3486_;
v_anyFailed_3418_ = v___x_3489_;
goto v___jp_3412_;
}
else
{
lean_dec(v_fst_3399_);
v___y_3413_ = v___y_3482_;
v___y_3414_ = v___y_3483_;
v___y_3415_ = v_anyUnlocated_3488_;
v___y_3416_ = v___y_3484_;
v___y_3417_ = v___y_3486_;
v_anyFailed_3418_ = v_anyUnlocated_3366_;
goto v___jp_3412_;
}
}
else
{
lean_dec(v_fst_3399_);
v___y_3413_ = v___y_3482_;
v___y_3414_ = v___y_3483_;
v___y_3415_ = v_anyUnlocated_3488_;
v___y_3416_ = v___y_3484_;
v___y_3417_ = v___y_3486_;
v_anyFailed_3418_ = v_anyUnlocated_3366_;
goto v___jp_3412_;
}
}
v___jp_3490_:
{
lean_object* v___x_3499_; lean_object* v_snd_3500_; lean_object* v_fst_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3499_ = lean_st_ref_get(v___y_3497_);
lean_dec(v___y_3497_);
lean_dec(v___x_3499_);
v_snd_3500_ = lean_ctor_get(v_a_3498_, 1);
lean_inc(v_snd_3500_);
v_fst_3501_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_fst_3501_);
lean_dec_ref(v_a_3498_);
v_fst_3502_ = lean_ctor_get(v_snd_3500_, 0);
lean_inc(v_fst_3502_);
v_snd_3503_ = lean_ctor_get(v_snd_3500_, 1);
lean_inc(v_snd_3503_);
lean_dec(v_snd_3500_);
v___x_3504_ = l_Array_append___redArg(v___y_3494_, v_fst_3502_);
lean_dec(v_fst_3502_);
v___x_3505_ = lean_unbox(v_snd_3503_);
lean_dec(v_snd_3503_);
if (v___x_3505_ == 0)
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_unbox(v_fst_3501_);
lean_dec(v_fst_3501_);
v___y_3482_ = v___y_3491_;
v___y_3483_ = v___y_3493_;
v___y_3484_ = v___x_3504_;
v___y_3485_ = v___x_3506_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___y_3496_;
v_anyUnlocated_3488_ = v___y_3492_;
goto v___jp_3481_;
}
else
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_unbox(v_fst_3501_);
lean_dec(v_fst_3501_);
v___y_3482_ = v___y_3491_;
v___y_3483_ = v___y_3493_;
v___y_3484_ = v___x_3504_;
v___y_3485_ = v___x_3507_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___y_3496_;
v_anyUnlocated_3488_ = v_anyUnlocated_3366_;
goto v___jp_3481_;
}
}
v___jp_3508_:
{
if (lean_obj_tag(v___y_3516_) == 0)
{
lean_object* v_a_3517_; 
v_a_3517_ = lean_ctor_get(v___y_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___y_3516_, 1);
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
v___y_3493_ = v___y_3511_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3513_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___y_3514_;
v_a_3498_ = v_a_3517_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3518_; 
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3509_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3518_ = lean_ctor_get(v___y_3516_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___y_3516_, 1);
v_a_3368_ = v_a_3518_;
goto v___jp_3367_;
}
}
v___jp_3520_:
{
if (v___y_3531_ == 0)
{
lean_del_object(v___x_3394_);
if (v___y_3534_ == 0)
{
lean_dec_ref(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3523_);
if (v___y_3529_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__4));
lean_inc(v_a_3386_);
v___x_3536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3386_, v_anyUnlocated_3366_);
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5));
v___x_3539_ = lean_string_append(v___x_3537_, v___x_3538_);
v___x_3540_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3539_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3519_, v_anyFailed_3365_, v___y_3534_, v_a_3541_, v___y_3524_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3524_);
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3522_;
v___y_3511_ = v___y_3533_;
v___y_3512_ = v___y_3525_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3529_;
v___y_3516_ = v___x_3542_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3521_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3543_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3545_ = v___x_3540_;
v_isShared_3546_ = v_isSharedCheck_3552_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3540_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3552_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = lean_io_error_to_string(v_a_3543_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set_tag(v___x_3545_, 3);
lean_ctor_set(v___x_3545_, 0, v___x_3547_);
v___x_3549_ = v___x_3545_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_MessageData_ofFormat(v___x_3549_);
v_msg_3360_ = v___x_3550_;
goto v___jp_3359_;
}
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_box(0);
v___x_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3519_, v_anyFailed_3365_, v___y_3534_, v___x_3553_, v___y_3524_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3524_);
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3522_;
v___y_3511_ = v___y_3533_;
v___y_3512_ = v___y_3525_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3529_;
v___y_3516_ = v___x_3554_;
goto v___jp_3508_;
}
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; 
v___x_3555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__6));
lean_inc(v_a_3386_);
v___x_3556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3386_, v___y_3534_);
v___x_3557_ = lean_string_append(v___x_3555_, v___x_3556_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = 1;
v___x_3559_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_3527_, v___y_3526_, v_anyUnlocated_3366_, v___x_3557_, v___x_3558_, v___y_3523_, v_anyUnlocated_3366_, v___y_3524_, v___y_3532_);
lean_dec_ref(v___y_3526_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = l_Lean_MessageData_toString(v_a_3560_);
v___x_3562_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__1(v___x_3519_, v_anyFailed_3365_, v___y_3534_, v_a_3563_, v___y_3524_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3524_);
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3522_;
v___y_3511_ = v___y_3533_;
v___y_3512_ = v___y_3525_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3530_;
v___y_3515_ = v___y_3529_;
v___y_3516_ = v___x_3564_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3521_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3565_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3567_ = v___x_3562_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3562_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = lean_io_error_to_string(v_a_3565_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set_tag(v___x_3567_, 3);
lean_ctor_set(v___x_3567_, 0, v___x_3569_);
v___x_3571_ = v___x_3567_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_MessageData_ofFormat(v___x_3571_);
v_msg_3360_ = v___x_3572_;
goto v___jp_3359_;
}
}
}
}
else
{
lean_object* v_a_3575_; 
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3521_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3575_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3559_, 1);
v_a_3368_ = v_a_3575_;
goto v___jp_3367_;
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3523_);
v___x_3576_ = lean_st_ref_get(v___y_3532_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc_ref(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3578_ = l_Lean_Environment_mainModule(v_env_3577_);
lean_dec_ref(v_env_3577_);
v___x_3579_ = lean_box(v_anyFailed_3365_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 1, v___x_3579_);
lean_ctor_set(v___x_3394_, 0, v___x_3519_);
v___x_3581_ = v___x_3394_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
size_t v_sz_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v_sz_3582_ = lean_array_size(v___y_3527_);
v___x_3583_ = ((size_t)0ULL);
lean_inc(v___x_3344_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___y_3531_, v___x_3344_, v___x_3578_, v___y_3527_, v_sz_3582_, v___x_3583_, v___x_3581_, v___y_3524_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3527_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v_fst_3586_; lean_object* v_snd_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3596_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3584_, 1);
v_fst_3586_ = lean_ctor_get(v_a_3585_, 0);
v_snd_3587_ = lean_ctor_get(v_a_3585_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3585_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3589_ = v_a_3585_;
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_snd_3587_);
lean_inc(v_fst_3586_);
lean_dec(v_a_3585_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_fst_3586_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_snd_3587_);
v___x_3592_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_box(v___y_3534_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v___x_3592_);
v___y_3491_ = v___y_3521_;
v___y_3492_ = v___y_3522_;
v___y_3493_ = v___y_3533_;
v___y_3494_ = v___y_3525_;
v___y_3495_ = v___y_3528_;
v___y_3496_ = v___y_3529_;
v___y_3497_ = v___y_3530_;
v_a_3498_ = v___x_3594_;
goto v___jp_3490_;
}
}
}
else
{
lean_object* v_a_3597_; 
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3521_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3597_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3584_, 1);
v_a_3368_ = v_a_3597_;
goto v___jp_3367_;
}
}
}
}
v___jp_3599_:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_3611_, v___y_3605_, v___y_3602_);
lean_dec(v___y_3611_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = lean_array_get_size(v_a_3613_);
v___x_3615_ = lean_nat_dec_eq(v___x_3614_, v___x_3364_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_Linter_EnvLinter_lintCore(v___y_3607_, v_a_3613_, v___y_3605_, v___y_3602_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = lean_array_get_size(v_a_3617_);
v___x_3619_ = lean_nat_dec_lt(v___x_3364_, v___x_3618_);
if (v___x_3619_ == 0)
{
v___y_3521_ = v___y_3601_;
v___y_3522_ = v___y_3603_;
v___y_3523_ = v___x_3614_;
v___y_3524_ = v___y_3605_;
v___y_3525_ = v___y_3606_;
v___y_3526_ = v___y_3607_;
v___y_3527_ = v_a_3617_;
v___y_3528_ = v___y_3608_;
v___y_3529_ = v___y_3610_;
v___y_3530_ = v___y_3609_;
v___y_3531_ = v___y_3600_;
v___y_3532_ = v___y_3602_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___x_3615_;
goto v___jp_3520_;
}
else
{
if (v___x_3619_ == 0)
{
v___y_3521_ = v___y_3601_;
v___y_3522_ = v___y_3603_;
v___y_3523_ = v___x_3614_;
v___y_3524_ = v___y_3605_;
v___y_3525_ = v___y_3606_;
v___y_3526_ = v___y_3607_;
v___y_3527_ = v_a_3617_;
v___y_3528_ = v___y_3608_;
v___y_3529_ = v___y_3610_;
v___y_3530_ = v___y_3609_;
v___y_3531_ = v___y_3600_;
v___y_3532_ = v___y_3602_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___x_3615_;
goto v___jp_3520_;
}
else
{
size_t v___x_3620_; size_t v___x_3621_; uint8_t v___x_3622_; 
v___x_3620_ = ((size_t)0ULL);
v___x_3621_ = lean_usize_of_nat(v___x_3618_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__7(v___x_3614_, v_a_3617_, v___x_3620_, v___x_3621_);
v___y_3521_ = v___y_3601_;
v___y_3522_ = v___y_3603_;
v___y_3523_ = v___x_3614_;
v___y_3524_ = v___y_3605_;
v___y_3525_ = v___y_3606_;
v___y_3526_ = v___y_3607_;
v___y_3527_ = v_a_3617_;
v___y_3528_ = v___y_3608_;
v___y_3529_ = v___y_3610_;
v___y_3530_ = v___y_3609_;
v___y_3531_ = v___y_3600_;
v___y_3532_ = v___y_3602_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___x_3622_;
goto v___jp_3520_;
}
}
}
else
{
lean_object* v_a_3623_; 
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3602_);
lean_dec(v___y_3601_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3623_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3616_, 1);
v_a_3368_ = v_a_3623_;
goto v___jp_3367_;
}
}
else
{
lean_dec(v_a_3613_);
lean_dec_ref(v___y_3607_);
lean_del_object(v___x_3394_);
if (v___y_3600_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__7));
lean_inc(v_a_3386_);
v___x_3625_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3386_, v___x_3615_);
v___x_3626_ = lean_string_append(v___x_3624_, v___x_3625_);
lean_dec_ref(v___x_3625_);
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___closed__5));
v___x_3628_ = lean_string_append(v___x_3626_, v___x_3627_);
v___x_3629_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3631_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_3519_, v_anyFailed_3365_, v_a_3630_, v___y_3605_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3605_);
v___y_3509_ = v___y_3601_;
v___y_3510_ = v___y_3603_;
v___y_3511_ = v___y_3604_;
v___y_3512_ = v___y_3606_;
v___y_3513_ = v___y_3608_;
v___y_3514_ = v___y_3609_;
v___y_3515_ = v___y_3610_;
v___y_3516_ = v___x_3631_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3602_);
lean_dec(v___y_3601_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_dec(v___x_3344_);
v_a_3632_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3634_ = v___x_3629_;
v_isShared_3635_ = v_isSharedCheck_3641_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3629_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3641_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_io_error_to_string(v_a_3632_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 3);
lean_ctor_set(v___x_3634_, 0, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_MessageData_ofFormat(v___x_3638_);
v_msg_3360_ = v___x_3639_;
goto v___jp_3359_;
}
}
}
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = lean_box(0);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___lam__0(v___x_3519_, v_anyFailed_3365_, v___x_3642_, v___y_3605_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3605_);
v___y_3509_ = v___y_3601_;
v___y_3510_ = v___y_3603_;
v___y_3511_ = v___y_3604_;
v___y_3512_ = v___y_3606_;
v___y_3513_ = v___y_3608_;
v___y_3514_ = v___y_3609_;
v___y_3515_ = v___y_3610_;
v___y_3516_ = v___x_3643_;
goto v___jp_3508_;
}
}
}
else
{
lean_object* v_a_3644_; 
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3602_);
lean_dec(v___y_3601_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3644_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3612_, 1);
v_a_3368_ = v_a_3644_;
goto v___jp_3367_;
}
}
v___jp_3645_:
{
lean_object* v_fileName_3659_; lean_object* v_fileMap_3660_; lean_object* v_currRecDepth_3661_; lean_object* v_ref_3662_; lean_object* v_currNamespace_3663_; lean_object* v_openDecls_3664_; lean_object* v_initHeartbeats_3665_; lean_object* v_maxHeartbeats_3666_; lean_object* v_quotContext_3667_; lean_object* v_currMacroScope_3668_; lean_object* v_cancelTk_x3f_3669_; uint8_t v_suppressElabErrors_3670_; lean_object* v_inheritedTraceOptions_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3691_; 
v_fileName_3659_ = lean_ctor_get(v___y_3657_, 0);
v_fileMap_3660_ = lean_ctor_get(v___y_3657_, 1);
v_currRecDepth_3661_ = lean_ctor_get(v___y_3657_, 3);
v_ref_3662_ = lean_ctor_get(v___y_3657_, 5);
v_currNamespace_3663_ = lean_ctor_get(v___y_3657_, 6);
v_openDecls_3664_ = lean_ctor_get(v___y_3657_, 7);
v_initHeartbeats_3665_ = lean_ctor_get(v___y_3657_, 8);
v_maxHeartbeats_3666_ = lean_ctor_get(v___y_3657_, 9);
v_quotContext_3667_ = lean_ctor_get(v___y_3657_, 10);
v_currMacroScope_3668_ = lean_ctor_get(v___y_3657_, 11);
v_cancelTk_x3f_3669_ = lean_ctor_get(v___y_3657_, 12);
v_suppressElabErrors_3670_ = lean_ctor_get_uint8(v___y_3657_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3671_ = lean_ctor_get(v___y_3657_, 13);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___y_3657_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3692_ = lean_ctor_get(v___y_3657_, 4);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v___y_3657_, 2);
lean_dec(v_unused_3693_);
v___x_3673_ = v___y_3657_;
v_isShared_3674_ = v_isSharedCheck_3691_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_inheritedTraceOptions_3671_);
lean_inc(v_cancelTk_x3f_3669_);
lean_inc(v_currMacroScope_3668_);
lean_inc(v_quotContext_3667_);
lean_inc(v_maxHeartbeats_3666_);
lean_inc(v_initHeartbeats_3665_);
lean_inc(v_openDecls_3664_);
lean_inc(v_currNamespace_3663_);
lean_inc(v_ref_3662_);
lean_inc(v_currRecDepth_3661_);
lean_inc(v_fileMap_3660_);
lean_inc(v_fileName_3659_);
lean_dec(v___y_3657_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3691_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_3647_, v___y_3658_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3689_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3680_ = l_Lean_maxRecDepth;
v___x_3681_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_3652_, v___x_3680_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 4, v___x_3681_);
lean_ctor_set(v___x_3673_, 2, v___y_3652_);
v___x_3683_ = v___x_3673_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_fileName_3659_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_fileMap_3660_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v___y_3652_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_currRecDepth_3661_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v_ref_3662_);
lean_ctor_set(v_reuseFailAlloc_3688_, 6, v_currNamespace_3663_);
lean_ctor_set(v_reuseFailAlloc_3688_, 7, v_openDecls_3664_);
lean_ctor_set(v_reuseFailAlloc_3688_, 8, v_initHeartbeats_3665_);
lean_ctor_set(v_reuseFailAlloc_3688_, 9, v_maxHeartbeats_3666_);
lean_ctor_set(v_reuseFailAlloc_3688_, 10, v_quotContext_3667_);
lean_ctor_set(v_reuseFailAlloc_3688_, 11, v_currMacroScope_3668_);
lean_ctor_set(v_reuseFailAlloc_3688_, 12, v_cancelTk_x3f_3669_);
lean_ctor_set(v_reuseFailAlloc_3688_, 13, v_inheritedTraceOptions_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, sizeof(void*)*14 + 1, v_suppressElabErrors_3670_);
v___x_3683_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_ctor_set_uint8(v___x_3683_, sizeof(void*)*14, v___y_3649_);
if (v___y_3653_ == 0)
{
lean_object* v___x_3684_; 
lean_del_object(v___x_3678_);
v___x_3684_ = lean_box(0);
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3658_;
v___y_3603_ = v___y_3648_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___x_3683_;
v___y_3606_ = v___y_3651_;
v___y_3607_ = v_a_3676_;
v___y_3608_ = v___y_3654_;
v___y_3609_ = v___y_3656_;
v___y_3610_ = v___y_3655_;
v___y_3611_ = v___x_3684_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3686_; 
lean_inc_ref(v___y_3654_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v___y_3654_);
v___x_3686_ = v___x_3678_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___y_3654_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3658_;
v___y_3603_ = v___y_3648_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___x_3683_;
v___y_3606_ = v___y_3651_;
v___y_3607_ = v_a_3676_;
v___y_3608_ = v___y_3654_;
v___y_3609_ = v___y_3656_;
v___y_3610_ = v___y_3655_;
v___y_3611_ = v___x_3686_;
goto v___jp_3599_;
}
}
}
}
}
else
{
lean_object* v_a_3690_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_inheritedTraceOptions_3671_);
lean_dec(v_cancelTk_x3f_3669_);
lean_dec(v_currMacroScope_3668_);
lean_dec(v_quotContext_3667_);
lean_dec(v_maxHeartbeats_3666_);
lean_dec(v_initHeartbeats_3665_);
lean_dec(v_openDecls_3664_);
lean_dec(v_currNamespace_3663_);
lean_dec(v_ref_3662_);
lean_dec(v_currRecDepth_3661_);
lean_dec_ref(v_fileMap_3660_);
lean_dec_ref(v_fileName_3659_);
lean_dec(v___y_3658_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3647_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3690_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3675_, 1);
v_a_3368_ = v_a_3690_;
goto v___jp_3367_;
}
}
}
v___jp_3694_:
{
if (v___y_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v_env_3710_; lean_object* v_nextMacroScope_3711_; lean_object* v_ngen_3712_; lean_object* v_auxDeclNGen_3713_; lean_object* v_traceState_3714_; lean_object* v_messages_3715_; lean_object* v_infoState_3716_; lean_object* v_snapshotTasks_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3726_; 
v___x_3709_ = lean_st_ref_take(v___y_3702_);
v_env_3710_ = lean_ctor_get(v___x_3709_, 0);
v_nextMacroScope_3711_ = lean_ctor_get(v___x_3709_, 1);
v_ngen_3712_ = lean_ctor_get(v___x_3709_, 2);
v_auxDeclNGen_3713_ = lean_ctor_get(v___x_3709_, 3);
v_traceState_3714_ = lean_ctor_get(v___x_3709_, 4);
v_messages_3715_ = lean_ctor_get(v___x_3709_, 6);
v_infoState_3716_ = lean_ctor_get(v___x_3709_, 7);
v_snapshotTasks_3717_ = lean_ctor_get(v___x_3709_, 8);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v___x_3709_, 5);
lean_dec(v_unused_3727_);
v___x_3719_ = v___x_3709_;
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_snapshotTasks_3717_);
lean_inc(v_infoState_3716_);
lean_inc(v_messages_3715_);
lean_inc(v_traceState_3714_);
lean_inc(v_auxDeclNGen_3713_);
lean_inc(v_ngen_3712_);
lean_inc(v_nextMacroScope_3711_);
lean_inc(v_env_3710_);
lean_dec(v___x_3709_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = l_Lean_Kernel_enableDiag(v_env_3710_, v___y_3704_);
lean_inc_ref(v___y_3699_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 5, v___y_3699_);
lean_ctor_set(v___x_3719_, 0, v___x_3721_);
v___x_3723_ = v___x_3719_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_nextMacroScope_3711_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_ngen_3712_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_auxDeclNGen_3713_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_traceState_3714_);
lean_ctor_set(v_reuseFailAlloc_3725_, 5, v___y_3699_);
lean_ctor_set(v_reuseFailAlloc_3725_, 6, v_messages_3715_);
lean_ctor_set(v_reuseFailAlloc_3725_, 7, v_infoState_3716_);
lean_ctor_set(v_reuseFailAlloc_3725_, 8, v_snapshotTasks_3717_);
v___x_3723_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_st_ref_set(v___y_3702_, v___x_3723_);
lean_inc(v___y_3702_);
v___y_3646_ = v___y_3703_;
v___y_3647_ = v___y_3695_;
v___y_3648_ = v___y_3696_;
v___y_3649_ = v___y_3704_;
v___y_3650_ = v___y_3705_;
v___y_3651_ = v___y_3697_;
v___y_3652_ = v___y_3698_;
v___y_3653_ = v___y_3707_;
v___y_3654_ = v___y_3700_;
v___y_3655_ = v___y_3701_;
v___y_3656_ = v___y_3702_;
v___y_3657_ = v___y_3706_;
v___y_3658_ = v___y_3702_;
goto v___jp_3645_;
}
}
}
else
{
lean_inc(v___y_3702_);
v___y_3646_ = v___y_3703_;
v___y_3647_ = v___y_3695_;
v___y_3648_ = v___y_3696_;
v___y_3649_ = v___y_3704_;
v___y_3650_ = v___y_3705_;
v___y_3651_ = v___y_3697_;
v___y_3652_ = v___y_3698_;
v___y_3653_ = v___y_3707_;
v___y_3654_ = v___y_3700_;
v___y_3655_ = v___y_3701_;
v___y_3656_ = v___y_3702_;
v___y_3657_ = v___y_3706_;
v___y_3658_ = v___y_3702_;
goto v___jp_3645_;
}
}
v___jp_3728_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v_env_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; uint8_t v___x_3765_; 
v___x_3739_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_3740_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_3741_ = lean_io_get_num_heartbeats();
v___x_3742_ = l_Lean_firstFrontendMacroScope;
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_3745_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_3746_ = lean_box(0);
lean_inc_n(v___y_3733_, 2);
v___x_3747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3747_, 0, v___y_3733_);
lean_ctor_set(v___x_3747_, 1, v___x_3743_);
lean_ctor_set(v___x_3747_, 2, v___x_3746_);
v___x_3748_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_3749_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
lean_inc_ref(v___y_3731_);
v___x_3750_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3750_, 0, v___y_3731_);
lean_ctor_set(v___x_3750_, 1, v___x_3744_);
lean_ctor_set(v___x_3750_, 2, v___x_3745_);
lean_ctor_set(v___x_3750_, 3, v___x_3747_);
lean_ctor_set(v___x_3750_, 4, v___x_3748_);
lean_ctor_set(v___x_3750_, 5, v___x_3739_);
lean_ctor_set(v___x_3750_, 6, v___x_3740_);
lean_ctor_set(v___x_3750_, 7, v___x_3749_);
lean_ctor_set(v___x_3750_, 8, v___x_3519_);
v___x_3751_ = lean_st_mk_ref(v___x_3750_);
v___x_3752_ = l_Lean_inheritedTraceOptions;
v___x_3753_ = lean_st_ref_get(v___x_3752_);
v___x_3754_ = lean_st_ref_get(v___x_3751_);
v___x_3755_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_3756_ = l_Lean_instInhabitedFileMap_default;
v___x_3757_ = lean_unsigned_to_nat(1000u);
v___x_3758_ = lean_box(0);
v___x_3759_ = l_Lean_Core_getMaxHeartbeats(v___y_3732_);
v___x_3760_ = lean_box(0);
lean_inc_ref(v___y_3732_);
v___x_3761_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3761_, 0, v___x_3755_);
lean_ctor_set(v___x_3761_, 1, v___x_3756_);
lean_ctor_set(v___x_3761_, 2, v___y_3732_);
lean_ctor_set(v___x_3761_, 3, v___x_3364_);
lean_ctor_set(v___x_3761_, 4, v___x_3757_);
lean_ctor_set(v___x_3761_, 5, v___x_3758_);
lean_ctor_set(v___x_3761_, 6, v___y_3733_);
lean_ctor_set(v___x_3761_, 7, v___x_3746_);
lean_ctor_set(v___x_3761_, 8, v___x_3741_);
lean_ctor_set(v___x_3761_, 9, v___x_3759_);
lean_ctor_set(v___x_3761_, 10, v___y_3733_);
lean_ctor_set(v___x_3761_, 11, v___x_3742_);
lean_ctor_set(v___x_3761_, 12, v___x_3760_);
lean_ctor_set(v___x_3761_, 13, v___x_3753_);
lean_ctor_set_uint8(v___x_3761_, sizeof(void*)*14, v_anyFailed_3365_);
lean_ctor_set_uint8(v___x_3761_, sizeof(void*)*14 + 1, v_anyFailed_3365_);
v_env_3762_ = lean_ctor_get(v___x_3754_, 0);
lean_inc_ref(v_env_3762_);
lean_dec(v___x_3754_);
v___x_3763_ = l_Lean_diagnostics;
v___x_3764_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_3732_, v___x_3763_);
v___x_3765_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3762_);
lean_dec_ref(v_env_3762_);
if (v___x_3765_ == 0)
{
if (v___x_3764_ == 0)
{
v___y_3695_ = v___y_3730_;
v___y_3696_ = v_anyUnlocated_3738_;
v___y_3697_ = v_records_3737_;
v___y_3698_ = v___y_3732_;
v___y_3699_ = v___x_3739_;
v___y_3700_ = v___y_3735_;
v___y_3701_ = v___y_3736_;
v___y_3702_ = v___x_3751_;
v___y_3703_ = v___y_3729_;
v___y_3704_ = v___x_3764_;
v___y_3705_ = v___y_3731_;
v___y_3706_ = v___x_3761_;
v___y_3707_ = v___y_3734_;
v___y_3708_ = v___x_3383_;
goto v___jp_3694_;
}
else
{
v___y_3695_ = v___y_3730_;
v___y_3696_ = v_anyUnlocated_3738_;
v___y_3697_ = v_records_3737_;
v___y_3698_ = v___y_3732_;
v___y_3699_ = v___x_3739_;
v___y_3700_ = v___y_3735_;
v___y_3701_ = v___y_3736_;
v___y_3702_ = v___x_3751_;
v___y_3703_ = v___y_3729_;
v___y_3704_ = v___x_3764_;
v___y_3705_ = v___y_3731_;
v___y_3706_ = v___x_3761_;
v___y_3707_ = v___y_3734_;
v___y_3708_ = v___x_3765_;
goto v___jp_3694_;
}
}
else
{
v___y_3695_ = v___y_3730_;
v___y_3696_ = v_anyUnlocated_3738_;
v___y_3697_ = v_records_3737_;
v___y_3698_ = v___y_3732_;
v___y_3699_ = v___x_3739_;
v___y_3700_ = v___y_3735_;
v___y_3701_ = v___y_3736_;
v___y_3702_ = v___x_3751_;
v___y_3703_ = v___y_3729_;
v___y_3704_ = v___x_3764_;
v___y_3705_ = v___y_3731_;
v___y_3706_ = v___x_3761_;
v___y_3707_ = v___y_3734_;
v___y_3708_ = v___x_3764_;
goto v___jp_3694_;
}
}
v___jp_3766_:
{
if (v___y_3768_ == 0)
{
lean_object* v___x_3776_; size_t v_sz_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3776_ = lean_box(0);
v_sz_3777_ = lean_array_size(v___y_3769_);
v___x_3778_ = ((size_t)0ULL);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__10(v___x_3342_, v___y_3769_, v_sz_3777_, v___x_3778_, v___x_3776_);
lean_dec_ref(v___y_3769_);
if (lean_obj_tag(v___x_3779_) == 0)
{
uint8_t v___x_3780_; 
lean_dec_ref_known(v___x_3779_, 1);
v___x_3780_ = lean_unbox(v_fst_3407_);
lean_dec(v_fst_3407_);
v___y_3729_ = v___y_3768_;
v___y_3730_ = v___y_3767_;
v___y_3731_ = v___y_3770_;
v___y_3732_ = v___y_3771_;
v___y_3733_ = v___y_3772_;
v___y_3734_ = v___y_3773_;
v___y_3735_ = v___y_3774_;
v___y_3736_ = v___y_3775_;
v_records_3737_ = v_fst_3403_;
v_anyUnlocated_3738_ = v___x_3780_;
goto v___jp_3728_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3767_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_dec(v_fst_3407_);
lean_del_object(v___x_3405_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3781_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3779_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v___x_3789_; size_t v_sz_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v_fst_3403_);
lean_ctor_set(v___x_3789_, 1, v_fst_3407_);
v_sz_3790_ = lean_array_size(v___y_3769_);
v___x_3791_ = ((size_t)0ULL);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___y_3768_, v___y_3769_, v_sz_3790_, v___x_3791_, v___x_3789_);
lean_dec_ref(v___y_3769_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v_fst_3794_; lean_object* v_snd_3795_; uint8_t v___x_3796_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v_fst_3794_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_fst_3794_);
v_snd_3795_ = lean_ctor_get(v_a_3793_, 1);
lean_inc(v_snd_3795_);
lean_dec(v_a_3793_);
v___x_3796_ = lean_unbox(v_snd_3795_);
lean_dec(v_snd_3795_);
v___y_3729_ = v___y_3768_;
v___y_3730_ = v___y_3767_;
v___y_3731_ = v___y_3770_;
v___y_3732_ = v___y_3771_;
v___y_3733_ = v___y_3772_;
v___y_3734_ = v___y_3773_;
v___y_3735_ = v___y_3774_;
v___y_3736_ = v___y_3775_;
v_records_3737_ = v_fst_3794_;
v_anyUnlocated_3738_ = v___x_3796_;
goto v___jp_3728_;
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3767_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_del_object(v___x_3405_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3797_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3792_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3792_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
v___jp_3805_:
{
lean_object* v___x_3814_; uint8_t v___x_3815_; 
v___x_3814_ = lean_array_get_size(v___y_3813_);
v___x_3815_ = lean_nat_dec_eq(v___x_3814_, v___x_3364_);
if (v___x_3815_ == 0)
{
v___y_3767_ = v___y_3807_;
v___y_3768_ = v___y_3806_;
v___y_3769_ = v___y_3813_;
v___y_3770_ = v___y_3808_;
v___y_3771_ = v___y_3809_;
v___y_3772_ = v___y_3810_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v___y_3812_;
v___y_3775_ = v_anyUnlocated_3366_;
goto v___jp_3766_;
}
else
{
v___y_3767_ = v___y_3807_;
v___y_3768_ = v___y_3806_;
v___y_3769_ = v___y_3813_;
v___y_3770_ = v___y_3808_;
v___y_3771_ = v___y_3809_;
v___y_3772_ = v___y_3810_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v___y_3812_;
v___y_3775_ = v_anyFailed_3365_;
goto v___jp_3766_;
}
}
v___jp_3816_:
{
lean_object* v___x_3822_; lean_object* v_toEnvExtension_3823_; lean_object* v_asyncMode_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v_merged_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3839_; 
v___x_3822_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_3823_ = lean_ctor_get(v___x_3822_, 0);
v_asyncMode_3824_ = lean_ctor_get(v_toEnvExtension_3823_, 2);
v___x_3825_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_3826_ = lean_box(0);
lean_inc_ref(v___y_3818_);
v___x_3827_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3825_, v___x_3822_, v___y_3818_, v_asyncMode_3824_, v___x_3826_);
v_merged_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3827_, 1);
lean_dec(v_unused_3840_);
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3839_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_merged_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3839_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v_merged_3828_);
lean_ctor_set(v___x_3830_, 0, v___y_3821_);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___y_3821_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_merged_3828_);
v___x_3833_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = l_Lean_Name_getRoot(v_a_3386_);
v___x_3835_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v___y_3818_, v___x_3834_);
if (v___y_3820_ == 0)
{
v___y_3806_ = v___y_3817_;
v___y_3807_ = v___x_3834_;
v___y_3808_ = v___y_3818_;
v___y_3809_ = v___y_3819_;
v___y_3810_ = v___x_3826_;
v___y_3811_ = v___y_3820_;
v___y_3812_ = v___x_3833_;
v___y_3813_ = v___x_3835_;
goto v___jp_3805_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = lean_array_get_size(v___x_3835_);
v___x_3837_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__12(v___x_3833_, v___x_3835_, v___x_3364_, v___x_3836_);
lean_dec_ref(v___x_3835_);
v___y_3806_ = v___y_3817_;
v___y_3807_ = v___x_3834_;
v___y_3808_ = v___y_3818_;
v___y_3809_ = v___y_3819_;
v___y_3810_ = v___x_3826_;
v___y_3811_ = v___y_3820_;
v___y_3812_ = v___x_3833_;
v___y_3813_ = v___x_3837_;
goto v___jp_3805_;
}
}
}
}
v___jp_3841_:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_compacted_region_free(v_snd_3392_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; uint32_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_dec_ref_known(v___x_3843_, 1);
lean_inc(v_a_3386_);
v___x_3844_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3844_, 0, v_a_3386_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*1, v_anyFailed_3365_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*1 + 1, v_anyUnlocated_3366_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*1 + 2, v_anyFailed_3365_);
v___x_3845_ = lean_unsigned_to_nat(2u);
v___x_3846_ = lean_mk_empty_array_with_capacity(v___x_3845_);
v___x_3847_ = lean_array_push(v___x_3846_, v___x_3844_);
v___x_3848_ = lean_array_push(v___x_3847_, v_envLinterModule_3382_);
v___x_3849_ = l_Lean_Options_empty;
v___x_3850_ = 1024;
v___x_3851_ = lean_box(1);
v___x_3852_ = l_Lean_importModules(v___x_3848_, v___x_3849_, v___x_3850_, v___x_3519_, v_anyFailed_3365_, v_anyUnlocated_3366_, v___y_3842_, v___x_3851_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v_linterOverrides_3854_; uint8_t v_lintOnly_3855_; uint8_t v_recordExceptions_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v_linterOverrides_3854_ = lean_ctor_get(v_args_3343_, 0);
v_lintOnly_3855_ = lean_ctor_get_uint8(v_args_3343_, sizeof(void*)*3);
v_recordExceptions_3856_ = lean_ctor_get_uint8(v_args_3343_, sizeof(void*)*3 + 1);
v___x_3857_ = lean_array_get_size(v_linterOverrides_3854_);
v___x_3858_ = lean_nat_dec_lt(v___x_3364_, v___x_3857_);
if (v___x_3858_ == 0)
{
v___y_3817_ = v_recordExceptions_3856_;
v___y_3818_ = v_a_3853_;
v___y_3819_ = v___x_3849_;
v___y_3820_ = v_lintOnly_3855_;
v___y_3821_ = v___x_3849_;
goto v___jp_3816_;
}
else
{
uint8_t v___x_3859_; 
v___x_3859_ = lean_nat_dec_le(v___x_3857_, v___x_3857_);
if (v___x_3859_ == 0)
{
if (v___x_3858_ == 0)
{
v___y_3817_ = v_recordExceptions_3856_;
v___y_3818_ = v_a_3853_;
v___y_3819_ = v___x_3849_;
v___y_3820_ = v_lintOnly_3855_;
v___y_3821_ = v___x_3849_;
goto v___jp_3816_;
}
else
{
size_t v___x_3860_; size_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = ((size_t)0ULL);
v___x_3861_ = lean_usize_of_nat(v___x_3857_);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_linterOverrides_3854_, v___x_3860_, v___x_3861_, v___x_3849_);
v___y_3817_ = v_recordExceptions_3856_;
v___y_3818_ = v_a_3853_;
v___y_3819_ = v___x_3849_;
v___y_3820_ = v_lintOnly_3855_;
v___y_3821_ = v___x_3862_;
goto v___jp_3816_;
}
}
else
{
size_t v___x_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = lean_usize_of_nat(v___x_3857_);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__13(v_linterOverrides_3854_, v___x_3863_, v___x_3864_, v___x_3849_);
v___y_3817_ = v_recordExceptions_3856_;
v___y_3818_ = v_a_3853_;
v___y_3819_ = v___x_3849_;
v___y_3820_ = v_lintOnly_3855_;
v___y_3821_ = v___x_3865_;
goto v___jp_3816_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_dec(v_fst_3407_);
lean_del_object(v___x_3405_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec(v___x_3344_);
v_a_3866_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3852_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3852_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_del_object(v___x_3410_);
lean_dec(v_snd_3408_);
lean_dec(v_fst_3407_);
lean_del_object(v___x_3405_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_dec(v_fst_3399_);
lean_del_object(v___x_3394_);
lean_dec_ref_known(v_envLinterModule_3382_, 1);
lean_dec(v___x_3344_);
v_a_3874_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3843_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3843_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
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
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec_ref_known(v_envLinterModule_3382_, 1);
lean_dec_ref(v_b_3348_);
lean_dec(v___x_3344_);
v_a_3890_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3389_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3389_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec_ref_known(v_envLinterModule_3382_, 1);
lean_dec_ref(v_b_3348_);
lean_dec(v___x_3344_);
v_a_3898_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3387_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3387_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
v___jp_3350_:
{
size_t v___x_3352_; size_t v___x_3353_; 
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_add(v_i_3347_, v___x_3352_);
v_i_3347_ = v___x_3353_;
v_b_3348_ = v_a_3351_;
goto _start;
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = lean_mk_io_user_error(v_a_3356_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
v___jp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = l_Lean_MessageData_toString(v_msg_3360_);
v___x_3362_ = lean_mk_io_user_error(v___x_3361_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
v___jp_3367_:
{
if (lean_obj_tag(v_a_3368_) == 0)
{
lean_object* v_msg_3369_; 
v_msg_3369_ = lean_ctor_get(v_a_3368_, 1);
lean_inc_ref(v_msg_3369_);
lean_dec_ref_known(v_a_3368_, 2);
v_msg_3360_ = v_msg_3369_;
goto v___jp_3359_;
}
else
{
lean_object* v_id_3370_; lean_object* v___x_3371_; 
v_id_3370_ = lean_ctor_get(v_a_3368_, 0);
lean_inc(v_id_3370_);
lean_dec_ref_known(v_a_3368_, 2);
v___x_3371_ = l_Lean_InternalExceptionId_getName(v_id_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec(v_id_3370_);
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v___x_3373_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_3374_ = l_Lean_Name_toString(v_a_3372_, v_anyUnlocated_3366_);
v___x_3375_ = lean_string_append(v___x_3373_, v___x_3374_);
lean_dec_ref(v___x_3374_);
v_a_3356_ = v___x_3375_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref_known(v___x_3371_, 1);
v___x_3376_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_3377_ = l_Nat_reprFast(v_id_3370_);
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v_a_3356_ = v___x_3380_;
goto v___jp_3355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14___boxed(lean_object* v___x_3906_, lean_object* v_args_3907_, lean_object* v___x_3908_, lean_object* v_as_3909_, lean_object* v_sz_3910_, lean_object* v_i_3911_, lean_object* v_b_3912_, lean_object* v___y_3913_){
_start:
{
size_t v_sz_boxed_3914_; size_t v_i_boxed_3915_; lean_object* v_res_3916_; 
v_sz_boxed_3914_ = lean_unbox_usize(v_sz_3910_);
lean_dec(v_sz_3910_);
v_i_boxed_3915_ = lean_unbox_usize(v_i_3911_);
lean_dec(v_i_3911_);
v_res_3916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___x_3906_, v_args_3907_, v___x_3908_, v_as_3909_, v_sz_boxed_3914_, v_i_boxed_3915_, v_b_3912_);
lean_dec_ref(v_as_3909_);
lean_dec_ref(v_args_3907_);
lean_dec(v___x_3906_);
return v_res_3916_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = 0;
v___x_3919_ = lean_box_uint32(v___x_3918_);
return v___x_3919_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = 1;
v___x_3921_ = lean_box_uint32(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_3922_){
_start:
{
lean_object* v_mods_3924_; uint8_t v_recordExceptions_3925_; lean_object* v_srcSearchPath_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; uint8_t v_anyFailed_3929_; 
v_mods_3924_ = lean_ctor_get(v_args_3922_, 1);
lean_inc_ref(v_mods_3924_);
v_recordExceptions_3925_ = lean_ctor_get_uint8(v_args_3922_, sizeof(void*)*3 + 1);
v_srcSearchPath_3926_ = lean_ctor_get(v_args_3922_, 2);
v___x_3927_ = lean_array_get_size(v_mods_3924_);
v___x_3928_ = lean_unsigned_to_nat(0u);
v_anyFailed_3929_ = lean_nat_dec_eq(v___x_3927_, v___x_3928_);
if (v_anyFailed_3929_ == 0)
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; size_t v_sz_3940_; size_t v___x_3941_; lean_object* v___x_3942_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
lean_inc(v_srcSearchPath_3926_);
v___x_3932_ = l_List_appendTR___redArg(v_srcSearchPath_3926_, v_a_3931_);
v___x_3933_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_3934_ = l_Lean_NameSet_empty;
v___x_3935_ = lean_box(v_anyFailed_3929_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
lean_ctor_set(v___x_3936_, 1, v___x_3934_);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3933_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_box(v_anyFailed_3929_);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
lean_ctor_set(v___x_3939_, 1, v___x_3937_);
v_sz_3940_ = lean_array_size(v_mods_3924_);
v___x_3941_ = ((size_t)0ULL);
v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__14(v___x_3927_, v_args_3922_, v___x_3932_, v_mods_3924_, v_sz_3940_, v___x_3941_, v___x_3939_);
lean_dec_ref(v_mods_3924_);
lean_dec_ref(v_args_3922_);
if (lean_obj_tag(v___x_3942_) == 0)
{
if (v_recordExceptions_3925_ == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3957_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3957_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3957_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v_fst_3947_; uint8_t v___x_3948_; 
v_fst_3947_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_fst_3947_);
lean_dec(v_a_3943_);
v___x_3948_ = lean_unbox(v_fst_3947_);
lean_dec(v_fst_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3949_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3949_);
v___x_3951_ = v___x_3945_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3953_);
v___x_3955_ = v___x_3945_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v_snd_3959_; lean_object* v_fst_3960_; lean_object* v_snd_3961_; lean_object* v___x_3962_; 
v_a_3958_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3942_, 1);
v_snd_3959_ = lean_ctor_get(v_a_3958_, 1);
lean_inc(v_snd_3959_);
lean_dec(v_a_3958_);
v_fst_3960_ = lean_ctor_get(v_snd_3959_, 0);
lean_inc(v_fst_3960_);
v_snd_3961_ = lean_ctor_get(v_snd_3959_, 1);
lean_inc(v_snd_3961_);
lean_dec(v_snd_3959_);
v___x_3962_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_3960_);
lean_dec(v_fst_3960_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3976_; 
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; 
v_unused_3977_ = lean_ctor_get(v___x_3962_, 0);
lean_dec(v_unused_3977_);
v___x_3964_ = v___x_3962_;
v_isShared_3965_ = v_isSharedCheck_3976_;
goto v_resetjp_3963_;
}
else
{
lean_dec(v___x_3962_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3976_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v_fst_3966_; uint8_t v___x_3967_; 
v_fst_3966_ = lean_ctor_get(v_snd_3961_, 0);
lean_inc(v_fst_3966_);
lean_dec(v_snd_3961_);
v___x_3967_ = lean_unbox(v_fst_3966_);
lean_dec(v_fst_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3970_; 
v___x_3968_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3968_);
v___x_3970_ = v___x_3964_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3972_);
v___x_3974_ = v___x_3964_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_snd_3961_);
v_a_3978_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3962_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3962_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
v_a_3986_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3942_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3942_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_mods_3924_);
lean_dec_ref(v_args_3922_);
v_a_3994_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3930_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3930_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec_ref(v_mods_3924_);
lean_dec_ref(v_args_3922_);
v___x_4002_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_4003_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_4002_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4011_; 
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4011_ == 0)
{
lean_object* v_unused_4012_; 
v_unused_4012_ = lean_ctor_get(v___x_4003_, 0);
lean_dec(v_unused_4012_);
v___x_4005_ = v___x_4003_;
v_isShared_4006_ = v_isSharedCheck_4011_;
goto v_resetjp_4004_;
}
else
{
lean_dec(v___x_4003_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4011_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4007_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4007_);
v___x_4009_ = v___x_4005_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4003_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4003_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lake_BuiltinLint_run(v_args_4021_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_4024_, lean_object* v_constName_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___redArg(v_constName_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4030_, lean_object* v_constName_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3(v_00_u03b1_4030_, v_constName_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16(lean_object* v_00_u03b1_4036_, lean_object* v_ref_4037_, lean_object* v_constName_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___redArg(v_ref_4037_, v_constName_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16___boxed(lean_object* v_00_u03b1_4043_, lean_object* v_ref_4044_, lean_object* v_constName_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16(v_00_u03b1_4043_, v_ref_4044_, v_constName_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v_ref_4044_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18(lean_object* v_00_u03b1_4050_, lean_object* v_ref_4051_, lean_object* v_msg_4052_, lean_object* v_declHint_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___redArg(v_ref_4051_, v_msg_4052_, v_declHint_4053_, v___y_4054_, v___y_4055_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18___boxed(lean_object* v_00_u03b1_4058_, lean_object* v_ref_4059_, lean_object* v_msg_4060_, lean_object* v_declHint_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18(v_00_u03b1_4058_, v_ref_4059_, v_msg_4060_, v_declHint_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v_ref_4059_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_4066_, lean_object* v_declHint_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_4066_, v_declHint_4067_, v___y_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_4072_, lean_object* v_declHint_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__19_spec__20(v_msg_4072_, v_declHint_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_4078_, lean_object* v_ref_4079_, lean_object* v_msg_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___redArg(v_ref_4079_, v_msg_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_4085_, lean_object* v_ref_4086_, lean_object* v_msg_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20(v_00_u03b1_4085_, v_ref_4086_, v_msg_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v_ref_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_4092_, lean_object* v_msg_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_4093_, v___y_4094_, v___y_4095_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_4098_, lean_object* v_msg_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lake_BuiltinLint_run_spec__2_spec__2_spec__3_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_4098_, v_msg_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4103_;
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
