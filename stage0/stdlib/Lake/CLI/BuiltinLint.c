// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter public import Lean.Linter.PersistentLintLog import Lean.CoreM import Lean.DocString.Extension import Lean.Elab.DocString.Builtin.Postponed import Lake.Config.Workspace import Lean.Linter.CodeQuality
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_get_stdout();
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_linter_doc_deferred;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Doc_DeferredCheck_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuiltinLint_instBEqMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_instBEqMode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuiltinLint_instBEqMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuiltinLint_instBEqMode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuiltinLint_instBEqMode___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_instBEqMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuiltinLint_instBEqMode = (const lean_object*)&l_Lake_BuiltinLint_instBEqMode___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "set_option "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " false in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__4_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "warning: could not read `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`; skipping its "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exception(s)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "error: in module `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "`, in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": error: in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "warning: could not determine the position of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "`; cannot record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "warning: could not locate source file for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` to record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "warning: could not determine the command position of a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` text-linter warning in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`; skipping its exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0_value;
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "warning: no declaration range for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "-- Environment linting passed for "};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2_value;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "-- No environment linters were run for "};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_BuiltinLint_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_run___closed__0;
static lean_once_cell_t l_Lake_BuiltinLint_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_run___closed__1;
static const lean_string_object l_Lake_BuiltinLint_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__2 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_BuiltinLint_Mode_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_BuiltinLint_Mode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lake_BuiltinLint_Mode_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg(lean_object* v_report_23_){
_start:
{
lean_inc(v_report_23_);
return v_report_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg___boxed(lean_object* v_report_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_BuiltinLint_Mode_report_elim___redArg(v_report_24_);
lean_dec(v_report_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_report_29_){
_start:
{
lean_inc(v_report_29_);
return v_report_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_report_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lake_BuiltinLint_Mode_report_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_report_33_);
lean_dec(v_report_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(lean_object* v_recordExceptions_36_){
_start:
{
lean_inc(v_recordExceptions_36_);
return v_recordExceptions_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg___boxed(lean_object* v_recordExceptions_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(v_recordExceptions_37_);
lean_dec(v_recordExceptions_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_recordExceptions_42_){
_start:
{
lean_inc(v_recordExceptions_42_);
return v_recordExceptions_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_recordExceptions_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_recordExceptions_46_);
lean_dec(v_recordExceptions_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(lean_object* v_codeQuality_49_){
_start:
{
lean_inc(v_codeQuality_49_);
return v_codeQuality_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg___boxed(lean_object* v_codeQuality_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(v_codeQuality_50_);
lean_dec(v_codeQuality_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_codeQuality_55_){
_start:
{
lean_inc(v_codeQuality_55_);
return v_codeQuality_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_codeQuality_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lake_BuiltinLint_Mode_codeQuality_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_codeQuality_59_);
lean_dec(v_codeQuality_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuiltinLint_instBEqMode_beq(uint8_t v_x_62_, uint8_t v_y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_Lake_BuiltinLint_Mode_ctorIdx(v_x_62_);
v___x_65_ = l_Lake_BuiltinLint_Mode_ctorIdx(v_y_63_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_instBEqMode_beq___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_x_17__boxed_69_; uint8_t v_y_18__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_17__boxed_69_ = lean_unbox(v_x_67_);
v_y_18__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lake_BuiltinLint_instBEqMode_beq(v_x_17__boxed_69_, v_y_18__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t v_sz_78_, size_t v_i_79_, lean_object* v_bs_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_usize_dec_lt(v_i_79_, v_sz_78_);
if (v___x_81_ == 0)
{
return v_bs_80_;
}
else
{
lean_object* v_v_82_; lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_101_; 
v_v_82_ = lean_array_uget(v_bs_80_, v_i_79_);
v_fst_83_ = lean_ctor_get(v_v_82_, 0);
v_snd_84_ = lean_ctor_get(v_v_82_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_v_82_);
if (v_isSharedCheck_101_ == 0)
{
v___x_86_ = v_v_82_;
v_isShared_87_ = v_isSharedCheck_101_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_snd_84_);
lean_inc(v_fst_83_);
lean_dec(v_v_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_101_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v_bs_x27_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_95_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v_bs_x27_89_ = lean_array_uset(v_bs_80_, v_i_79_, v___x_88_);
v___x_90_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1));
v___x_91_ = l_Lean_Name_append(v___x_90_, v_fst_83_);
v___x_92_ = lean_alloc_ctor(1, 0, 1);
v___x_93_ = lean_unbox(v_snd_84_);
lean_dec(v_snd_84_);
lean_ctor_set_uint8(v___x_92_, 0, v___x_93_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___x_92_);
lean_ctor_set(v___x_86_, 0, v___x_91_);
v___x_95_ = v___x_86_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_92_);
v___x_95_ = v_reuseFailAlloc_100_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_79_, v___x_96_);
v___x_98_ = lean_array_uset(v_bs_x27_89_, v_i_79_, v___x_95_);
v_i_79_ = v___x_97_;
v_bs_80_ = v___x_98_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object* v_sz_102_, lean_object* v_i_103_, lean_object* v_bs_104_){
_start:
{
size_t v_sz_boxed_105_; size_t v_i_boxed_106_; lean_object* v_res_107_; 
v_sz_boxed_105_ = lean_unbox_usize(v_sz_102_);
lean_dec(v_sz_102_);
v_i_boxed_106_ = lean_unbox_usize(v_i_103_);
lean_dec(v_i_103_);
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_boxed_105_, v_i_boxed_106_, v_bs_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object* v_as_108_, size_t v_i_109_, size_t v_stop_110_, lean_object* v_b_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = lean_usize_dec_eq(v_i_109_, v_stop_110_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; 
v___x_113_ = lean_array_uget_borrowed(v_as_108_, v_i_109_);
v_fst_114_ = lean_ctor_get(v___x_113_, 0);
v_snd_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_snd_115_);
lean_inc(v_fst_114_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_114_, v_snd_115_, v_b_111_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_add(v_i_109_, v___x_117_);
v_i_109_ = v___x_118_;
v_b_111_ = v___x_116_;
goto _start;
}
else
{
return v_b_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object* v_as_120_, lean_object* v_i_121_, lean_object* v_stop_122_, lean_object* v_b_123_){
_start:
{
size_t v_i_boxed_124_; size_t v_stop_boxed_125_; lean_object* v_res_126_; 
v_i_boxed_124_ = lean_unbox_usize(v_i_121_);
lean_dec(v_i_121_);
v_stop_boxed_125_ = lean_unbox_usize(v_stop_122_);
lean_dec(v_stop_122_);
v_res_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_120_, v_i_boxed_124_, v_stop_boxed_125_, v_b_123_);
lean_dec_ref(v_as_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object* v_init_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v_k_129_; lean_object* v_v_130_; lean_object* v_l_131_; lean_object* v_r_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_129_ = lean_ctor_get(v_x_128_, 1);
v_v_130_ = lean_ctor_get(v_x_128_, 2);
v_l_131_ = lean_ctor_get(v_x_128_, 3);
v_r_132_ = lean_ctor_get(v_x_128_, 4);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_127_, v_l_131_);
lean_inc(v_v_130_);
lean_inc(v_k_129_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_k_129_);
lean_ctor_set(v___x_134_, 1, v_v_130_);
v___x_135_ = lean_array_push(v___x_133_, v___x_134_);
v_init_127_ = v___x_135_;
v_x_128_ = v_r_132_;
goto _start;
}
else
{
return v_init_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object* v_init_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_137_, v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_152_){
_start:
{
lean_object* v_linterOverrides_153_; uint8_t v_mode_154_; lean_object* v___y_156_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_linterOverrides_153_ = lean_ctor_get(v_args_152_, 0);
v_mode_154_ = lean_ctor_get_uint8(v_args_152_, sizeof(void*)*3 + 1);
v___x_168_ = lean_box(1);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_array_get_size(v_linterOverrides_153_);
v___x_171_ = lean_nat_dec_lt(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
v___y_156_ = v___x_168_;
goto v___jp_155_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_le(v___x_170_, v___x_170_);
if (v___x_172_ == 0)
{
if (v___x_171_ == 0)
{
v___y_156_ = v___x_168_;
goto v___jp_155_;
}
else
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_170_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_153_, v___x_173_, v___x_174_, v___x_168_);
v___y_156_ = v___x_175_;
goto v___jp_155_;
}
}
else
{
size_t v___x_176_; size_t v___x_177_; lean_object* v___x_178_; 
v___x_176_ = ((size_t)0ULL);
v___x_177_ = lean_usize_of_nat(v___x_170_);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_153_, v___x_176_, v___x_177_, v___x_168_);
v___y_156_ = v___x_178_;
goto v___jp_155_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; size_t v_sz_159_; size_t v___x_160_; lean_object* v_base_161_; uint8_t v___x_162_; uint8_t v___x_163_; 
v___x_157_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__0));
v___x_158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v___x_157_, v___y_156_);
lean_dec(v___y_156_);
v_sz_159_ = lean_array_size(v___x_158_);
v___x_160_ = ((size_t)0ULL);
v_base_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_159_, v___x_160_, v___x_158_);
v___x_162_ = 1;
v___x_163_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_154_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_LeanOptions_ofArray(v_base_161_);
lean_dec_ref(v_base_161_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__5));
v___x_166_ = lean_array_push(v_base_161_, v___x_165_);
v___x_167_ = l_Lean_LeanOptions_ofArray(v___x_166_);
lean_dec_ref(v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_179_);
lean_dec_ref(v_args_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_181_, lean_object* v_t_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_181_, v_t_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_184_, lean_object* v_t_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_184_, v_t_185_);
lean_dec(v_t_185_);
return v_res_186_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_box(0);
v___x_189_ = l_Lean_instInhabitedPosition_default;
v___x_190_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1, &l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once, _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1);
return v___x_192_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx(lean_object* v_x_194_){
_start:
{
switch(lean_obj_tag(v_x_194_))
{
case 0:
{
lean_object* v___x_195_; 
v___x_195_ = lean_unsigned_to_nat(0u);
return v___x_195_;
}
case 1:
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(1u);
return v___x_196_;
}
default: 
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(2u);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___boxed(lean_object* v_x_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx(v_x_198_);
lean_dec_ref(v_x_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object* v_t_200_, lean_object* v_k_201_){
_start:
{
switch(lean_obj_tag(v_t_200_))
{
case 0:
{
uint8_t v_failed_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_failed_202_ = lean_ctor_get_uint8(v_t_200_, 0);
lean_dec_ref_known(v_t_200_, 0);
v___x_203_ = lean_box(v_failed_202_);
v___x_204_ = lean_apply_1(v_k_201_, v___x_203_);
return v___x_204_;
}
case 1:
{
lean_object* v_records_205_; uint8_t v_unlocated_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_records_205_ = lean_ctor_get(v_t_200_, 0);
lean_inc_ref(v_records_205_);
v_unlocated_206_ = lean_ctor_get_uint8(v_t_200_, sizeof(void*)*1);
lean_dec_ref_known(v_t_200_, 1);
v___x_207_ = lean_box(v_unlocated_206_);
v___x_208_ = lean_apply_2(v_k_201_, v_records_205_, v___x_207_);
return v___x_208_;
}
default: 
{
lean_object* v_entries_209_; lean_object* v___x_210_; 
v_entries_209_ = lean_ctor_get(v_t_200_, 0);
lean_inc_ref(v_entries_209_);
lean_dec_ref_known(v_t_200_, 1);
v___x_210_ = lean_apply_1(v_k_201_, v_entries_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_213_, v_k_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(v_motive_217_, v_ctorIdx_218_, v_t_219_, v_h_220_, v_k_221_);
lean_dec(v_ctorIdx_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object* v_t_223_, lean_object* v_reported_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_223_, v_reported_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_reported_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_227_, v_reported_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object* v_t_231_, lean_object* v_recorded_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_231_, v_recorded_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object* v_motive_234_, lean_object* v_t_235_, lean_object* v_h_236_, lean_object* v_recorded_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_235_, v_recorded_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object* v_t_239_, lean_object* v_codeQualityChecks_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_239_, v_codeQualityChecks_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_codeQualityChecks_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_243_, v_codeQualityChecks_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(0u);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(1u);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx(v_x_250_);
lean_dec_ref(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_252_, lean_object* v_k_253_){
_start:
{
if (lean_obj_tag(v_t_252_) == 0)
{
uint8_t v_failed_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_failed_254_ = lean_ctor_get_uint8(v_t_252_, 0);
lean_dec_ref_known(v_t_252_, 0);
v___x_255_ = lean_box(v_failed_254_);
v___x_256_ = lean_apply_1(v_k_253_, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v_records_257_; uint8_t v_unlocated_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_records_257_ = lean_ctor_get(v_t_252_, 0);
lean_inc_ref(v_records_257_);
v_unlocated_258_ = lean_ctor_get_uint8(v_t_252_, sizeof(void*)*1);
lean_dec_ref_known(v_t_252_, 1);
v___x_259_ = lean_box(v_unlocated_258_);
v___x_260_ = lean_apply_2(v_k_253_, v_records_257_, v___x_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_263_, v_k_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_267_, lean_object* v_ctorIdx_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_267_, v_ctorIdx_268_, v_t_269_, v_h_270_, v_k_271_);
lean_dec(v_ctorIdx_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_273_, lean_object* v_reported_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_273_, v_reported_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_reported_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_277_, v_reported_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_281_, lean_object* v_recorded_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_281_, v_recorded_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_recorded_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_285_, v_recorded_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_289_, lean_object* v_as_290_, size_t v_i_291_, size_t v_stop_292_, lean_object* v_b_293_){
_start:
{
lean_object* v___y_295_; uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_eq(v_i_291_, v_stop_292_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; uint8_t v___y_302_; lean_object* v_fst_304_; lean_object* v_snd_305_; uint8_t v___x_306_; 
v___x_300_ = lean_array_uget_borrowed(v_as_290_, v_i_291_);
v_fst_304_ = lean_ctor_get(v___x_300_, 0);
v_snd_305_ = lean_ctor_get(v___x_300_, 1);
v___x_306_ = l_Lean_Name_isPrefixOf(v_pkgRoot_289_, v_fst_304_);
if (v___x_306_ == 0)
{
v___y_302_ = v___x_306_;
goto v___jp_301_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_array_get_size(v_snd_305_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
v___y_302_ = v___x_306_;
goto v___jp_301_;
}
else
{
v___y_295_ = v_b_293_;
goto v___jp_294_;
}
}
v___jp_301_:
{
if (v___y_302_ == 0)
{
v___y_295_ = v_b_293_;
goto v___jp_294_;
}
else
{
lean_object* v___x_303_; 
lean_inc(v___x_300_);
v___x_303_ = lean_array_push(v_b_293_, v___x_300_);
v___y_295_ = v___x_303_;
goto v___jp_294_;
}
}
}
else
{
return v_b_293_;
}
v___jp_294_:
{
size_t v___x_296_; size_t v___x_297_; 
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_291_, v___x_296_);
v_i_291_ = v___x_297_;
v_b_293_ = v___y_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_310_, lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_stop_313_, lean_object* v_b_314_){
_start:
{
size_t v_i_boxed_315_; size_t v_stop_boxed_316_; lean_object* v_res_317_; 
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_stop_boxed_316_ = lean_unbox_usize(v_stop_313_);
lean_dec(v_stop_313_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_310_, v_as_311_, v_i_boxed_315_, v_stop_boxed_316_, v_b_314_);
lean_dec_ref(v_as_311_);
lean_dec(v_pkgRoot_310_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_320_, lean_object* v_pkgRoot_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_324_ = l_Lean_Linter_getAllLints(v_env_320_);
v___x_325_ = lean_array_get_size(v___x_324_);
v___x_326_ = lean_nat_dec_lt(v___x_322_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec_ref(v___x_324_);
return v___x_323_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_le(v___x_325_, v___x_325_);
if (v___x_327_ == 0)
{
if (v___x_326_ == 0)
{
lean_dec_ref(v___x_324_);
return v___x_323_;
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_325_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_321_, v___x_324_, v___x_328_, v___x_329_, v___x_323_);
lean_dec_ref(v___x_324_);
return v___x_330_;
}
}
else
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((size_t)0ULL);
v___x_332_ = lean_usize_of_nat(v___x_325_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_321_, v___x_324_, v___x_331_, v___x_332_, v___x_323_);
lean_dec_ref(v___x_324_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_334_, lean_object* v_pkgRoot_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_334_, v_pkgRoot_335_);
lean_dec(v_pkgRoot_335_);
lean_dec_ref(v_env_334_);
return v_res_336_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_337_){
_start:
{
uint8_t v_isModule_339_; 
v_isModule_339_ = lean_ctor_get_uint8(v_modData_337_, sizeof(void*)*5);
return v_isModule_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_340_, lean_object* v_a_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_340_);
lean_dec_ref(v_modData_340_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_346_){
_start:
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 32;
v___x_348_ = lean_uint32_dec_eq(v_c_346_, v___x_347_);
if (v___x_348_ == 0)
{
uint32_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = 9;
v___x_350_ = lean_uint32_dec_eq(v_c_346_, v___x_349_);
return v___x_350_;
}
else
{
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_351_){
_start:
{
uint32_t v_c_boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_c_boxed_352_ = lean_unbox_uint32(v_c_351_);
lean_dec(v_c_351_);
v_res_353_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_355_, lean_object* v_stopPos_356_, lean_object* v_i_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_lt(v_i_357_, v_stopPos_356_);
if (v___x_358_ == 0)
{
return v_i_357_;
}
else
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_string_utf8_get(v_s_355_, v_i_357_);
v___x_360_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_359_);
if (v___x_360_ == 0)
{
return v_i_357_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_string_utf8_next(v_s_355_, v_i_357_);
lean_dec(v_i_357_);
v_i_357_ = v___x_361_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_363_, lean_object* v_stopPos_364_, lean_object* v_i_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_363_, v_stopPos_364_, v_i_365_);
lean_dec(v_stopPos_364_);
lean_dec_ref(v_s_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_e_370_; lean_object* v___x_371_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_string_utf8_byte_size(v_line_367_);
v_e_370_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_367_, v___x_369_, v___x_368_);
v___x_371_ = lean_string_utf8_extract(v_line_367_, v___x_368_, v_e_370_);
lean_dec(v_e_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_372_);
lean_dec_ref(v_line_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v_s_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v_s_378_);
lean_dec_ref(v_s_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7(lean_object* v_b_380_, lean_object* v_acc_381_, lean_object* v_i_382_){
_start:
{
lean_object* v_keyArray_387_; lean_object* v_valueArray_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_keyArray_387_ = lean_ctor_get(v_b_380_, 1);
v_valueArray_388_ = lean_ctor_get(v_b_380_, 2);
v___x_389_ = lean_array_get_size(v_keyArray_387_);
v___x_390_ = lean_nat_dec_lt(v_i_382_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_i_382_);
return v_acc_381_;
}
else
{
lean_object* v___x_391_; uint8_t v_isSome_392_; 
v___x_391_ = lean_array_fget_borrowed(v_keyArray_387_, v_i_382_);
v_isSome_392_ = lean_noption_is_some(v___x_391_);
if (v_isSome_392_ == 0)
{
goto v___jp_383_;
}
else
{
lean_object* v___x_393_; uint8_t v_isSome_394_; 
v___x_393_ = lean_array_fget_borrowed(v_valueArray_388_, v_i_382_);
v_isSome_394_ = lean_noption_is_some(v___x_393_);
if (v_isSome_394_ == 0)
{
goto v___jp_383_;
}
else
{
lean_object* v_val_395_; lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_inc(v___x_391_);
v_val_395_ = lean_noption_get(v___x_391_);
lean_inc(v___x_393_);
v_val_396_ = lean_noption_get(v___x_393_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_val_395_);
lean_ctor_set(v___x_397_, 1, v_val_396_);
v___x_398_ = lean_array_push(v_acc_381_, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_i_382_, v___x_399_);
lean_dec(v_i_382_);
v_acc_381_ = v___x_398_;
v_i_382_ = v___x_400_;
goto _start;
}
}
}
v___jp_383_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_i_382_, v___x_384_);
lean_dec(v_i_382_);
v_i_382_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7___boxed(lean_object* v_b_402_, lean_object* v_acc_403_, lean_object* v_i_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7(v_b_402_, v_acc_403_, v_i_404_);
lean_dec_ref(v_b_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_init_406_, lean_object* v_b_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__7(v_b_407_, v_init_406_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_init_410_, lean_object* v_b_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_init_410_, v_b_411_);
lean_dec_ref(v_b_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_m_413_, lean_object* v_query_414_, lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_zero_418_; uint8_t v_isZero_419_; 
v_zero_418_ = lean_unsigned_to_nat(0u);
v_isZero_419_ = lean_nat_dec_eq(v_x_416_, v_zero_418_);
if (v_isZero_419_ == 1)
{
lean_dec(v_x_417_);
lean_dec(v_x_416_);
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_box(2);
return v___x_420_;
}
else
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_val_421_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v_x_415_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_x_415_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_val_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_keyArray_429_; lean_object* v_valueArray_430_; lean_object* v___x_431_; uint8_t v_isSome_432_; 
v_keyArray_429_ = lean_ctor_get(v_m_413_, 1);
v_valueArray_430_ = lean_ctor_get(v_m_413_, 2);
v___x_431_ = lean_array_fget_borrowed(v_keyArray_429_, v_x_417_);
v_isSome_432_ = lean_noption_is_some(v___x_431_);
if (v_isSome_432_ == 0)
{
lean_dec(v_x_416_);
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v_x_417_);
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_x_417_);
v_val_434_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v_x_415_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v_x_415_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_val_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_one_442_; lean_object* v_n_443_; lean_object* v___y_445_; 
v_one_442_ = lean_unsigned_to_nat(1u);
v_n_443_ = lean_nat_sub(v_x_416_, v_one_442_);
lean_dec(v_x_416_);
if (v_isSome_432_ == 0)
{
goto v___jp_451_;
}
else
{
lean_object* v___x_453_; uint8_t v_isSome_454_; 
v___x_453_ = lean_array_fget_borrowed(v_valueArray_430_, v_x_417_);
v_isSome_454_ = lean_noption_is_some(v___x_453_);
if (v_isSome_454_ == 0)
{
goto v___jp_451_;
}
else
{
lean_object* v_val_455_; uint8_t v___x_456_; 
lean_inc(v___x_431_);
v_val_455_ = lean_noption_get(v___x_431_);
v___x_456_ = lean_string_dec_eq(v_val_455_, v_query_414_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
lean_dec(v_val_455_);
v___x_457_ = lean_array_get_size(v_keyArray_429_);
v___x_458_ = lean_nat_add(v_x_417_, v_one_442_);
lean_dec(v_x_417_);
v___x_459_ = lean_nat_dec_lt(v___x_458_, v___x_457_);
if (v___x_459_ == 0)
{
lean_dec(v___x_458_);
v_x_416_ = v_n_443_;
v_x_417_ = v_zero_418_;
goto _start;
}
else
{
v_x_416_ = v_n_443_;
v_x_417_ = v___x_458_;
goto _start;
}
}
else
{
lean_object* v_val_462_; lean_object* v___x_463_; 
lean_dec(v_n_443_);
lean_dec(v_x_415_);
lean_inc(v___x_453_);
v_val_462_ = lean_noption_get(v___x_453_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v_x_417_);
lean_ctor_set(v___x_463_, 1, v_val_455_);
lean_ctor_set(v___x_463_, 2, v_val_462_);
return v___x_463_;
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_array_get_size(v_keyArray_429_);
v___x_447_ = lean_nat_add(v_x_417_, v_one_442_);
lean_dec(v_x_417_);
v___x_448_ = lean_nat_dec_lt(v___x_447_, v___x_446_);
if (v___x_448_ == 0)
{
lean_dec(v___x_447_);
v_x_415_ = v___y_445_;
v_x_416_ = v_n_443_;
v_x_417_ = v_zero_418_;
goto _start;
}
else
{
v_x_415_ = v___y_445_;
v_x_416_ = v_n_443_;
v_x_417_ = v___x_447_;
goto _start;
}
}
v___jp_451_:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_452_; 
lean_inc(v_x_417_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_x_417_);
v___y_445_ = v___x_452_;
goto v___jp_444_;
}
else
{
v___y_445_ = v_x_415_;
goto v___jp_444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_m_464_, lean_object* v_query_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_m_464_, v_query_465_, v_x_466_, v_x_467_, v_x_468_);
lean_dec_ref(v_query_465_);
lean_dec_ref(v_m_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_470_, lean_object* v_query_471_){
_start:
{
lean_object* v_keyArray_472_; lean_object* v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_keyArray_472_ = lean_ctor_get(v_m_470_, 1);
v___x_473_ = lean_array_get_size(v_keyArray_472_);
v___x_474_ = lean_string_hash(v_query_471_);
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___x_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___x_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_473_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v___x_486_ = lean_usize_to_nat(v___x_485_);
v___x_487_ = lean_box(0);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_m_470_, v_query_471_, v___x_487_, v___x_473_, v___x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg___boxed(lean_object* v_m_489_, lean_object* v_query_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_489_, v_query_490_);
lean_dec_ref(v_query_490_);
lean_dec_ref(v_m_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg(lean_object* v_b_492_, lean_object* v_acc_493_, lean_object* v_i_494_){
_start:
{
lean_object* v___y_496_; lean_object* v_keyArray_504_; lean_object* v_valueArray_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_keyArray_504_ = lean_ctor_get(v_b_492_, 1);
v_valueArray_505_ = lean_ctor_get(v_b_492_, 2);
v___x_506_ = lean_array_get_size(v_keyArray_504_);
v___x_507_ = lean_nat_dec_lt(v_i_494_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v_i_494_);
return v_acc_493_;
}
else
{
lean_object* v___x_508_; uint8_t v_isSome_509_; 
v___x_508_ = lean_array_fget_borrowed(v_keyArray_504_, v_i_494_);
v_isSome_509_ = lean_noption_is_some(v___x_508_);
if (v_isSome_509_ == 0)
{
goto v___jp_500_;
}
else
{
lean_object* v___x_510_; uint8_t v_isSome_511_; 
v___x_510_ = lean_array_fget_borrowed(v_valueArray_505_, v_i_494_);
v_isSome_511_ = lean_noption_is_some(v___x_510_);
if (v_isSome_511_ == 0)
{
goto v___jp_500_;
}
else
{
lean_object* v_val_512_; lean_object* v_val_513_; lean_object* v_i_515_; lean_object* v___x_520_; 
lean_inc(v___x_508_);
v_val_512_ = lean_noption_get(v___x_508_);
lean_inc(v___x_510_);
v_val_513_ = lean_noption_get(v___x_510_);
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_acc_493_, v_val_512_);
switch(lean_obj_tag(v___x_520_))
{
case 0:
{
lean_object* v_index_521_; lean_object* v_size_522_; lean_object* v___x_523_; 
v_index_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_521_);
lean_dec_ref_known(v___x_520_, 3);
v_size_522_ = lean_ctor_get(v_acc_493_, 0);
lean_inc(v_size_522_);
v___x_523_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_493_, v_size_522_, v_index_521_, v_val_512_, v_val_513_);
lean_dec(v_index_521_);
v___y_496_ = v___x_523_;
goto v___jp_495_;
}
case 1:
{
lean_object* v_index_524_; 
v_index_524_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_524_);
lean_dec_ref_known(v___x_520_, 1);
v_i_515_ = v_index_524_;
goto v___jp_514_;
}
default: 
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_493_, v___x_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_index_527_; 
v_index_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_index_527_);
lean_dec_ref_known(v___x_526_, 1);
v_i_515_ = v_index_527_;
goto v___jp_514_;
}
else
{
lean_dec(v_val_513_);
lean_dec(v_val_512_);
v___y_496_ = v_acc_493_;
goto v___jp_495_;
}
}
}
v___jp_514_:
{
lean_object* v_size_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_size_516_ = lean_ctor_get(v_acc_493_, 0);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_size_516_, v___x_517_);
v___x_519_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_493_, v___x_518_, v_i_515_, v_val_512_, v_val_513_);
lean_dec(v_i_515_);
v___y_496_ = v___x_519_;
goto v___jp_495_;
}
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_i_494_, v___x_497_);
lean_dec(v_i_494_);
v_acc_493_ = v___y_496_;
v_i_494_ = v___x_498_;
goto _start;
}
v___jp_500_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_i_494_, v___x_501_);
lean_dec(v_i_494_);
v_i_494_ = v___x_502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_b_528_, lean_object* v_acc_529_, lean_object* v_i_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg(v_b_528_, v_acc_529_, v_i_530_);
lean_dec_ref(v_b_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg(lean_object* v_init_532_, lean_object* v_b_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg(v_b_533_, v_init_532_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg___boxed(lean_object* v_init_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg(v_init_536_, v_b_537_);
lean_dec_ref(v_b_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(lean_object* v_m_539_){
_start:
{
lean_object* v_keyArray_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_cellCount_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_target_547_; lean_object* v___x_548_; 
v_keyArray_540_ = lean_ctor_get(v_m_539_, 1);
v___x_541_ = lean_array_get_size(v_keyArray_540_);
v___x_542_ = lean_unsigned_to_nat(2u);
v_cellCount_543_ = lean_nat_mul(v___x_541_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_543_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_543_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_543_);
v_target_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_547_, 0, v___x_544_);
lean_ctor_set(v_target_547_, 1, v___x_545_);
lean_ctor_set(v_target_547_, 2, v___x_546_);
v___x_548_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg(v_target_547_, v_m_539_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg___boxed(lean_object* v_m_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(v_m_549_);
lean_dec_ref(v_m_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg(lean_object* v_m_551_, lean_object* v_query_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_551_, v_query_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_index_554_; lean_object* v_key_555_; lean_object* v_value_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_index_554_ = lean_ctor_get(v___x_553_, 0);
v_key_555_ = lean_ctor_get(v___x_553_, 1);
v_value_556_ = lean_ctor_get(v___x_553_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_key_555_);
lean_inc(v_index_554_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_index_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_key_555_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_value_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v___x_553_);
v___x_564_ = lean_box(1);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_565_, lean_object* v_query_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg(v_m_565_, v_query_566_);
lean_dec_ref(v_query_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg(v_m_568_, v_a_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_value_571_; lean_object* v___x_572_; 
v_value_571_ = lean_ctor_get(v___x_570_, 2);
lean_inc(v_value_571_);
lean_dec_ref_known(v___x_570_, 3);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_value_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_box(0);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_m_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_m_574_, v_a_575_);
lean_dec_ref(v_a_575_);
lean_dec_ref(v_m_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_577_, lean_object* v_a_578_, lean_object* v_fallback_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_m_577_, v_a_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_inc(v_fallback_579_);
return v_fallback_579_;
}
else
{
lean_object* v_val_581_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
return v_val_581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_582_, lean_object* v_a_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_582_, v_a_583_, v_fallback_584_);
lean_dec(v_fallback_584_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_m_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_as_588_, size_t v_sz_589_, size_t v_i_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___y_594_; uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_lt(v_i_590_, v_sz_589_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_b_591_);
return v___x_599_;
}
else
{
lean_object* v_a_600_; lean_object* v_file_601_; lean_object* v_pos_602_; lean_object* v_option_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_688_; 
v_a_600_ = lean_array_uget_borrowed(v_as_588_, v_i_590_);
v_file_601_ = lean_ctor_get(v_a_600_, 0);
v_pos_602_ = lean_ctor_get(v_a_600_, 1);
lean_inc_ref(v_pos_602_);
v_option_603_ = lean_ctor_get(v_a_600_, 2);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___closed__0));
lean_inc_ref(v_file_601_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_file_601_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_591_, v_file_601_, v___x_606_);
lean_dec_ref_known(v___x_606_, 2);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
v_snd_609_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_688_ == 0)
{
v___x_611_ = v___x_607_;
v_isShared_612_ = v_isSharedCheck_688_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snd_609_);
lean_inc(v_fst_608_);
lean_dec(v___x_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_688_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_line_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_686_; 
v_line_613_ = lean_ctor_get(v_pos_602_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_pos_602_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_pos_602_, 1);
lean_dec(v_unused_687_);
v___x_615_ = v_pos_602_;
v_isShared_616_ = v_isSharedCheck_686_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_line_613_);
lean_dec(v_pos_602_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_686_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
lean_inc(v_option_603_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v_option_603_);
lean_ctor_set(v___x_611_, 0, v_line_613_);
v___x_618_ = v___x_611_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_line_613_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_option_603_);
v___x_618_ = v_reuseFailAlloc_685_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_array_push(v_snd_609_, v___x_618_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___x_619_);
lean_ctor_set(v___x_615_, 0, v_fst_608_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_fst_608_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_619_);
v___x_621_ = v_reuseFailAlloc_684_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___y_623_; lean_object* v_i_624_; lean_object* v___y_630_; lean_object* v___y_639_; lean_object* v_i_640_; lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_591_, v_file_601_);
switch(lean_obj_tag(v___x_654_))
{
case 0:
{
lean_object* v_index_655_; lean_object* v_size_656_; lean_object* v___x_657_; 
v_index_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_index_655_);
lean_dec_ref_known(v___x_654_, 3);
v_size_656_ = lean_ctor_get(v_b_591_, 0);
lean_inc(v_size_656_);
lean_inc_ref(v_file_601_);
v___x_657_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_591_, v_size_656_, v_index_655_, v_file_601_, v___x_621_);
lean_dec(v_index_655_);
v___y_594_ = v___x_657_;
goto v___jp_593_;
}
case 1:
{
lean_object* v_index_658_; lean_object* v_size_659_; lean_object* v_keyArray_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_index_658_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_index_658_);
lean_dec_ref_known(v___x_654_, 1);
v_size_659_ = lean_ctor_get(v_b_591_, 0);
v_keyArray_660_ = lean_ctor_get(v_b_591_, 1);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_size_659_, v___x_661_);
v___x_663_ = lean_array_get_size(v_keyArray_660_);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec(v___x_662_);
lean_dec(v_index_658_);
goto v___jp_645_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_665_ = lean_unsigned_to_nat(4u);
v___x_666_ = lean_nat_mul(v___x_662_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(3u);
v___x_668_ = lean_nat_mul(v___x_663_, v___x_667_);
v___x_669_ = lean_nat_dec_le(v___x_666_, v___x_668_);
lean_dec(v___x_668_);
lean_dec(v___x_666_);
if (v___x_669_ == 0)
{
lean_dec(v___x_662_);
lean_dec(v_index_658_);
goto v___jp_645_;
}
else
{
lean_object* v___x_670_; 
lean_inc_ref(v_file_601_);
v___x_670_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_591_, v___x_662_, v_index_658_, v_file_601_, v___x_621_);
lean_dec(v_index_658_);
v___y_594_ = v___x_670_;
goto v___jp_593_;
}
}
}
default: 
{
lean_object* v_size_671_; lean_object* v_keyArray_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_size_671_ = lean_ctor_get(v_b_591_, 0);
v_keyArray_672_ = lean_ctor_get(v_b_591_, 1);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_size_671_, v___x_673_);
v___x_675_ = lean_array_get_size(v_keyArray_672_);
v___x_676_ = lean_nat_dec_lt(v___x_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_674_);
v___x_677_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(v_b_591_);
lean_dec_ref(v_b_591_);
v___y_630_ = v___x_677_;
goto v___jp_629_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_678_ = lean_unsigned_to_nat(4u);
v___x_679_ = lean_nat_mul(v___x_674_, v___x_678_);
lean_dec(v___x_674_);
v___x_680_ = lean_unsigned_to_nat(3u);
v___x_681_ = lean_nat_mul(v___x_675_, v___x_680_);
v___x_682_ = lean_nat_dec_le(v___x_679_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(v_b_591_);
lean_dec_ref(v_b_591_);
v___y_630_ = v___x_683_;
goto v___jp_629_;
}
else
{
v___y_630_ = v_b_591_;
goto v___jp_629_;
}
}
}
}
v___jp_622_:
{
lean_object* v_size_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_size_625_ = lean_ctor_get(v___y_623_, 0);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_size_625_, v___x_626_);
lean_inc_ref(v_file_601_);
v___x_628_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_623_, v___x_627_, v_i_624_, v_file_601_, v___x_621_);
lean_dec(v_i_624_);
v___y_594_ = v___x_628_;
goto v___jp_593_;
}
v___jp_629_:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v___y_630_, v_file_601_);
switch(lean_obj_tag(v___x_631_))
{
case 0:
{
lean_object* v_index_632_; lean_object* v_size_633_; lean_object* v___x_634_; 
v_index_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_index_632_);
lean_dec_ref_known(v___x_631_, 3);
v_size_633_ = lean_ctor_get(v___y_630_, 0);
lean_inc(v_size_633_);
lean_inc_ref(v_file_601_);
v___x_634_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_630_, v_size_633_, v_index_632_, v_file_601_, v___x_621_);
lean_dec(v_index_632_);
v___y_594_ = v___x_634_;
goto v___jp_593_;
}
case 1:
{
lean_object* v_index_635_; 
v_index_635_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_index_635_);
lean_dec_ref_known(v___x_631_, 1);
v___y_623_ = v___y_630_;
v_i_624_ = v_index_635_;
goto v___jp_622_;
}
default: 
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_630_, v___x_604_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_index_637_; 
v_index_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_index_637_);
lean_dec_ref_known(v___x_636_, 1);
v___y_623_ = v___y_630_;
v_i_624_ = v_index_637_;
goto v___jp_622_;
}
else
{
lean_dec_ref(v___x_621_);
v___y_594_ = v___y_630_;
goto v___jp_593_;
}
}
}
}
v___jp_638_:
{
lean_object* v_size_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_size_641_ = lean_ctor_get(v___y_639_, 0);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_size_641_, v___x_642_);
lean_inc_ref(v_file_601_);
v___x_644_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_639_, v___x_643_, v_i_640_, v_file_601_, v___x_621_);
lean_dec(v_i_640_);
v___y_594_ = v___x_644_;
goto v___jp_593_;
}
v___jp_645_:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(v_b_591_);
lean_dec_ref(v_b_591_);
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v___x_646_, v_file_601_);
switch(lean_obj_tag(v___x_647_))
{
case 0:
{
lean_object* v_index_648_; lean_object* v_size_649_; lean_object* v___x_650_; 
v_index_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_index_648_);
lean_dec_ref_known(v___x_647_, 3);
v_size_649_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_size_649_);
lean_inc_ref(v_file_601_);
v___x_650_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_646_, v_size_649_, v_index_648_, v_file_601_, v___x_621_);
lean_dec(v_index_648_);
v___y_594_ = v___x_650_;
goto v___jp_593_;
}
case 1:
{
lean_object* v_index_651_; 
v_index_651_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_index_651_);
lean_dec_ref_known(v___x_647_, 1);
v___y_639_ = v___x_646_;
v_i_640_ = v_index_651_;
goto v___jp_638_;
}
default: 
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_646_, v___x_604_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_index_653_; 
v_index_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_index_653_);
lean_dec_ref_known(v___x_652_, 1);
v___y_639_ = v___x_646_;
v_i_640_ = v_index_653_;
goto v___jp_638_;
}
else
{
lean_dec_ref(v___x_621_);
v___y_594_ = v___x_646_;
goto v___jp_593_;
}
}
}
}
}
}
}
}
}
v___jp_593_:
{
size_t v___x_595_; size_t v___x_596_; 
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_590_, v___x_595_);
v_i_590_ = v___x_596_;
v_b_591_ = v___y_594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_as_689_, lean_object* v_sz_690_, lean_object* v_i_691_, lean_object* v_b_692_, lean_object* v___y_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v_i_boxed_695_; lean_object* v_res_696_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_690_);
lean_dec(v_sz_690_);
v_i_boxed_695_ = lean_unbox_usize(v_i_691_);
lean_dec(v_i_691_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_as_689_, v_sz_boxed_694_, v_i_boxed_695_, v_b_692_);
lean_dec_ref(v_as_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg(lean_object* v_m_697_, lean_object* v_query_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_zero_702_; uint8_t v_isZero_703_; 
v_zero_702_ = lean_unsigned_to_nat(0u);
v_isZero_703_ = lean_nat_dec_eq(v_x_700_, v_zero_702_);
if (v_isZero_703_ == 1)
{
lean_dec(v_x_701_);
lean_dec(v_x_700_);
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(2);
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_val_705_ = lean_ctor_get(v_x_699_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v_x_699_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v_x_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_val_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_keyArray_713_; lean_object* v_valueArray_714_; lean_object* v___x_715_; uint8_t v_isSome_716_; 
v_keyArray_713_ = lean_ctor_get(v_m_697_, 1);
v_valueArray_714_ = lean_ctor_get(v_m_697_, 2);
v___x_715_ = lean_array_fget_borrowed(v_keyArray_713_, v_x_701_);
v_isSome_716_ = lean_noption_is_some(v___x_715_);
if (v_isSome_716_ == 0)
{
lean_dec(v_x_700_);
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_x_701_);
return v___x_717_;
}
else
{
lean_object* v_val_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_x_701_);
v_val_718_ = lean_ctor_get(v_x_699_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v_x_699_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_val_718_);
lean_dec(v_x_699_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_val_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_one_726_; lean_object* v_n_727_; lean_object* v___y_729_; 
v_one_726_ = lean_unsigned_to_nat(1u);
v_n_727_ = lean_nat_sub(v_x_700_, v_one_726_);
lean_dec(v_x_700_);
if (v_isSome_716_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v___x_737_; uint8_t v_isSome_738_; 
v___x_737_ = lean_array_fget_borrowed(v_valueArray_714_, v_x_701_);
v_isSome_738_ = lean_noption_is_some(v___x_737_);
if (v_isSome_738_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v_val_739_; uint8_t v___x_740_; 
lean_inc(v___x_715_);
v_val_739_ = lean_noption_get(v___x_715_);
v___x_740_ = lean_nat_dec_eq(v_val_739_, v_query_698_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
lean_dec(v_val_739_);
v___x_741_ = lean_array_get_size(v_keyArray_713_);
v___x_742_ = lean_nat_add(v_x_701_, v_one_726_);
lean_dec(v_x_701_);
v___x_743_ = lean_nat_dec_lt(v___x_742_, v___x_741_);
if (v___x_743_ == 0)
{
lean_dec(v___x_742_);
v_x_700_ = v_n_727_;
v_x_701_ = v_zero_702_;
goto _start;
}
else
{
v_x_700_ = v_n_727_;
v_x_701_ = v___x_742_;
goto _start;
}
}
else
{
lean_object* v_val_746_; lean_object* v___x_747_; 
lean_dec(v_n_727_);
lean_dec(v_x_699_);
lean_inc(v___x_737_);
v_val_746_ = lean_noption_get(v___x_737_);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v_x_701_);
lean_ctor_set(v___x_747_, 1, v_val_739_);
lean_ctor_set(v___x_747_, 2, v_val_746_);
return v___x_747_;
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_array_get_size(v_keyArray_713_);
v___x_731_ = lean_nat_add(v_x_701_, v_one_726_);
lean_dec(v_x_701_);
v___x_732_ = lean_nat_dec_lt(v___x_731_, v___x_730_);
if (v___x_732_ == 0)
{
lean_dec(v___x_731_);
v_x_699_ = v___y_729_;
v_x_700_ = v_n_727_;
v_x_701_ = v_zero_702_;
goto _start;
}
else
{
v_x_699_ = v___y_729_;
v_x_700_ = v_n_727_;
v_x_701_ = v___x_731_;
goto _start;
}
}
v___jp_735_:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_736_; 
lean_inc(v_x_701_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_x_701_);
v___y_729_ = v___x_736_;
goto v___jp_728_;
}
else
{
v___y_729_ = v_x_699_;
goto v___jp_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg___boxed(lean_object* v_m_748_, lean_object* v_query_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg(v_m_748_, v_query_749_, v_x_750_, v_x_751_, v_x_752_);
lean_dec(v_query_749_);
lean_dec_ref(v_m_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(lean_object* v_m_754_, lean_object* v_query_755_){
_start:
{
lean_object* v_keyArray_756_; lean_object* v___x_757_; uint64_t v___x_758_; uint64_t v___x_759_; uint64_t v___x_760_; uint64_t v_fold_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_keyArray_756_ = lean_ctor_get(v_m_754_, 1);
v___x_757_ = lean_array_get_size(v_keyArray_756_);
v___x_758_ = lean_uint64_of_nat(v_query_755_);
v___x_759_ = 32ULL;
v___x_760_ = lean_uint64_shift_right(v___x_758_, v___x_759_);
v_fold_761_ = lean_uint64_xor(v___x_758_, v___x_760_);
v___x_762_ = 16ULL;
v___x_763_ = lean_uint64_shift_right(v_fold_761_, v___x_762_);
v___x_764_ = lean_uint64_xor(v_fold_761_, v___x_763_);
v___x_765_ = lean_uint64_to_usize(v___x_764_);
v___x_766_ = lean_usize_of_nat(v___x_757_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_sub(v___x_766_, v___x_767_);
v___x_769_ = lean_usize_land(v___x_765_, v___x_768_);
v___x_770_ = lean_usize_to_nat(v___x_769_);
v___x_771_ = lean_box(0);
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg(v_m_754_, v_query_755_, v___x_771_, v___x_757_, v___x_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object* v_m_773_, lean_object* v_query_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v_m_773_, v_query_774_);
lean_dec(v_query_774_);
lean_dec_ref(v_m_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg(lean_object* v_m_776_, lean_object* v_query_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v_m_776_, v_query_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_index_779_; lean_object* v_key_780_; lean_object* v_value_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_index_779_ = lean_ctor_get(v___x_778_, 0);
v_key_780_ = lean_ctor_get(v___x_778_, 1);
v_value_781_ = lean_ctor_get(v___x_778_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_778_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_value_781_);
lean_inc(v_key_780_);
lean_inc(v_index_779_);
lean_dec(v___x_778_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_index_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_key_780_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_value_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v___x_789_; 
lean_dec(v___x_778_);
v___x_789_ = lean_box(1);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_m_790_, lean_object* v_query_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg(v_m_790_, v_query_791_);
lean_dec(v_query_791_);
lean_dec_ref(v_m_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg(lean_object* v_m_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg(v_m_793_, v_a_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_value_796_; lean_object* v___x_797_; 
v_value_796_ = lean_ctor_get(v___x_795_, 2);
lean_inc(v_value_796_);
lean_dec_ref_known(v___x_795_, 3);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_value_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg___boxed(lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg(v_m_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_m_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_802_, lean_object* v_a_803_, lean_object* v_fallback_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg(v_m_802_, v_a_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_inc(v_fallback_804_);
return v_fallback_804_;
}
else
{
lean_object* v_val_806_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_805_, 1);
return v_val_806_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg___boxed(lean_object* v_m_807_, lean_object* v_a_808_, lean_object* v_fallback_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_807_, v_a_808_, v_fallback_809_);
lean_dec(v_fallback_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_m_807_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11(lean_object* v_a_811_, lean_object* v_as_812_, size_t v_i_813_, size_t v_stop_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_eq(v_i_813_, v_stop_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_array_uget_borrowed(v_as_812_, v_i_813_);
v___x_817_ = lean_name_eq(v_a_811_, v___x_816_);
if (v___x_817_ == 0)
{
size_t v___x_818_; size_t v___x_819_; 
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_i_813_, v___x_818_);
v_i_813_ = v___x_819_;
goto _start;
}
else
{
return v___x_817_;
}
}
else
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11___boxed(lean_object* v_a_822_, lean_object* v_as_823_, lean_object* v_i_824_, lean_object* v_stop_825_){
_start:
{
size_t v_i_boxed_826_; size_t v_stop_boxed_827_; uint8_t v_res_828_; lean_object* v_r_829_; 
v_i_boxed_826_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_stop_boxed_827_ = lean_unbox_usize(v_stop_825_);
lean_dec(v_stop_825_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11(v_a_822_, v_as_823_, v_i_boxed_826_, v_stop_boxed_827_);
lean_dec_ref(v_as_823_);
lean_dec(v_a_822_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_array_get_size(v_as_830_);
v___x_834_ = lean_nat_dec_lt(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
return v___x_834_;
}
else
{
if (v___x_834_ == 0)
{
return v___x_834_;
}
else
{
size_t v___x_835_; size_t v___x_836_; uint8_t v___x_837_; 
v___x_835_ = ((size_t)0ULL);
v___x_836_ = lean_usize_of_nat(v___x_833_);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6_spec__11(v_a_831_, v_as_830_, v___x_835_, v___x_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_as_838_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg(lean_object* v_b_842_, lean_object* v_acc_843_, lean_object* v_i_844_){
_start:
{
lean_object* v___y_846_; lean_object* v_keyArray_854_; lean_object* v_valueArray_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_keyArray_854_ = lean_ctor_get(v_b_842_, 1);
v_valueArray_855_ = lean_ctor_get(v_b_842_, 2);
v___x_856_ = lean_array_get_size(v_keyArray_854_);
v___x_857_ = lean_nat_dec_lt(v_i_844_, v___x_856_);
if (v___x_857_ == 0)
{
lean_dec(v_i_844_);
return v_acc_843_;
}
else
{
lean_object* v___x_858_; uint8_t v_isSome_859_; 
v___x_858_ = lean_array_fget_borrowed(v_keyArray_854_, v_i_844_);
v_isSome_859_ = lean_noption_is_some(v___x_858_);
if (v_isSome_859_ == 0)
{
goto v___jp_850_;
}
else
{
lean_object* v___x_860_; uint8_t v_isSome_861_; 
v___x_860_ = lean_array_fget_borrowed(v_valueArray_855_, v_i_844_);
v_isSome_861_ = lean_noption_is_some(v___x_860_);
if (v_isSome_861_ == 0)
{
goto v___jp_850_;
}
else
{
lean_object* v_val_862_; lean_object* v_val_863_; lean_object* v_i_865_; lean_object* v___x_870_; 
lean_inc(v___x_858_);
v_val_862_ = lean_noption_get(v___x_858_);
lean_inc(v___x_860_);
v_val_863_ = lean_noption_get(v___x_860_);
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v_acc_843_, v_val_862_);
switch(lean_obj_tag(v___x_870_))
{
case 0:
{
lean_object* v_index_871_; lean_object* v_size_872_; lean_object* v___x_873_; 
v_index_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_index_871_);
lean_dec_ref_known(v___x_870_, 3);
v_size_872_ = lean_ctor_get(v_acc_843_, 0);
lean_inc(v_size_872_);
v___x_873_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_843_, v_size_872_, v_index_871_, v_val_862_, v_val_863_);
lean_dec(v_index_871_);
v___y_846_ = v___x_873_;
goto v___jp_845_;
}
case 1:
{
lean_object* v_index_874_; 
v_index_874_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_index_874_);
lean_dec_ref_known(v___x_870_, 1);
v_i_865_ = v_index_874_;
goto v___jp_864_;
}
default: 
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_843_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_index_877_; 
v_index_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_index_877_);
lean_dec_ref_known(v___x_876_, 1);
v_i_865_ = v_index_877_;
goto v___jp_864_;
}
else
{
lean_dec(v_val_863_);
lean_dec(v_val_862_);
v___y_846_ = v_acc_843_;
goto v___jp_845_;
}
}
}
v___jp_864_:
{
lean_object* v_size_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_size_866_ = lean_ctor_get(v_acc_843_, 0);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_size_866_, v___x_867_);
v___x_869_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_843_, v___x_868_, v_i_865_, v_val_862_, v_val_863_);
lean_dec(v_i_865_);
v___y_846_ = v___x_869_;
goto v___jp_845_;
}
}
}
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_i_844_, v___x_847_);
lean_dec(v_i_844_);
v_acc_843_ = v___y_846_;
v_i_844_ = v___x_848_;
goto _start;
}
v___jp_850_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v_i_844_, v___x_851_);
lean_dec(v_i_844_);
v_i_844_ = v___x_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg___boxed(lean_object* v_b_878_, lean_object* v_acc_879_, lean_object* v_i_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg(v_b_878_, v_acc_879_, v_i_880_);
lean_dec_ref(v_b_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg(lean_object* v_init_882_, lean_object* v_b_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg(v_b_883_, v_init_882_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg___boxed(lean_object* v_init_886_, lean_object* v_b_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg(v_init_886_, v_b_887_);
lean_dec_ref(v_b_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_m_889_){
_start:
{
lean_object* v_keyArray_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_cellCount_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_target_897_; lean_object* v___x_898_; 
v_keyArray_890_ = lean_ctor_get(v_m_889_, 1);
v___x_891_ = lean_array_get_size(v_keyArray_890_);
v___x_892_ = lean_unsigned_to_nat(2u);
v_cellCount_893_ = lean_nat_mul(v___x_891_, v___x_892_);
v___x_894_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_893_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_893_);
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_893_);
v_target_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_897_, 0, v___x_894_);
lean_ctor_set(v_target_897_, 1, v___x_895_);
lean_ctor_set(v_target_897_, 2, v___x_896_);
v___x_898_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg(v_target_897_, v_m_889_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_m_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_m_899_);
lean_dec_ref(v_m_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_){
_start:
{
lean_object* v_a_909_; uint8_t v___x_913_; 
v___x_913_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_b_906_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_a_915_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
v_fst_916_ = lean_ctor_get(v_a_915_, 0);
v_snd_917_ = lean_ctor_get(v_a_915_, 1);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___closed__0));
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_906_, v_fst_916_, v___x_919_);
v___x_921_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v___x_920_, v_snd_917_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v_i_925_; lean_object* v___y_931_; lean_object* v___y_940_; lean_object* v_i_941_; lean_object* v___x_955_; 
lean_inc(v_snd_917_);
v___x_922_ = lean_array_push(v___x_920_, v_snd_917_);
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v_b_906_, v_fst_916_);
switch(lean_obj_tag(v___x_955_))
{
case 0:
{
lean_object* v_index_956_; lean_object* v_size_957_; lean_object* v___x_958_; 
v_index_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_956_);
lean_dec_ref_known(v___x_955_, 3);
v_size_957_ = lean_ctor_get(v_b_906_, 0);
lean_inc(v_size_957_);
lean_inc(v_fst_916_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_906_, v_size_957_, v_index_956_, v_fst_916_, v___x_922_);
lean_dec(v_index_956_);
v_a_909_ = v___x_958_;
goto v___jp_908_;
}
case 1:
{
lean_object* v_index_959_; lean_object* v_size_960_; lean_object* v_keyArray_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v_index_959_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_959_);
lean_dec_ref_known(v___x_955_, 1);
v_size_960_ = lean_ctor_get(v_b_906_, 0);
v_keyArray_961_ = lean_ctor_get(v_b_906_, 1);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_size_960_, v___x_962_);
v___x_964_ = lean_array_get_size(v_keyArray_961_);
v___x_965_ = lean_nat_dec_lt(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_dec(v___x_963_);
lean_dec(v_index_959_);
goto v___jp_946_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_nat_mul(v___x_963_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(3u);
v___x_969_ = lean_nat_mul(v___x_964_, v___x_968_);
v___x_970_ = lean_nat_dec_le(v___x_967_, v___x_969_);
lean_dec(v___x_969_);
lean_dec(v___x_967_);
if (v___x_970_ == 0)
{
lean_dec(v___x_963_);
lean_dec(v_index_959_);
goto v___jp_946_;
}
else
{
lean_object* v___x_971_; 
lean_inc(v_fst_916_);
v___x_971_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_906_, v___x_963_, v_index_959_, v_fst_916_, v___x_922_);
lean_dec(v_index_959_);
v_a_909_ = v___x_971_;
goto v___jp_908_;
}
}
}
default: 
{
lean_object* v_size_972_; lean_object* v_keyArray_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_size_972_ = lean_ctor_get(v_b_906_, 0);
v_keyArray_973_ = lean_ctor_get(v_b_906_, 1);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_add(v_size_972_, v___x_974_);
v___x_976_ = lean_array_get_size(v_keyArray_973_);
v___x_977_ = lean_nat_dec_lt(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v___x_975_);
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_b_906_);
lean_dec_ref(v_b_906_);
v___y_931_ = v___x_978_;
goto v___jp_930_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_979_ = lean_unsigned_to_nat(4u);
v___x_980_ = lean_nat_mul(v___x_975_, v___x_979_);
lean_dec(v___x_975_);
v___x_981_ = lean_unsigned_to_nat(3u);
v___x_982_ = lean_nat_mul(v___x_976_, v___x_981_);
v___x_983_ = lean_nat_dec_le(v___x_980_, v___x_982_);
lean_dec(v___x_982_);
lean_dec(v___x_980_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_b_906_);
lean_dec_ref(v_b_906_);
v___y_931_ = v___x_984_;
goto v___jp_930_;
}
else
{
v___y_931_ = v_b_906_;
goto v___jp_930_;
}
}
}
}
v___jp_923_:
{
lean_object* v_size_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_size_926_ = lean_ctor_get(v___y_924_, 0);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_size_926_, v___x_927_);
lean_inc(v_fst_916_);
v___x_929_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_924_, v___x_928_, v_i_925_, v_fst_916_, v___x_922_);
lean_dec(v_i_925_);
v_a_909_ = v___x_929_;
goto v___jp_908_;
}
v___jp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v___y_931_, v_fst_916_);
switch(lean_obj_tag(v___x_932_))
{
case 0:
{
lean_object* v_index_933_; lean_object* v_size_934_; lean_object* v___x_935_; 
v_index_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_933_);
lean_dec_ref_known(v___x_932_, 3);
v_size_934_ = lean_ctor_get(v___y_931_, 0);
lean_inc(v_size_934_);
lean_inc(v_fst_916_);
v___x_935_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_931_, v_size_934_, v_index_933_, v_fst_916_, v___x_922_);
lean_dec(v_index_933_);
v_a_909_ = v___x_935_;
goto v___jp_908_;
}
case 1:
{
lean_object* v_index_936_; 
v_index_936_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_index_936_);
lean_dec_ref_known(v___x_932_, 1);
v___y_924_ = v___y_931_;
v_i_925_ = v_index_936_;
goto v___jp_923_;
}
default: 
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_931_, v___x_918_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_index_938_; 
v_index_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_index_938_);
lean_dec_ref_known(v___x_937_, 1);
v___y_924_ = v___y_931_;
v_i_925_ = v_index_938_;
goto v___jp_923_;
}
else
{
lean_dec_ref(v___x_922_);
v_a_909_ = v___y_931_;
goto v___jp_908_;
}
}
}
}
v___jp_939_:
{
lean_object* v_size_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_size_942_ = lean_ctor_get(v___y_940_, 0);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_size_942_, v___x_943_);
lean_inc(v_fst_916_);
v___x_945_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_940_, v___x_944_, v_i_941_, v_fst_916_, v___x_922_);
lean_dec(v_i_941_);
v_a_909_ = v___x_945_;
goto v___jp_908_;
}
v___jp_946_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_b_906_);
lean_dec_ref(v_b_906_);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v___x_947_, v_fst_916_);
switch(lean_obj_tag(v___x_948_))
{
case 0:
{
lean_object* v_index_949_; lean_object* v_size_950_; lean_object* v___x_951_; 
v_index_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_index_949_);
lean_dec_ref_known(v___x_948_, 3);
v_size_950_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_size_950_);
lean_inc(v_fst_916_);
v___x_951_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_947_, v_size_950_, v_index_949_, v_fst_916_, v___x_922_);
lean_dec(v_index_949_);
v_a_909_ = v___x_951_;
goto v___jp_908_;
}
case 1:
{
lean_object* v_index_952_; 
v_index_952_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_index_952_);
lean_dec_ref_known(v___x_948_, 1);
v___y_940_ = v___x_947_;
v_i_941_ = v_index_952_;
goto v___jp_939_;
}
default: 
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_947_, v___x_918_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_index_954_; 
v_index_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_index_954_);
lean_dec_ref_known(v___x_953_, 1);
v___y_940_ = v___x_947_;
v_i_941_ = v_index_954_;
goto v___jp_939_;
}
else
{
lean_dec_ref(v___x_922_);
v_a_909_ = v___x_947_;
goto v___jp_908_;
}
}
}
}
}
else
{
lean_dec(v___x_920_);
v_a_909_ = v_b_906_;
goto v___jp_908_;
}
}
v___jp_908_:
{
size_t v___x_910_; size_t v___x_911_; 
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_905_, v___x_910_);
v_i_905_ = v___x_911_;
v_b_906_ = v_a_909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_as_985_, lean_object* v_sz_986_, lean_object* v_i_987_, lean_object* v_b_988_, lean_object* v___y_989_){
_start:
{
size_t v_sz_boxed_990_; size_t v_i_boxed_991_; lean_object* v_res_992_; 
v_sz_boxed_990_ = lean_unbox_usize(v_sz_986_);
lean_dec(v_sz_986_);
v_i_boxed_991_ = lean_unbox_usize(v_i_987_);
lean_dec(v_i_987_);
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_as_985_, v_sz_boxed_990_, v_i_boxed_991_, v_b_988_);
lean_dec_ref(v_as_985_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21(lean_object* v_b_993_, lean_object* v_acc_994_, lean_object* v_i_995_){
_start:
{
lean_object* v_keyArray_1000_; lean_object* v_valueArray_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_keyArray_1000_ = lean_ctor_get(v_b_993_, 1);
v_valueArray_1001_ = lean_ctor_get(v_b_993_, 2);
v___x_1002_ = lean_array_get_size(v_keyArray_1000_);
v___x_1003_ = lean_nat_dec_lt(v_i_995_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec(v_i_995_);
return v_acc_994_;
}
else
{
lean_object* v___x_1004_; uint8_t v_isSome_1005_; 
v___x_1004_ = lean_array_fget_borrowed(v_keyArray_1000_, v_i_995_);
v_isSome_1005_ = lean_noption_is_some(v___x_1004_);
if (v_isSome_1005_ == 0)
{
goto v___jp_996_;
}
else
{
lean_object* v___x_1006_; uint8_t v_isSome_1007_; 
v___x_1006_ = lean_array_fget_borrowed(v_valueArray_1001_, v_i_995_);
v_isSome_1007_ = lean_noption_is_some(v___x_1006_);
if (v_isSome_1007_ == 0)
{
goto v___jp_996_;
}
else
{
lean_object* v_val_1008_; lean_object* v_val_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc(v___x_1004_);
v_val_1008_ = lean_noption_get(v___x_1004_);
lean_inc(v___x_1006_);
v_val_1009_ = lean_noption_get(v___x_1006_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_val_1008_);
lean_ctor_set(v___x_1010_, 1, v_val_1009_);
v___x_1011_ = lean_array_push(v_acc_994_, v___x_1010_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_add(v_i_995_, v___x_1012_);
lean_dec(v_i_995_);
v_acc_994_ = v___x_1011_;
v_i_995_ = v___x_1013_;
goto _start;
}
}
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_i_995_, v___x_997_);
lean_dec(v_i_995_);
v_i_995_ = v___x_998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21___boxed(lean_object* v_b_1015_, lean_object* v_acc_1016_, lean_object* v_i_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21(v_b_1015_, v_acc_1016_, v_i_1017_);
lean_dec_ref(v_b_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_init_1019_, lean_object* v_b_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__21(v_b_1020_, v_init_1019_, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_init_1023_, lean_object* v_b_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_init_1023_, v_b_1024_);
lean_dec_ref(v_b_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(lean_object* v_s_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_putStr_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_get_stdout();
v_putStr_1029_ = lean_ctor_get(v___x_1028_, 4);
lean_inc_ref(v_putStr_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = lean_apply_2(v_putStr_1029_, v_s_1026_, lean_box(0));
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27___boxed(lean_object* v_s_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(v_s_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_1034_){
_start:
{
uint32_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = 10;
v___x_1037_ = lean_string_push(v_s_1034_, v___x_1036_);
v___x_1038_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(lean_object* v_a_1042_, lean_object* v_b_1043_){
_start:
{
lean_object* v_fst_1044_; lean_object* v_fst_1045_; uint8_t v___x_1046_; 
v_fst_1044_ = lean_ctor_get(v_b_1043_, 0);
v_fst_1045_ = lean_ctor_get(v_a_1042_, 0);
v___x_1046_ = lean_nat_dec_lt(v_fst_1044_, v_fst_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0___boxed(lean_object* v_a_1047_, lean_object* v_b_1048_){
_start:
{
uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(v_a_1047_, v_b_1048_);
lean_dec_ref(v_b_1048_);
lean_dec_ref(v_a_1047_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg(lean_object* v_hi_1051_, lean_object* v_pivot_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_lt(v_k_1055_, v_hi_1051_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v_k_1055_);
v___x_1057_ = lean_array_fswap(v_as_1053_, v_i_1054_, v_hi_1051_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_i_1054_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_fst_1059_; lean_object* v___x_1060_; lean_object* v_fst_1061_; uint8_t v___x_1062_; 
v_fst_1059_ = lean_ctor_get(v_pivot_1052_, 0);
v___x_1060_ = lean_array_fget_borrowed(v_as_1053_, v_k_1055_);
v_fst_1061_ = lean_ctor_get(v___x_1060_, 0);
v___x_1062_ = lean_nat_dec_lt(v_fst_1059_, v_fst_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_k_1055_, v___x_1063_);
lean_dec(v_k_1055_);
v_k_1055_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_array_fswap(v_as_1053_, v_i_1054_, v_k_1055_);
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_add(v_i_1054_, v___x_1067_);
lean_dec(v_i_1054_);
v___x_1069_ = lean_nat_add(v_k_1055_, v___x_1067_);
lean_dec(v_k_1055_);
v_as_1053_ = v___x_1066_;
v_i_1054_ = v___x_1068_;
v_k_1055_ = v___x_1069_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg___boxed(lean_object* v_hi_1071_, lean_object* v_pivot_1072_, lean_object* v_as_1073_, lean_object* v_i_1074_, lean_object* v_k_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg(v_hi_1071_, v_pivot_1072_, v_as_1073_, v_i_1074_, v_k_1075_);
lean_dec_ref(v_pivot_1072_);
lean_dec(v_hi_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(lean_object* v_n_1077_, lean_object* v_as_1078_, lean_object* v_lo_1079_, lean_object* v_hi_1080_){
_start:
{
lean_object* v___y_1082_; uint8_t v___x_1092_; 
v___x_1092_ = lean_nat_dec_lt(v_lo_1079_, v_hi_1080_);
if (v___x_1092_ == 0)
{
lean_dec(v_lo_1079_);
return v_as_1078_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_mid_1095_; lean_object* v___y_1097_; lean_object* v___y_1103_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1093_ = lean_nat_add(v_lo_1079_, v_hi_1080_);
v___x_1094_ = lean_unsigned_to_nat(1u);
v_mid_1095_ = lean_nat_shiftr(v___x_1093_, v___x_1094_);
lean_dec(v___x_1093_);
v___x_1108_ = lean_array_fget_borrowed(v_as_1078_, v_mid_1095_);
v___x_1109_ = lean_array_fget_borrowed(v_as_1078_, v_lo_1079_);
v___x_1110_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
v___y_1103_ = v_as_1078_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_array_fswap(v_as_1078_, v_lo_1079_, v_mid_1095_);
v___y_1103_ = v___x_1111_;
goto v___jp_1102_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_array_fget_borrowed(v___y_1097_, v_mid_1095_);
v___x_1099_ = lean_array_fget_borrowed(v___y_1097_, v_hi_1080_);
v___x_1100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_dec(v_mid_1095_);
v___y_1082_ = v___y_1097_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_array_fswap(v___y_1097_, v_mid_1095_, v_hi_1080_);
lean_dec(v_mid_1095_);
v___y_1082_ = v___x_1101_;
goto v___jp_1081_;
}
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_array_fget_borrowed(v___y_1103_, v_hi_1080_);
v___x_1105_ = lean_array_fget_borrowed(v___y_1103_, v_lo_1079_);
v___x_1106_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___lam__0(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
v___y_1097_ = v___y_1103_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_array_fswap(v___y_1103_, v_lo_1079_, v_hi_1080_);
v___y_1097_ = v___x_1107_;
goto v___jp_1096_;
}
}
}
v___jp_1081_:
{
lean_object* v_pivot_1083_; lean_object* v___x_1084_; lean_object* v_fst_1085_; lean_object* v_snd_1086_; uint8_t v___x_1087_; 
v_pivot_1083_ = lean_array_fget(v___y_1082_, v_hi_1080_);
lean_inc_n(v_lo_1079_, 2);
v___x_1084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg(v_hi_1080_, v_pivot_1083_, v___y_1082_, v_lo_1079_, v_lo_1079_);
lean_dec(v_pivot_1083_);
v_fst_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_fst_1085_);
v_snd_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_snd_1086_);
lean_dec_ref(v___x_1084_);
v___x_1087_ = lean_nat_dec_le(v_hi_1080_, v_fst_1085_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(v_n_1077_, v_snd_1086_, v_lo_1079_, v_fst_1085_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_fst_1085_, v___x_1089_);
lean_dec(v_fst_1085_);
v_as_1078_ = v___x_1088_;
v_lo_1079_ = v___x_1090_;
goto _start;
}
else
{
lean_dec(v_fst_1085_);
lean_dec(v_lo_1079_);
return v_snd_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg___boxed(lean_object* v_n_1112_, lean_object* v_as_1113_, lean_object* v_lo_1114_, lean_object* v_hi_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(v_n_1112_, v_as_1113_, v_lo_1114_, v_hi_1115_);
lean_dec(v_hi_1115_);
lean_dec(v_n_1112_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31(lean_object* v_s_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_putStr_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_get_stderr();
v_putStr_1120_ = lean_ctor_get(v___x_1119_, 4);
lean_inc_ref(v_putStr_1120_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = lean_apply_2(v_putStr_1120_, v_s_1117_, lean_box(0));
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31___boxed(lean_object* v_s_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31(v_s_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_s_1125_){
_start:
{
uint32_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = 10;
v___x_1128_ = lean_string_push(v_s_1125_, v___x_1127_);
v___x_1129_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19_spec__31(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_s_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_s_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_bs_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1136_ == 0)
{
return v_bs_1135_;
}
else
{
lean_object* v_v_1137_; lean_object* v___x_1138_; lean_object* v_bs_x27_1139_; lean_object* v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v_v_1137_ = lean_array_uget(v_bs_1135_, v_i_1134_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v_bs_x27_1139_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1138_);
v___x_1140_ = l_String_Slice_toString(v_v_1137_);
lean_dec(v_v_1137_);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1134_, v___x_1141_);
v___x_1143_ = lean_array_uset(v_bs_x27_1139_, v_i_1134_, v___x_1140_);
v_i_1134_ = v___x_1142_;
v_bs_1135_ = v___x_1143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_sz_1145_, lean_object* v_i_1146_, lean_object* v_bs_1147_){
_start:
{
size_t v_sz_boxed_1148_; size_t v_i_boxed_1149_; lean_object* v_res_1150_; 
v_sz_boxed_1148_ = lean_unbox_usize(v_sz_1145_);
lean_dec(v_sz_1145_);
v_i_boxed_1149_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_sz_boxed_1148_, v_i_boxed_1149_, v_bs_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v_a_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_){
_start:
{
lean_object* v_it_1157_; lean_object* v_startInclusive_1158_; lean_object* v_endExclusive_1159_; 
if (lean_obj_tag(v_a_1154_) == 0)
{
lean_object* v_currPos_1163_; lean_object* v_searcher_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1190_; 
v_currPos_1163_ = lean_ctor_get(v_a_1154_, 0);
v_searcher_1164_ = lean_ctor_get(v_a_1154_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_a_1154_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1166_ = v_a_1154_;
v_isShared_1167_ = v_isSharedCheck_1190_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_searcher_1164_);
lean_inc(v_currPos_1163_);
lean_dec(v_a_1154_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1190_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_startInclusive_1168_; lean_object* v_endExclusive_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_startInclusive_1168_ = lean_ctor_get(v___x_1152_, 1);
v_endExclusive_1169_ = lean_ctor_get(v___x_1152_, 2);
v___x_1170_ = lean_nat_sub(v_endExclusive_1169_, v_startInclusive_1168_);
v___x_1171_ = lean_nat_dec_eq(v_searcher_1164_, v___x_1170_);
lean_dec(v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = 10;
v___x_1173_ = lean_string_utf8_get_fast(v_a_1151_, v_searcher_1164_);
v___x_1174_ = lean_uint32_dec_eq(v___x_1173_, v___x_1172_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_string_utf8_next_fast(v_a_1151_, v_searcher_1164_);
lean_dec(v_searcher_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1175_);
v___x_1177_ = v___x_1166_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_currPos_1163_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
v_a_1154_ = v___x_1177_;
goto _start;
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_slice_1183_; lean_object* v_nextIt_1185_; 
v___x_1180_ = lean_string_utf8_next_fast(v_a_1151_, v_searcher_1164_);
v___x_1181_ = lean_nat_sub(v___x_1180_, v_searcher_1164_);
v___x_1182_ = lean_nat_add(v_searcher_1164_, v___x_1181_);
lean_dec(v___x_1181_);
v_slice_1183_ = l_String_Slice_subslice_x21(v___x_1152_, v_currPos_1163_, v_searcher_1164_);
lean_inc(v___x_1182_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1182_);
lean_ctor_set(v___x_1166_, 0, v___x_1182_);
v_nextIt_1185_ = v___x_1166_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1182_);
v_nextIt_1185_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v_startInclusive_1186_; lean_object* v_endExclusive_1187_; 
v_startInclusive_1186_ = lean_ctor_get(v_slice_1183_, 0);
lean_inc(v_startInclusive_1186_);
v_endExclusive_1187_ = lean_ctor_get(v_slice_1183_, 1);
lean_inc(v_endExclusive_1187_);
lean_dec_ref(v_slice_1183_);
v_it_1157_ = v_nextIt_1185_;
v_startInclusive_1158_ = v_startInclusive_1186_;
v_endExclusive_1159_ = v_endExclusive_1187_;
goto v___jp_1156_;
}
}
}
else
{
lean_object* v___x_1189_; 
lean_del_object(v___x_1166_);
lean_dec(v_searcher_1164_);
v___x_1189_ = lean_box(1);
lean_inc(v___x_1153_);
v_it_1157_ = v___x_1189_;
v_startInclusive_1158_ = v_currPos_1163_;
v_endExclusive_1159_ = v___x_1153_;
goto v___jp_1156_;
}
}
}
else
{
lean_dec(v___x_1153_);
lean_dec_ref(v_a_1151_);
return v_b_1155_;
}
v___jp_1156_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_inc_ref(v_a_1151_);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v_a_1151_);
lean_ctor_set(v___x_1160_, 1, v_startInclusive_1158_);
lean_ctor_set(v___x_1160_, 2, v_endExclusive_1159_);
v___x_1161_ = lean_array_push(v_b_1155_, v___x_1160_);
v_a_1154_ = v_it_1157_;
v_b_1155_ = v___x_1161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v_a_1191_, lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_a_1191_, v___x_1192_, v___x_1193_, v_a_1194_, v_b_1195_);
lean_dec_ref(v___x_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg(lean_object* v_hi_1197_, lean_object* v_pivot_1198_, lean_object* v_as_1199_, lean_object* v_i_1200_, lean_object* v_k_1201_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_nat_dec_lt(v_k_1201_, v_hi_1197_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v_k_1201_);
lean_dec(v_pivot_1198_);
v___x_1203_ = lean_array_fswap(v_as_1199_, v_i_1200_, v_hi_1197_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_i_1200_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1205_ = lean_array_fget_borrowed(v_as_1199_, v_k_1201_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1205_, v___x_1202_);
lean_inc(v_pivot_1198_);
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_1198_, v___x_1202_);
v___x_1208_ = lean_string_dec_lt(v___x_1206_, v___x_1207_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_k_1201_, v___x_1209_);
lean_dec(v_k_1201_);
v_k_1201_ = v___x_1210_;
goto _start;
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_array_fswap(v_as_1199_, v_i_1200_, v_k_1201_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_add(v_i_1200_, v___x_1213_);
lean_dec(v_i_1200_);
v___x_1215_ = lean_nat_add(v_k_1201_, v___x_1213_);
lean_dec(v_k_1201_);
v_as_1199_ = v___x_1212_;
v_i_1200_ = v___x_1214_;
v_k_1201_ = v___x_1215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg___boxed(lean_object* v_hi_1217_, lean_object* v_pivot_1218_, lean_object* v_as_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg(v_hi_1217_, v_pivot_1218_, v_as_1219_, v_i_1220_, v_k_1221_);
lean_dec(v_hi_1217_);
return v_res_1222_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(uint8_t v___x_1223_, lean_object* v_a_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1224_, v___x_1223_);
v___x_1227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_1225_, v___x_1223_);
v___x_1228_ = lean_string_dec_lt(v___x_1226_, v___x_1227_);
lean_dec_ref(v___x_1227_);
lean_dec_ref(v___x_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0___boxed(lean_object* v___x_1229_, lean_object* v_a_1230_, lean_object* v_b_1231_){
_start:
{
uint8_t v___x_13699__boxed_1232_; uint8_t v_res_1233_; lean_object* v_r_1234_; 
v___x_13699__boxed_1232_ = lean_unbox(v___x_1229_);
v_res_1233_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(v___x_13699__boxed_1232_, v_a_1230_, v_b_1231_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(lean_object* v_n_1235_, lean_object* v_as_1236_, lean_object* v_lo_1237_, lean_object* v_hi_1238_){
_start:
{
lean_object* v___y_1240_; uint8_t v___x_1250_; 
v___x_1250_ = lean_nat_dec_lt(v_lo_1237_, v_hi_1238_);
if (v___x_1250_ == 0)
{
lean_dec(v_lo_1237_);
return v_as_1236_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_mid_1253_; lean_object* v___y_1255_; lean_object* v___y_1261_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1251_ = lean_nat_add(v_lo_1237_, v_hi_1238_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v_mid_1253_ = lean_nat_shiftr(v___x_1251_, v___x_1252_);
lean_dec(v___x_1251_);
v___x_1266_ = lean_array_fget_borrowed(v_as_1236_, v_mid_1253_);
v___x_1267_ = lean_array_fget_borrowed(v_as_1236_, v_lo_1237_);
lean_inc(v___x_1267_);
lean_inc(v___x_1266_);
v___x_1268_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(v___x_1250_, v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
v___y_1261_ = v_as_1236_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_array_fswap(v_as_1236_, v_lo_1237_, v_mid_1253_);
v___y_1261_ = v___x_1269_;
goto v___jp_1260_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_array_fget_borrowed(v___y_1255_, v_mid_1253_);
v___x_1257_ = lean_array_fget_borrowed(v___y_1255_, v_hi_1238_);
lean_inc(v___x_1257_);
lean_inc(v___x_1256_);
v___x_1258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(v___x_1250_, v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_dec(v_mid_1253_);
v___y_1240_ = v___y_1255_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_array_fswap(v___y_1255_, v_mid_1253_, v_hi_1238_);
lean_dec(v_mid_1253_);
v___y_1240_ = v___x_1259_;
goto v___jp_1239_;
}
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_array_fget_borrowed(v___y_1261_, v_hi_1238_);
v___x_1263_ = lean_array_fget_borrowed(v___y_1261_, v_lo_1237_);
lean_inc(v___x_1263_);
lean_inc(v___x_1262_);
v___x_1264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___lam__0(v___x_1250_, v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1255_ = v___y_1261_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_array_fswap(v___y_1261_, v_lo_1237_, v_hi_1238_);
v___y_1255_ = v___x_1265_;
goto v___jp_1254_;
}
}
}
v___jp_1239_:
{
lean_object* v_pivot_1241_; lean_object* v___x_1242_; lean_object* v_fst_1243_; lean_object* v_snd_1244_; uint8_t v___x_1245_; 
v_pivot_1241_ = lean_array_fget(v___y_1240_, v_hi_1238_);
lean_inc_n(v_lo_1237_, 2);
v___x_1242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg(v_hi_1238_, v_pivot_1241_, v___y_1240_, v_lo_1237_, v_lo_1237_);
v_fst_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_fst_1243_);
v_snd_1244_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_snd_1244_);
lean_dec_ref(v___x_1242_);
v___x_1245_ = lean_nat_dec_le(v_hi_1238_, v_fst_1243_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(v_n_1235_, v_snd_1244_, v_lo_1237_, v_fst_1243_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_fst_1243_, v___x_1247_);
lean_dec(v_fst_1243_);
v_as_1236_ = v___x_1246_;
v_lo_1237_ = v___x_1248_;
goto _start;
}
else
{
lean_dec(v_fst_1243_);
lean_dec(v_lo_1237_);
return v_snd_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg___boxed(lean_object* v_n_1270_, lean_object* v_as_1271_, lean_object* v_lo_1272_, lean_object* v_hi_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(v_n_1270_, v_as_1271_, v_lo_1272_, v_hi_1273_);
lean_dec(v_hi_1273_);
lean_dec(v_n_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v___x_1277_, size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_bs_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v___x_1277_);
return v_bs_1280_;
}
else
{
lean_object* v_v_1282_; lean_object* v___x_1283_; lean_object* v_bs_x27_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v_v_1282_ = lean_array_uget(v_bs_1280_, v_i_1279_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v_bs_x27_1284_ = lean_array_uset(v_bs_1280_, v_i_1279_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__0));
lean_inc_ref(v___x_1277_);
v___x_1286_ = lean_string_append(v___x_1277_, v___x_1285_);
v___x_1287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1282_, v___x_1281_);
v___x_1288_ = lean_string_append(v___x_1286_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___closed__1));
v___x_1290_ = lean_string_append(v___x_1288_, v___x_1289_);
v___x_1291_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1279_, v___x_1293_);
v___x_1295_ = lean_array_uset(v_bs_x27_1284_, v_i_1279_, v___x_1292_);
v_i_1279_ = v___x_1294_;
v_bs_1280_ = v___x_1295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v___x_1297_, lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v___x_1297_, v_sz_boxed_1301_, v_i_boxed_1302_, v_bs_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_1304_, size_t v_sz_1305_, size_t v_i_1306_, lean_object* v_b_1307_){
_start:
{
lean_object* v_a_1310_; uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1306_, v_sz_1305_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_b_1307_);
return v___x_1315_;
}
else
{
lean_object* v_a_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1359_; 
v_a_1316_ = lean_array_uget_borrowed(v_as_1304_, v_i_1306_);
v_fst_1317_ = lean_ctor_get(v_a_1316_, 0);
v_snd_1318_ = lean_ctor_get(v_a_1316_, 1);
v_fst_1319_ = lean_ctor_get(v_b_1307_, 0);
v_snd_1320_ = lean_ctor_get(v_b_1307_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_b_1307_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1322_ = v_b_1307_;
v_isShared_1323_ = v_isSharedCheck_1359_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_inc(v_fst_1319_);
lean_dec(v_b_1307_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1359_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_nat_sub(v_fst_1317_, v___x_1324_);
v___x_1326_ = lean_array_get_size(v_fst_1319_);
v___x_1327_ = lean_nat_dec_lt(v___x_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v___x_1325_);
if (v_isShared_1323_ == 0)
{
v___x_1329_ = v___x_1322_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_snd_1320_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v_a_1310_ = v___x_1329_;
goto v___jp_1309_;
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___y_1335_; lean_object* v___x_1348_; lean_object* v___y_1350_; lean_object* v___y_1351_; uint8_t v___x_1353_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_array_fget_borrowed(v_fst_1319_, v___x_1325_);
v___x_1333_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1332_);
v___x_1348_ = lean_array_get_size(v_snd_1318_);
v___x_1353_ = lean_nat_dec_eq(v___x_1348_, v___x_1331_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___y_1356_; uint8_t v___x_1358_; 
v___x_1354_ = lean_nat_sub(v___x_1348_, v___x_1324_);
v___x_1358_ = lean_nat_dec_le(v___x_1331_, v___x_1354_);
if (v___x_1358_ == 0)
{
lean_inc(v___x_1354_);
v___y_1356_ = v___x_1354_;
goto v___jp_1355_;
}
else
{
v___y_1356_ = v___x_1331_;
goto v___jp_1355_;
}
v___jp_1355_:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_le(v___y_1356_, v___x_1354_);
if (v___x_1357_ == 0)
{
lean_dec(v___x_1354_);
lean_inc(v___y_1356_);
v___y_1350_ = v___y_1356_;
v___y_1351_ = v___y_1356_;
goto v___jp_1349_;
}
else
{
v___y_1350_ = v___y_1356_;
v___y_1351_ = v___x_1354_;
goto v___jp_1349_;
}
}
}
else
{
lean_inc(v_snd_1318_);
v___y_1335_ = v_snd_1318_;
goto v___jp_1334_;
}
v___jp_1334_:
{
size_t v_sz_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_sz_1336_ = lean_array_size(v___y_1335_);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v___x_1333_, v_sz_1336_, v___x_1337_, v___y_1335_);
lean_inc(v___x_1325_);
v___x_1339_ = l_Array_extract___redArg(v_fst_1319_, v___x_1331_, v___x_1325_);
v___x_1340_ = l_Array_append___redArg(v___x_1339_, v___x_1338_);
v___x_1341_ = l_Array_extract___redArg(v_fst_1319_, v___x_1325_, v___x_1326_);
lean_dec(v_fst_1319_);
v___x_1342_ = l_Array_append___redArg(v___x_1340_, v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_array_get_size(v___x_1338_);
lean_dec_ref(v___x_1338_);
v___x_1344_ = lean_nat_add(v_snd_1320_, v___x_1343_);
lean_dec(v_snd_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1344_);
lean_ctor_set(v___x_1322_, 0, v___x_1342_);
v___x_1346_ = v___x_1322_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v_a_1310_ = v___x_1346_;
goto v___jp_1309_;
}
}
v___jp_1349_:
{
lean_object* v___x_1352_; 
lean_inc(v_snd_1318_);
v___x_1352_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(v___x_1348_, v_snd_1318_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
v___y_1335_ = v___x_1352_;
goto v___jp_1334_;
}
}
}
}
v___jp_1309_:
{
size_t v___x_1311_; size_t v___x_1312_; 
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1306_, v___x_1311_);
v_i_1306_ = v___x_1312_;
v_b_1307_ = v_a_1310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_){
_start:
{
size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_1360_, v_sz_boxed_1365_, v_i_boxed_1366_, v_b_1363_);
lean_dec_ref(v_as_1360_);
return v_res_1367_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0(void){
_start:
{
lean_object* v_cellCount_1368_; lean_object* v___x_1369_; 
v_cellCount_1368_ = lean_unsigned_to_nat(16u);
v___x_1369_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1(void){
_start:
{
lean_object* v_cellCount_1370_; lean_object* v___x_1371_; 
v_cellCount_1370_ = lean_unsigned_to_nat(16u);
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__1);
v___x_1373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__0);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
lean_ctor_set(v___x_1375_, 2, v___x_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_1386_, size_t v_sz_1387_, size_t v_i_1388_, lean_object* v_b_1389_){
_start:
{
lean_object* v_a_1392_; uint8_t v___x_1396_; 
v___x_1396_ = lean_usize_dec_lt(v_i_1388_, v_sz_1387_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1389_);
return v___x_1397_;
}
else
{
lean_object* v_a_1398_; lean_object* v_snd_1399_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1494_; 
v_a_1398_ = lean_array_uget_borrowed(v_as_1386_, v_i_1388_);
v_snd_1399_ = lean_ctor_get(v_a_1398_, 1);
lean_inc(v_snd_1399_);
v_fst_1400_ = lean_ctor_get(v_snd_1399_, 0);
v_snd_1401_ = lean_ctor_get(v_snd_1399_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_snd_1399_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1403_ = v_snd_1399_;
v_isShared_1404_ = v_isSharedCheck_1494_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1401_);
lean_inc(v_fst_1400_);
lean_dec(v_snd_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1494_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__2);
v_sz_1407_ = lean_array_size(v_snd_1401_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_snd_1401_, v_sz_1407_, v___x_1408_, v___x_1406_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___x_1425_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = lean_box(0);
v___x_1425_ = l_IO_FS_readFile(v_fst_1400_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_size_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___y_1439_; lean_object* v___x_1465_; lean_object* v___y_1467_; lean_object* v___y_1468_; uint8_t v___x_1470_; 
lean_dec(v_snd_1401_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc_n(v_a_1426_, 2);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = lean_string_utf8_byte_size(v_a_1426_);
v___x_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1405_);
lean_ctor_set(v___x_1428_, 2, v___x_1427_);
v___x_1429_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1428_);
v_size_1430_ = lean_ctor_get(v_a_1410_, 0);
v___x_1431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__5));
v___x_1432_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_a_1426_, v___x_1428_, v___x_1427_, v___x_1429_, v___x_1431_);
lean_dec_ref_known(v___x_1428_, 3);
v_sz_1433_ = lean_array_size(v___x_1432_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_sz_1433_, v___x_1408_, v___x_1432_);
v___x_1435_ = lean_mk_empty_array_with_capacity(v_size_1430_);
v___x_1436_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1435_, v_a_1410_);
lean_dec(v_a_1410_);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_array_get_size(v___x_1436_);
v___x_1470_ = lean_nat_dec_eq(v___x_1465_, v___x_1405_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___y_1473_; uint8_t v___x_1475_; 
v___x_1471_ = lean_nat_sub(v___x_1465_, v___x_1437_);
v___x_1475_ = lean_nat_dec_le(v___x_1405_, v___x_1471_);
if (v___x_1475_ == 0)
{
lean_inc(v___x_1471_);
v___y_1473_ = v___x_1471_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v___x_1405_;
goto v___jp_1472_;
}
v___jp_1472_:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_nat_dec_le(v___y_1473_, v___x_1471_);
if (v___x_1474_ == 0)
{
lean_dec(v___x_1471_);
lean_inc(v___y_1473_);
v___y_1467_ = v___y_1473_;
v___y_1468_ = v___y_1473_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___y_1473_;
v___y_1468_ = v___x_1471_;
goto v___jp_1466_;
}
}
}
else
{
v___y_1439_ = v___x_1436_;
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1405_);
lean_ctor_set(v___x_1403_, 0, v___x_1434_);
v___x_1441_ = v___x_1403_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1405_);
v___x_1441_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
size_t v_sz_1442_; lean_object* v___x_1443_; 
v_sz_1442_ = lean_array_size(v___y_1439_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v___y_1439_, v_sz_1442_, v___x_1408_, v___x_1441_);
lean_dec_ref(v___y_1439_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v_fst_1445_; lean_object* v_snd_1446_; uint8_t v___x_1447_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v_fst_1445_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_fst_1445_);
v_snd_1446_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_a_1444_);
v___x_1447_ = lean_nat_dec_lt(v___x_1405_, v_snd_1446_);
if (v___x_1447_ == 0)
{
lean_dec(v_snd_1446_);
lean_dec(v_fst_1445_);
lean_dec(v_fst_1400_);
v_a_1392_ = v___x_1411_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__6));
lean_inc(v_snd_1446_);
v___x_1449_ = l_Nat_reprFast(v_snd_1446_);
v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__7));
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
v___x_1453_ = lean_nat_dec_eq(v_snd_1446_, v___x_1437_);
lean_dec(v_snd_1446_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__8));
v___y_1413_ = v_fst_1445_;
v___y_1414_ = v___x_1452_;
v___y_1415_ = v___x_1454_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1413_ = v_fst_1445_;
v___y_1414_ = v___x_1452_;
v___y_1415_ = v___x_1455_;
goto v___jp_1412_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_fst_1400_);
v_a_1456_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1443_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1443_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
v___jp_1466_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(v___x_1465_, v___x_1436_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
v___y_1439_ = v___x_1469_;
goto v___jp_1438_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref_known(v___x_1425_, 1);
lean_dec(v_a_1410_);
lean_del_object(v___x_1403_);
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__9));
v___x_1477_ = lean_string_append(v___x_1476_, v_fst_1400_);
lean_dec(v_fst_1400_);
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__10));
v___x_1479_ = lean_string_append(v___x_1477_, v___x_1478_);
v___x_1480_ = lean_array_get_size(v_snd_1401_);
lean_dec(v_snd_1401_);
v___x_1481_ = l_Nat_reprFast(v___x_1480_);
v___x_1482_ = lean_string_append(v___x_1479_, v___x_1481_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__11));
v___x_1484_ = lean_string_append(v___x_1482_, v___x_1483_);
v___x_1485_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v_a_1392_ = v___x_1411_;
goto v___jp_1391_;
}
else
{
return v___x_1485_;
}
}
v___jp_1412_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1416_ = lean_string_append(v___y_1414_, v___y_1415_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__3));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1418_, v_fst_1400_);
v___x_1420_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1419_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref_known(v___x_1420_, 1);
v___x_1421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___closed__4));
v___x_1422_ = lean_array_to_list(v___y_1413_);
v___x_1423_ = l_String_intercalate(v___x_1421_, v___x_1422_);
v___x_1424_ = l_IO_FS_writeFile(v_fst_1400_, v___x_1423_);
lean_dec_ref(v___x_1423_);
lean_dec(v_fst_1400_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_dec_ref_known(v___x_1424_, 1);
v_a_1392_ = v___x_1411_;
goto v___jp_1391_;
}
else
{
return v___x_1424_;
}
}
else
{
lean_dec(v___y_1413_);
lean_dec(v_fst_1400_);
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_del_object(v___x_1403_);
lean_dec(v_snd_1401_);
lean_dec(v_fst_1400_);
v_a_1486_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1409_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1409_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
v___jp_1391_:
{
size_t v___x_1393_; size_t v___x_1394_; 
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1388_, v___x_1393_);
v_i_1388_ = v___x_1394_;
v_b_1389_ = v_a_1392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_1495_, lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_){
_start:
{
size_t v_sz_boxed_1500_; size_t v_i_boxed_1501_; lean_object* v_res_1502_; 
v_sz_boxed_1500_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1501_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_1495_, v_sz_boxed_1500_, v_i_boxed_1501_, v_b_1498_);
lean_dec_ref(v_as_1495_);
return v_res_1502_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v_cellCount_1503_; lean_object* v___x_1504_; 
v_cellCount_1503_ = lean_unsigned_to_nat(16u);
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v_cellCount_1505_; lean_object* v___x_1506_; 
v_cellCount_1505_ = lean_unsigned_to_nat(16u);
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_byFile_1510_; 
v___x_1507_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v___x_1508_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1509_ = lean_unsigned_to_nat(0u);
v_byFile_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_byFile_1510_, 0, v___x_1509_);
lean_ctor_set(v_byFile_1510_, 1, v___x_1508_);
lean_ctor_set(v_byFile_1510_, 2, v___x_1507_);
return v_byFile_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1511_){
_start:
{
lean_object* v_byFile_1513_; size_t v_sz_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v_byFile_1513_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__2);
v_sz_1514_ = lean_array_size(v_records_1511_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_records_1511_, v_sz_1514_, v___x_1515_, v_byFile_1513_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_size_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; size_t v_sz_1522_; lean_object* v___x_1523_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v_size_1518_ = lean_ctor_get(v_a_1517_, 0);
v___x_1519_ = lean_mk_empty_array_with_capacity(v_size_1518_);
v___x_1520_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_1519_, v_a_1517_);
lean_dec(v_a_1517_);
v___x_1521_ = lean_box(0);
v_sz_1522_ = lean_array_size(v___x_1520_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v___x_1520_, v_sz_1522_, v___x_1515_, v___x_1521_);
lean_dec_ref(v___x_1520_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1531_);
v___x_1525_ = v___x_1523_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1521_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1521_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
return v___x_1523_;
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1532_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1516_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1516_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1540_);
lean_dec_ref(v_records_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1543_, lean_object* v_m_1544_, lean_object* v_a_1545_, lean_object* v_fallback_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1544_, v_a_1545_, v_fallback_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_, lean_object* v_fallback_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1548_, v_m_1549_, v_a_1550_, v_fallback_1551_);
lean_dec(v_fallback_1551_);
lean_dec_ref(v_a_1550_);
lean_dec_ref(v_m_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_query_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1554_, v_query_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___boxed(lean_object* v_00_u03b2_1557_, lean_object* v_m_1558_, lean_object* v_query_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(v_00_u03b2_1557_, v_m_1558_, v_query_1559_);
lean_dec_ref(v_query_1559_);
lean_dec_ref(v_m_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_00_u03b2_1561_, lean_object* v_m_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___redArg(v_m_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_00_u03b2_1564_, lean_object* v_m_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_00_u03b2_1564_, v_m_1565_);
lean_dec_ref(v_m_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_a_1569_, lean_object* v_fallback_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1568_, v_a_1569_, v_fallback_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___boxed(lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_a_1574_, lean_object* v_fallback_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(v_00_u03b2_1572_, v_m_1573_, v_a_1574_, v_fallback_1575_);
lean_dec(v_fallback_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_m_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, lean_object* v_query_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(v_m_1578_, v_query_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_00_u03b2_1581_, lean_object* v_m_1582_, lean_object* v_query_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_00_u03b2_1581_, v_m_1582_, v_query_1583_);
lean_dec(v_query_1583_);
lean_dec_ref(v_m_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_00_u03b2_1585_, lean_object* v_m_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_m_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_00_u03b2_1588_, lean_object* v_m_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_00_u03b2_1588_, v_m_1589_);
lean_dec_ref(v_m_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v_a_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_inst_1594_, lean_object* v_R_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_a_1591_, v___x_1592_, v___x_1593_, v_a_1596_, v_b_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v_a_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_inst_1602_, lean_object* v_R_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v_a_1599_, v___x_1600_, v___x_1601_, v_inst_1602_, v_R_1603_, v_a_1604_, v_b_1605_);
lean_dec_ref(v___x_1600_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_n_1607_, lean_object* v_as_1608_, lean_object* v_lo_1609_, lean_object* v_hi_1610_, lean_object* v_w_1611_, lean_object* v_hlo_1612_, lean_object* v_hhi_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___redArg(v_n_1607_, v_as_1608_, v_lo_1609_, v_hi_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_n_1615_, lean_object* v_as_1616_, lean_object* v_lo_1617_, lean_object* v_hi_1618_, lean_object* v_w_1619_, lean_object* v_hlo_1620_, lean_object* v_hhi_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_n_1615_, v_as_1616_, v_lo_1617_, v_hi_1618_, v_w_1619_, v_hlo_1620_, v_hhi_1621_);
lean_dec(v_hi_1618_);
lean_dec(v_n_1615_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_, lean_object* v_w_1627_, lean_object* v_hlo_1628_, lean_object* v_hhi_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___redArg(v_n_1623_, v_as_1624_, v_lo_1625_, v_hi_1626_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_n_1631_, lean_object* v_as_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_, lean_object* v_w_1635_, lean_object* v_hlo_1636_, lean_object* v_hhi_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_n_1631_, v_as_1632_, v_lo_1633_, v_hi_1634_, v_w_1635_, v_hlo_1636_, v_hhi_1637_);
lean_dec(v_hi_1634_);
lean_dec(v_n_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_m_1640_, v_a_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_m_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1643_, v_m_1644_, v_a_1645_);
lean_dec_ref(v_a_1645_);
lean_dec_ref(v_m_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1647_, lean_object* v_m_1648_, lean_object* v_query_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_m_1648_, v_query_1649_, v_x_1650_, v_x_1651_, v_x_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_m_1656_, lean_object* v_query_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1655_, v_m_1656_, v_query_1657_, v_x_1658_, v_x_1659_, v_x_1660_, v_x_1661_);
lean_dec_ref(v_query_1657_);
lean_dec_ref(v_m_1656_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4(lean_object* v_00_u03b2_1663_, lean_object* v_init_1664_, lean_object* v_b_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___redArg(v_init_1664_, v_b_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1667_, lean_object* v_init_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4(v_00_u03b2_1667_, v_init_1668_, v_b_1669_);
lean_dec_ref(v_b_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9(lean_object* v_00_u03b2_1671_, lean_object* v_m_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___redArg(v_m_1672_, v_a_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1675_, lean_object* v_m_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9(v_00_u03b2_1675_, v_m_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_m_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13(lean_object* v_00_u03b2_1679_, lean_object* v_m_1680_, lean_object* v_query_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___redArg(v_m_1680_, v_query_1681_, v_x_1682_, v_x_1683_, v_x_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13___boxed(lean_object* v_00_u03b2_1687_, lean_object* v_m_1688_, lean_object* v_query_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7_spec__13(v_00_u03b2_1687_, v_m_1688_, v_query_1689_, v_x_1690_, v_x_1691_, v_x_1692_, v_x_1693_);
lean_dec(v_query_1689_);
lean_dec_ref(v_m_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15(lean_object* v_00_u03b2_1695_, lean_object* v_init_1696_, lean_object* v_b_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___redArg(v_init_1696_, v_b_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15___boxed(lean_object* v_00_u03b2_1699_, lean_object* v_init_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15(v_00_u03b2_1699_, v_init_1700_, v_b_1701_);
lean_dec_ref(v_b_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24(lean_object* v_n_1703_, lean_object* v_lo_1704_, lean_object* v_hi_1705_, lean_object* v_hhi_1706_, lean_object* v_pivot_1707_, lean_object* v_as_1708_, lean_object* v_i_1709_, lean_object* v_k_1710_, lean_object* v_ilo_1711_, lean_object* v_ik_1712_, lean_object* v_w_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___redArg(v_hi_1705_, v_pivot_1707_, v_as_1708_, v_i_1709_, v_k_1710_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24___boxed(lean_object* v_n_1715_, lean_object* v_lo_1716_, lean_object* v_hi_1717_, lean_object* v_hhi_1718_, lean_object* v_pivot_1719_, lean_object* v_as_1720_, lean_object* v_i_1721_, lean_object* v_k_1722_, lean_object* v_ilo_1723_, lean_object* v_ik_1724_, lean_object* v_w_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15_spec__24(v_n_1715_, v_lo_1716_, v_hi_1717_, v_hhi_1718_, v_pivot_1719_, v_as_1720_, v_i_1721_, v_k_1722_, v_ilo_1723_, v_ik_1724_, v_w_1725_);
lean_dec(v_hi_1717_);
lean_dec(v_lo_1716_);
lean_dec(v_n_1715_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29(lean_object* v_n_1727_, lean_object* v_lo_1728_, lean_object* v_hi_1729_, lean_object* v_hhi_1730_, lean_object* v_pivot_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_k_1734_, lean_object* v_ilo_1735_, lean_object* v_ik_1736_, lean_object* v_w_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___redArg(v_hi_1729_, v_pivot_1731_, v_as_1732_, v_i_1733_, v_k_1734_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29___boxed(lean_object* v_n_1739_, lean_object* v_lo_1740_, lean_object* v_hi_1741_, lean_object* v_hhi_1742_, lean_object* v_pivot_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_k_1746_, lean_object* v_ilo_1747_, lean_object* v_ik_1748_, lean_object* v_w_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18_spec__29(v_n_1739_, v_lo_1740_, v_hi_1741_, v_hhi_1742_, v_pivot_1743_, v_as_1744_, v_i_1745_, v_k_1746_, v_ilo_1747_, v_ik_1748_, v_w_1749_);
lean_dec_ref(v_pivot_1743_);
lean_dec(v_hi_1741_);
lean_dec(v_lo_1740_);
lean_dec(v_n_1739_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_query_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___redArg(v_m_1752_, v_query_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_query_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0_spec__2(v_00_u03b2_1755_, v_m_1756_, v_query_1757_);
lean_dec_ref(v_query_1757_);
lean_dec_ref(v_m_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1759_, lean_object* v_b_1760_, lean_object* v_acc_1761_, lean_object* v_i_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___redArg(v_b_1760_, v_acc_1761_, v_i_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1764_, lean_object* v_b_1765_, lean_object* v_acc_1766_, lean_object* v_i_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2_spec__4_spec__7(v_00_u03b2_1764_, v_b_1765_, v_acc_1766_, v_i_1767_);
lean_dec_ref(v_b_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1769_, lean_object* v_m_1770_, lean_object* v_query_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___redArg(v_m_1770_, v_query_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1773_, lean_object* v_m_1774_, lean_object* v_query_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__9_spec__13(v_00_u03b2_1773_, v_m_1774_, v_query_1775_);
lean_dec(v_query_1775_);
lean_dec_ref(v_m_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20(lean_object* v_00_u03b2_1777_, lean_object* v_b_1778_, lean_object* v_acc_1779_, lean_object* v_i_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___redArg(v_b_1778_, v_acc_1779_, v_i_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1782_, lean_object* v_b_1783_, lean_object* v_acc_1784_, lean_object* v_i_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8_spec__15_spec__20(v_00_u03b2_1782_, v_b_1783_, v_acc_1784_, v_i_1785_);
lean_dec_ref(v_b_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v___x_1792_; lean_object* v_env_1793_; lean_object* v___x_1794_; lean_object* v_toEnvExtension_1795_; lean_object* v_asyncMode_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1790_ = lean_st_ref_get(v___y_1788_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = lean_st_ref_get(v___y_1788_);
v_env_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc_ref(v_env_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Lean_declRangeExt;
v_toEnvExtension_1795_ = lean_ctor_get(v___x_1794_, 0);
v_asyncMode_1796_ = lean_ctor_get(v_toEnvExtension_1795_, 2);
v___x_1797_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1798_ = 0;
lean_inc(v_declName_1787_);
v___x_1799_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1797_, v___x_1794_, v_env_1791_, v_declName_1787_, v_asyncMode_1796_, v___x_1798_);
if (lean_obj_tag(v___x_1799_) == 0)
{
uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = 1;
v___x_1801_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1797_, v___x_1794_, v_env_1793_, v_declName_1787_, v_asyncMode_1796_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; 
lean_dec_ref(v_env_1793_);
lean_dec(v_declName_1787_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1799_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1804_, v___y_1805_);
lean_dec(v___y_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v_env_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1811_ = lean_st_ref_get(v___y_1809_);
v_env_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc_ref(v_env_1812_);
lean_dec(v___x_1811_);
v___x_1813_ = l_Lean_isRecCore(v_env_1812_, v_declName_1808_);
v___x_1814_ = lean_box(v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1816_, v___y_1817_);
lean_dec(v___y_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_ranges_1825_; lean_object* v___x_1831_; lean_object* v_env_1832_; lean_object* v___x_1833_; lean_object* v_a_1834_; uint8_t v___y_1840_; uint8_t v___x_1844_; 
v___x_1831_ = lean_st_ref_get(v___y_1822_);
v_env_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_ref_n(v_env_1832_, 2);
lean_dec(v___x_1831_);
lean_inc_n(v_declName_1820_, 2);
v___x_1833_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1820_, v___y_1822_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___x_1844_ = l_Lean_isAuxRecursor(v_env_1832_, v_declName_1820_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
lean_inc(v_declName_1820_);
v___x_1845_ = l_Lean_isNoConfusion(v_env_1832_, v_declName_1820_);
v___y_1840_ = v___x_1845_;
goto v___jp_1839_;
}
else
{
lean_dec_ref(v_env_1832_);
v___y_1840_ = v___x_1844_;
goto v___jp_1839_;
}
v___jp_1824_:
{
if (lean_obj_tag(v_ranges_1825_) == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1826_ = l_Lean_builtinDeclRanges;
v___x_1827_ = lean_st_ref_get(v___x_1826_);
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1827_, v_declName_1820_);
lean_dec(v_declName_1820_);
lean_dec(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_declName_1820_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_ranges_1825_);
return v___x_1830_;
}
}
v___jp_1835_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; 
v___x_1836_ = l_Lean_Name_getPrefix(v_declName_1820_);
v___x_1837_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1836_, v___y_1822_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v_ranges_1825_ = v_a_1838_;
goto v___jp_1824_;
}
v___jp_1839_:
{
if (v___y_1840_ == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_unbox(v_a_1834_);
lean_dec(v_a_1834_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v_a_1843_; 
lean_inc(v_declName_1820_);
v___x_1842_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1820_, v___y_1822_);
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1842_);
v_ranges_1825_ = v_a_1843_;
goto v___jp_1824_;
}
else
{
goto v___jp_1835_;
}
}
else
{
lean_dec(v_a_1834_);
goto v___jp_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1851_, lean_object* v_site_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
if (lean_obj_tag(v_site_1852_) == 0)
{
lean_object* v_name_1856_; lean_object* v___x_1857_; 
v_name_1856_ = lean_ctor_get(v_site_1852_, 0);
lean_inc(v_name_1856_);
lean_dec_ref_known(v_site_1852_, 1);
v___x_1857_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1856_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1879_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1879_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1879_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
if (lean_obj_tag(v_a_1858_) == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_box(0);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
else
{
lean_object* v_val_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1878_; 
v_val_1866_ = lean_ctor_get(v_a_1858_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1858_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1868_ = v_a_1858_;
v_isShared_1869_ = v_isSharedCheck_1878_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_val_1866_);
lean_dec(v_a_1858_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1878_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_range_1870_; lean_object* v_pos_1871_; lean_object* v___x_1873_; 
v_range_1870_ = lean_ctor_get(v_val_1866_, 0);
lean_inc_ref(v_range_1870_);
lean_dec(v_val_1866_);
v_pos_1871_ = lean_ctor_get(v_range_1870_, 0);
lean_inc_ref(v_pos_1871_);
lean_dec_ref(v_range_1870_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_pos_1871_);
v___x_1873_ = v___x_1868_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_pos_1871_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1873_);
v___x_1875_ = v___x_1860_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1857_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1857_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_n_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1919_; 
v_n_1888_ = lean_ctor_get(v_site_1852_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_site_1852_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1890_ = v_site_1852_;
v_isShared_1891_ = v_isSharedCheck_1919_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_n_1888_);
lean_dec(v_site_1852_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1919_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v_env_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_get(v_a_1854_);
v_env_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_ref(v_env_1893_);
lean_dec(v___x_1892_);
v___x_1894_ = l_Lean_getVersoModuleDoc_x3f(v_env_1893_, v_failMod_1851_);
lean_dec_ref(v_env_1893_);
if (lean_obj_tag(v___x_1894_) == 1)
{
lean_object* v_val_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1914_; 
v_val_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1914_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_val_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1914_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_val_1895_);
v___x_1900_ = lean_nat_dec_lt(v_n_1888_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_del_object(v___x_1897_);
lean_dec(v_val_1895_);
lean_dec(v_n_1888_);
v___x_1901_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1901_);
v___x_1903_ = v___x_1890_;
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
lean_object* v___x_1905_; lean_object* v_declarationRange_1906_; lean_object* v_pos_1907_; lean_object* v___x_1909_; 
v___x_1905_ = lean_array_fget(v_val_1895_, v_n_1888_);
lean_dec(v_n_1888_);
lean_dec(v_val_1895_);
v_declarationRange_1906_ = lean_ctor_get(v___x_1905_, 2);
lean_inc_ref(v_declarationRange_1906_);
lean_dec(v___x_1905_);
v_pos_1907_ = lean_ctor_get(v_declarationRange_1906_, 0);
lean_inc_ref(v_pos_1907_);
lean_dec_ref(v_declarationRange_1906_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v_pos_1907_);
v___x_1909_ = v___x_1897_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_pos_1907_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1909_);
v___x_1911_ = v___x_1890_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v___x_1894_);
lean_dec(v_n_1888_);
v___x_1915_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1915_);
v___x_1917_ = v___x_1890_;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1920_, lean_object* v_site_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1920_, v_site_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_failMod_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1926_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1936_, v___y_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v_name_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_name_1950_ = lean_ctor_get(v_x_1949_, 0);
lean_inc(v_name_1950_);
lean_dec_ref_known(v_x_1949_, 1);
v___x_1951_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1952_ = 1;
v___x_1953_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1950_, v___x_1952_);
v___x_1954_ = lean_string_append(v___x_1951_, v___x_1953_);
lean_dec_ref(v___x_1953_);
v___x_1955_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1956_ = lean_string_append(v___x_1954_, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v_n_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_n_1957_ = lean_ctor_get(v_x_1949_, 0);
lean_inc(v_n_1957_);
lean_dec_ref_known(v_x_1949_, 1);
v___x_1958_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_n_1957_, v___x_1959_);
lean_dec(v_n_1957_);
v___x_1961_ = l_Nat_reprFast(v___x_1960_);
v___x_1962_ = lean_string_append(v___x_1958_, v___x_1961_);
lean_dec_ref(v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v_env_1967_; lean_object* v___x_1968_; lean_object* v_toEnvExtension_1969_; lean_object* v_asyncMode_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_merged_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v___x_1966_ = lean_st_ref_get(v___y_1964_);
v_env_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc_ref(v_env_1967_);
lean_dec(v___x_1966_);
v___x_1968_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1969_ = lean_ctor_get(v___x_1968_, 0);
v_asyncMode_1970_ = lean_ctor_get(v_toEnvExtension_1969_, 2);
v___x_1971_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1972_ = lean_box(0);
v___x_1973_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1971_, v___x_1968_, v_env_1967_, v_asyncMode_1970_, v___x_1972_);
v_merged_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1973_, 1);
lean_dec(v_unused_1983_);
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_merged_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_merged_1974_);
lean_ctor_set(v___x_1976_, 0, v_o_1963_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_o_1963_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_merged_1974_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1984_, v___y_1985_);
lean_dec(v___y_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1988_, v___y_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1998_, lean_object* v_opt_1999_){
_start:
{
lean_object* v_name_2000_; lean_object* v_defValue_2001_; lean_object* v_map_2002_; lean_object* v___x_2003_; 
v_name_2000_ = lean_ctor_get(v_opt_1999_, 0);
v_defValue_2001_ = lean_ctor_get(v_opt_1999_, 1);
v_map_2002_ = lean_ctor_get(v_opts_1998_, 0);
v___x_2003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2002_, v_name_2000_);
if (lean_obj_tag(v___x_2003_) == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_unbox(v_defValue_2001_);
return v___x_2004_;
}
else
{
lean_object* v_val_2005_; 
v_val_2005_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_val_2005_);
lean_dec_ref_known(v___x_2003_, 1);
if (lean_obj_tag(v_val_2005_) == 1)
{
uint8_t v_v_2006_; 
v_v_2006_ = lean_ctor_get_uint8(v_val_2005_, 0);
lean_dec_ref_known(v_val_2005_, 0);
return v_v_2006_;
}
else
{
uint8_t v___x_2007_; 
lean_dec(v_val_2005_);
v___x_2007_ = lean_unbox(v_defValue_2001_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_2008_, lean_object* v_opt_2009_){
_start:
{
uint8_t v_res_2010_; lean_object* v_r_2011_; 
v_res_2010_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_2008_, v_opt_2009_);
lean_dec_ref(v_opt_2009_);
lean_dec_ref(v_opts_2008_);
v_r_2011_ = lean_box(v_res_2010_);
return v_r_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_2012_, lean_object* v_opt_2013_){
_start:
{
lean_object* v_name_2014_; lean_object* v_defValue_2015_; lean_object* v_map_2016_; lean_object* v___x_2017_; 
v_name_2014_ = lean_ctor_get(v_opt_2013_, 0);
v_defValue_2015_ = lean_ctor_get(v_opt_2013_, 1);
v_map_2016_ = lean_ctor_get(v_opts_2012_, 0);
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2016_, v_name_2014_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_inc(v_defValue_2015_);
return v_defValue_2015_;
}
else
{
lean_object* v_val_2018_; 
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v___x_2017_, 1);
if (lean_obj_tag(v_val_2018_) == 3)
{
lean_object* v_v_2019_; 
v_v_2019_ = lean_ctor_get(v_val_2018_, 0);
lean_inc(v_v_2019_);
lean_dec_ref_known(v_val_2018_, 1);
return v_v_2019_;
}
else
{
lean_dec(v_val_2018_);
lean_inc(v_defValue_2015_);
return v_defValue_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_2020_, lean_object* v_opt_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_2020_, v_opt_2021_);
lean_dec_ref(v_opt_2021_);
lean_dec_ref(v_opts_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_options_2027_; lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_options_2027_ = lean_ctor_get(v_c_2023_, 6);
lean_inc_ref(v_options_2027_);
lean_dec_ref(v_c_2023_);
v___x_2028_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_2027_, v___y_2025_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2033_ = l_Lean_linter_doc_deferred;
v___x_2034_ = l_Lean_Linter_getLinterValue(v___x_2033_, v_a_2029_);
lean_dec(v_a_2029_);
v___x_2035_ = lean_box(v___x_2034_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2045_, lean_object* v_docCheckedModules_2046_, lean_object* v_m_2047_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2045_, v_m_2047_);
if (v___x_2048_ == 0)
{
return v___x_2048_;
}
else
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lean_NameSet_contains(v_docCheckedModules_2046_, v_m_2047_);
if (v___x_2049_ == 0)
{
return v___x_2048_;
}
else
{
uint8_t v___x_2050_; 
v___x_2050_ = 0;
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2051_, lean_object* v_docCheckedModules_2052_, lean_object* v_m_2053_){
_start:
{
uint8_t v_res_2054_; lean_object* v_r_2055_; 
v_res_2054_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2051_, v_docCheckedModules_2052_, v_m_2053_);
lean_dec(v_m_2053_);
lean_dec(v_docCheckedModules_2052_);
lean_dec(v_pkgRoot_2051_);
v_r_2055_ = lean_box(v_res_2054_);
return v_r_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_2063_, uint8_t v___y_2064_, lean_object* v_as_2065_, size_t v_sz_2066_, size_t v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_a_2072_; uint8_t v___x_2076_; 
v___x_2076_ = lean_usize_dec_lt(v_i_2067_, v_sz_2066_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v_sp_2063_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_b_2068_);
return v___x_2077_;
}
else
{
lean_object* v_a_2078_; lean_object* v_snd_2079_; lean_object* v_fst_2080_; lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2177_; 
v_a_2078_ = lean_array_uget_borrowed(v_as_2065_, v_i_2067_);
v_snd_2079_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_snd_2079_);
v_fst_2080_ = lean_ctor_get(v_snd_2079_, 0);
lean_inc(v_fst_2080_);
v_fst_2081_ = lean_ctor_get(v_a_2078_, 0);
v_snd_2082_ = lean_ctor_get(v_snd_2079_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_snd_2079_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_snd_2079_, 0);
lean_dec(v_unused_2178_);
v___x_2084_ = v_snd_2079_;
v_isShared_2085_ = v_isSharedCheck_2177_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_dec(v_snd_2079_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2177_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_site_2086_; lean_object* v_sourceString_2087_; lean_object* v___x_2088_; lean_object* v___y_2090_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_site_2086_ = lean_ctor_get(v_fst_2080_, 0);
lean_inc_ref(v_site_2086_);
v_sourceString_2087_ = lean_ctor_get(v_fst_2080_, 2);
lean_inc_ref(v_sourceString_2087_);
lean_dec(v_fst_2080_);
v___x_2088_ = lean_box(0);
v___x_2169_ = lean_string_utf8_byte_size(v_sourceString_2087_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_nat_dec_eq(v___x_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2173_ = lean_string_append(v___x_2172_, v_sourceString_2087_);
lean_dec_ref(v_sourceString_2087_);
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__6));
v___x_2175_ = lean_string_append(v___x_2173_, v___x_2174_);
v___y_2090_ = v___x_2175_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2176_; 
lean_dec_ref(v_sourceString_2087_);
v___x_2176_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2090_ = v___x_2176_;
goto v___jp_2089_;
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2081_);
lean_inc(v_sp_2063_);
v___x_2092_ = l_Lean_SearchPath_findWithExt(v_sp_2063_, v___x_2091_, v_fst_2081_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
if (lean_obj_tag(v_a_2093_) == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2094_ = l_Lean_MessageData_toString(v_snd_2082_);
v___x_2095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
lean_inc(v_fst_2081_);
v___x_2096_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2081_, v___y_2064_);
v___x_2097_ = lean_string_append(v___x_2095_, v___x_2096_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2099_ = lean_string_append(v___x_2097_, v___x_2098_);
v___x_2100_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2086_);
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = lean_string_append(v___x_2101_, v___y_2090_);
lean_dec_ref(v___y_2090_);
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2104_ = lean_string_append(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_string_append(v___x_2104_, v___x_2094_);
lean_dec_ref(v___x_2094_);
v___x_2106_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_2105_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec_ref_known(v___x_2106_, 1);
lean_del_object(v___x_2084_);
v_a_2072_ = v___x_2088_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_sp_2063_);
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_ref_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v_ref_2111_ = lean_ctor_get(v___y_2069_, 5);
v___x_2112_ = lean_io_error_to_string(v_a_2107_);
v___x_2113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
v___x_2114_ = l_Lean_MessageData_ofFormat(v___x_2113_);
lean_inc(v_ref_2111_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___x_2114_);
lean_ctor_set(v___x_2084_, 0, v_ref_2111_);
v___x_2116_ = v___x_2084_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_ref_2111_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2116_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_val_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2153_; 
v_val_2122_ = lean_ctor_get(v_a_2093_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2093_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2124_ = v_a_2093_;
v_isShared_2125_ = v_isSharedCheck_2153_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_val_2122_);
lean_dec(v_a_2093_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2153_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2126_ = l_Lean_MessageData_toString(v_snd_2082_);
v___x_2127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2128_ = lean_string_append(v_val_2122_, v___x_2127_);
v___x_2129_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2086_);
v___x_2130_ = lean_string_append(v___x_2128_, v___x_2129_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_string_append(v___x_2130_, v___y_2090_);
lean_dec_ref(v___y_2090_);
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2133_ = lean_string_append(v___x_2131_, v___x_2132_);
v___x_2134_ = lean_string_append(v___x_2133_, v___x_2126_);
lean_dec_ref(v___x_2126_);
v___x_2135_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref_known(v___x_2135_, 1);
lean_del_object(v___x_2124_);
lean_del_object(v___x_2084_);
v_a_2072_ = v___x_2088_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_sp_2063_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2152_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2152_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_ref_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v_ref_2140_ = lean_ctor_get(v___y_2069_, 5);
v___x_2141_ = lean_io_error_to_string(v_a_2136_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 3);
lean_ctor_set(v___x_2124_, 0, v___x_2141_);
v___x_2143_ = v___x_2124_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = l_Lean_MessageData_ofFormat(v___x_2143_);
lean_inc(v_ref_2140_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___x_2144_);
lean_ctor_set(v___x_2084_, 0, v_ref_2140_);
v___x_2146_ = v___x_2084_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_ref_2140_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2146_);
v___x_2148_ = v___x_2138_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
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
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v___y_2090_);
lean_dec_ref(v_site_2086_);
lean_dec(v_snd_2082_);
lean_dec(v_sp_2063_);
v_a_2154_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2156_ = v___x_2092_;
v_isShared_2157_ = v_isSharedCheck_2168_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2092_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2168_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_ref_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v_ref_2158_ = lean_ctor_get(v___y_2069_, 5);
v___x_2159_ = lean_io_error_to_string(v_a_2154_);
v___x_2160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
v___x_2161_ = l_Lean_MessageData_ofFormat(v___x_2160_);
lean_inc(v_ref_2158_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___x_2161_);
lean_ctor_set(v___x_2084_, 0, v_ref_2158_);
v___x_2163_ = v___x_2084_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_ref_2158_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2163_);
v___x_2165_ = v___x_2156_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
v___jp_2071_:
{
size_t v___x_2073_; size_t v___x_2074_; 
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_add(v_i_2067_, v___x_2073_);
v_i_2067_ = v___x_2074_;
v_b_2068_ = v_a_2072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2179_, lean_object* v___y_2180_, lean_object* v_as_2181_, lean_object* v_sz_2182_, lean_object* v_i_2183_, lean_object* v_b_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v___y_8996__boxed_2187_; size_t v_sz_boxed_2188_; size_t v_i_boxed_2189_; lean_object* v_res_2190_; 
v___y_8996__boxed_2187_ = lean_unbox(v___y_2180_);
v_sz_boxed_2188_ = lean_unbox_usize(v_sz_2182_);
lean_dec(v_sz_2182_);
v_i_boxed_2189_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2179_, v___y_8996__boxed_2187_, v_as_2181_, v_sz_boxed_2188_, v_i_boxed_2189_, v_b_2184_, v___y_2185_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v_as_2181_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_2197_, lean_object* v_sp_2198_, lean_object* v_as_2199_, size_t v_sz_2200_, size_t v_i_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_a_2207_; uint8_t v_unlocated_2211_; 
v_unlocated_2211_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
if (v_unlocated_2211_ == 0)
{
lean_object* v___x_2212_; 
lean_dec(v_sp_2198_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v_b_2202_);
return v___x_2212_;
}
else
{
lean_object* v_a_2213_; lean_object* v_snd_2214_; lean_object* v_fst_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2344_; 
v_a_2213_ = lean_array_uget_borrowed(v_as_2199_, v_i_2201_);
v_snd_2214_ = lean_ctor_get(v_a_2213_, 1);
lean_inc(v_snd_2214_);
v_fst_2215_ = lean_ctor_get(v_snd_2214_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_snd_2214_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_snd_2214_, 1);
lean_dec(v_unused_2345_);
v___x_2217_ = v_snd_2214_;
v_isShared_2218_ = v_isSharedCheck_2344_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_fst_2215_);
lean_dec(v_snd_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2344_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_fst_2219_; lean_object* v_site_2220_; lean_object* v___x_2221_; 
v_fst_2219_ = lean_ctor_get(v_a_2213_, 0);
v_site_2220_ = lean_ctor_get(v_fst_2215_, 0);
lean_inc_ref_n(v_site_2220_, 2);
lean_dec(v_fst_2215_);
v___x_2221_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2219_, v_site_2220_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_fst_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2262_; 
v_fst_2223_ = lean_ctor_get(v_b_2202_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_b_2202_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v_b_2202_, 1);
lean_dec(v_unused_2263_);
v___x_2225_ = v_b_2202_;
v_isShared_2226_ = v_isSharedCheck_2262_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_fst_2223_);
lean_dec(v_b_2202_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2262_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v_name_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2227_ = l_Lean_linter_doc_deferred;
v_name_2228_ = lean_ctor_get(v___x_2227_, 0);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_2230_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2220_);
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
lean_inc(v_fst_2219_);
v___x_2234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2219_, v___x_2197_);
v___x_2235_ = lean_string_append(v___x_2233_, v___x_2234_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_2237_ = lean_string_append(v___x_2235_, v___x_2236_);
lean_inc(v_name_2228_);
v___x_2238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2228_, v___x_2197_);
v___x_2239_ = lean_string_append(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2241_ = lean_string_append(v___x_2239_, v___x_2240_);
v___x_2242_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec_ref_known(v___x_2242_, 1);
lean_del_object(v___x_2217_);
v___x_2243_ = lean_box(v_unlocated_2211_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v___x_2243_);
v___x_2245_ = v___x_2225_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_fst_2223_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v_a_2207_ = v___x_2245_;
goto v___jp_2206_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2261_; 
lean_del_object(v___x_2225_);
lean_dec(v_fst_2223_);
lean_dec(v_sp_2198_);
v_a_2247_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2249_ = v___x_2242_;
v_isShared_2250_ = v_isSharedCheck_2261_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2242_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2261_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_ref_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v_ref_2251_ = lean_ctor_get(v___y_2203_, 5);
v___x_2252_ = lean_io_error_to_string(v_a_2247_);
v___x_2253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofFormat(v___x_2253_);
lean_inc(v_ref_2251_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2254_);
lean_ctor_set(v___x_2217_, 0, v_ref_2251_);
v___x_2256_ = v___x_2217_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_ref_2251_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2258_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2256_);
v___x_2258_ = v___x_2249_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2264_; lean_object* v_snd_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_site_2220_);
v_fst_2264_ = lean_ctor_get(v_b_2202_, 0);
v_snd_2265_ = lean_ctor_get(v_b_2202_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_b_2202_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2267_ = v_b_2202_;
v_isShared_2268_ = v_isSharedCheck_2335_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_snd_2265_);
lean_inc(v_fst_2264_);
lean_dec(v_b_2202_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2335_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_val_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2334_; 
v_val_2269_ = lean_ctor_get(v_a_2222_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2271_ = v_a_2222_;
v_isShared_2272_ = v_isSharedCheck_2334_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_val_2269_);
lean_dec(v_a_2222_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2334_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2219_);
lean_inc(v_sp_2198_);
v___x_2274_ = l_Lean_SearchPath_findWithExt(v_sp_2198_, v___x_2273_, v_fst_2219_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v_name_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v_val_2269_);
lean_dec(v_snd_2265_);
v___x_2276_ = l_Lean_linter_doc_deferred;
v_name_2277_ = lean_ctor_get(v___x_2276_, 0);
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2219_);
v___x_2279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2219_, v___x_2197_);
v___x_2280_ = lean_string_append(v___x_2278_, v___x_2279_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
lean_inc(v_name_2277_);
v___x_2283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2277_, v___x_2197_);
v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
lean_dec_ref(v___x_2283_);
v___x_2285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
v___x_2287_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_dec_ref_known(v___x_2287_, 1);
lean_del_object(v___x_2271_);
lean_del_object(v___x_2217_);
v___x_2288_ = lean_box(v_unlocated_2211_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2288_);
v___x_2290_ = v___x_2267_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_fst_2264_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
v_a_2207_ = v___x_2290_;
goto v___jp_2206_;
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2308_; 
lean_del_object(v___x_2267_);
lean_dec(v_fst_2264_);
lean_dec(v_sp_2198_);
v_a_2292_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2294_ = v___x_2287_;
v_isShared_2295_ = v_isSharedCheck_2308_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2287_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2308_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_ref_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v_ref_2296_ = lean_ctor_get(v___y_2203_, 5);
v___x_2297_ = lean_io_error_to_string(v_a_2292_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2297_);
v___x_2299_ = v___x_2271_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l_Lean_MessageData_ofFormat(v___x_2299_);
lean_inc(v_ref_2296_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2300_);
lean_ctor_set(v___x_2217_, 0, v_ref_2296_);
v___x_2302_ = v___x_2217_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_ref_2296_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2302_);
v___x_2304_ = v___x_2294_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
else
{
lean_object* v_val_2309_; lean_object* v___x_2310_; lean_object* v_name_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_del_object(v___x_2271_);
lean_del_object(v___x_2217_);
v_val_2309_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_val_2309_);
lean_dec_ref_known(v_a_2275_, 1);
v___x_2310_ = l_Lean_linter_doc_deferred;
v_name_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_name_2311_);
v___x_2312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2312_, 0, v_val_2309_);
lean_ctor_set(v___x_2312_, 1, v_val_2269_);
lean_ctor_set(v___x_2312_, 2, v_name_2311_);
v___x_2313_ = lean_array_push(v_fst_2264_, v___x_2312_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2313_);
v___x_2315_ = v___x_2267_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_snd_2265_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
v_a_2207_ = v___x_2315_;
goto v___jp_2206_;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_val_2269_);
lean_del_object(v___x_2267_);
lean_dec(v_snd_2265_);
lean_dec(v_fst_2264_);
lean_dec(v_sp_2198_);
v_a_2317_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2319_ = v___x_2274_;
v_isShared_2320_ = v_isSharedCheck_2333_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2274_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2333_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_ref_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
v_ref_2321_ = lean_ctor_get(v___y_2203_, 5);
v___x_2322_ = lean_io_error_to_string(v_a_2317_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2322_);
v___x_2324_ = v___x_2271_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = l_Lean_MessageData_ofFormat(v___x_2324_);
lean_inc(v_ref_2321_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2325_);
lean_ctor_set(v___x_2217_, 0, v_ref_2321_);
v___x_2327_ = v___x_2217_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_ref_2321_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2327_);
v___x_2329_ = v___x_2319_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
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
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v_site_2220_);
lean_del_object(v___x_2217_);
lean_dec_ref(v_b_2202_);
lean_dec(v_sp_2198_);
v_a_2336_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2221_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2221_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
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
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
v___jp_2206_:
{
size_t v___x_2208_; size_t v___x_2209_; 
v___x_2208_ = ((size_t)1ULL);
v___x_2209_ = lean_usize_add(v_i_2201_, v___x_2208_);
v_i_2201_ = v___x_2209_;
v_b_2202_ = v_a_2207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2346_, lean_object* v_sp_2347_, lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_b_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v___x_9232__boxed_2355_; size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v___x_9232__boxed_2355_ = lean_unbox(v___x_2346_);
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_9232__boxed_2355_, v_sp_2347_, v_as_2348_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v_as_2348_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2359_, lean_object* v_as_2360_, size_t v_sz_2361_, size_t v_i_2362_, lean_object* v_b_2363_){
_start:
{
lean_object* v_a_2366_; uint8_t v___x_2370_; 
v___x_2370_ = lean_usize_dec_lt(v_i_2362_, v_sz_2361_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_b_2363_);
return v___x_2371_;
}
else
{
lean_object* v_a_2372_; uint8_t v___x_2373_; 
v_a_2372_ = lean_array_uget_borrowed(v_as_2360_, v_i_2362_);
v___x_2373_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2359_, v_a_2372_);
if (v___x_2373_ == 0)
{
v_a_2366_ = v_b_2363_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2374_; 
lean_inc(v_a_2372_);
v___x_2374_ = l_Lean_NameSet_insert(v_b_2363_, v_a_2372_);
v_a_2366_ = v___x_2374_;
goto v___jp_2365_;
}
}
v___jp_2365_:
{
size_t v___x_2367_; size_t v___x_2368_; 
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2362_, v___x_2367_);
v_i_2362_ = v___x_2368_;
v_b_2363_ = v_a_2366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2375_, lean_object* v_as_2376_, lean_object* v_sz_2377_, lean_object* v_i_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_){
_start:
{
size_t v_sz_boxed_2381_; size_t v_i_boxed_2382_; lean_object* v_res_2383_; 
v_sz_boxed_2381_ = lean_unbox_usize(v_sz_2377_);
lean_dec(v_sz_2377_);
v_i_boxed_2382_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2375_, v_as_2376_, v_sz_boxed_2381_, v_i_boxed_2382_, v_b_2379_);
lean_dec_ref(v_as_2376_);
lean_dec(v_pkgRoot_2375_);
return v_res_2383_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(32u);
v___x_2391_ = lean_mk_empty_array_with_capacity(v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2393_ = ((size_t)5ULL);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_unsigned_to_nat(32u);
v___x_2396_ = lean_mk_empty_array_with_capacity(v___x_2395_);
v___x_2397_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2398_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v___x_2396_);
lean_ctor_set(v___x_2398_, 2, v___x_2394_);
lean_ctor_set(v___x_2398_, 3, v___x_2394_);
lean_ctor_set_usize(v___x_2398_, 4, v___x_2393_);
return v___x_2398_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = l_Lean_NameSet_empty;
v___x_2405_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
lean_ctor_set(v___x_2406_, 2, v___x_2404_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = l_Lean_firstFrontendMacroScope;
v___x_2409_ = lean_nat_add(v___x_2408_, v___x_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2420_; uint64_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2421_ = 0ULL;
v___x_2422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set_uint64(v___x_2422_, sizeof(void*)*1, v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v_unlocated_2425_; lean_object* v___x_2426_; 
v___x_2423_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2424_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2425_ = 1;
v___x_2426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2424_);
lean_ctor_set(v___x_2426_, 2, v___x_2423_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*3, v_unlocated_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = l_Lean_Options_empty;
v___x_2430_ = l_Lean_Core_getMaxHeartbeats(v___x_2429_);
return v___x_2430_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = l_Lean_diagnostics;
v___x_2432_ = l_Lean_Options_empty;
v___x_2433_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2432_, v___x_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2434_, lean_object* v_linterOpts_2435_, lean_object* v_sp_2436_, lean_object* v_env_2437_, lean_object* v_pkgRoot_2438_, lean_object* v_docCheckedModules_2439_){
_start:
{
lean_object* v___y_2442_; lean_object* v_a_2443_; lean_object* v___y_2468_; uint8_t v___y_2469_; lean_object* v_a_2472_; uint8_t v___y_2476_; lean_object* v_a_2477_; lean_object* v___y_2494_; uint8_t v_lintOnly_2497_; uint8_t v_mode_2498_; lean_object* v___f_2499_; lean_object* v___f_2500_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2508_; lean_object* v_fileName_2509_; lean_object* v_fileMap_2510_; lean_object* v_currRecDepth_2511_; lean_object* v_ref_2512_; lean_object* v_currNamespace_2513_; lean_object* v_openDecls_2514_; lean_object* v_initHeartbeats_2515_; lean_object* v_maxHeartbeats_2516_; lean_object* v_quotContext_2517_; lean_object* v_currMacroScope_2518_; lean_object* v_cancelTk_x3f_2519_; uint8_t v_suppressElabErrors_2520_; lean_object* v_inheritedTraceOptions_2521_; lean_object* v___y_2522_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; uint8_t v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; uint8_t v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; lean_object* v___y_2581_; uint8_t v___y_2582_; uint8_t v___y_2603_; 
v_lintOnly_2497_ = lean_ctor_get_uint8(v_args_2434_, sizeof(void*)*3);
v_mode_2498_ = lean_ctor_get_uint8(v_args_2434_, sizeof(void*)*3 + 1);
v___f_2499_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
lean_inc(v_docCheckedModules_2439_);
lean_inc(v_pkgRoot_2438_);
v___f_2500_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2500_, 0, v_pkgRoot_2438_);
lean_closure_set(v___f_2500_, 1, v_docCheckedModules_2439_);
if (v_lintOnly_2497_ == 0)
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = l_Lean_linter_doc_deferred;
v___x_2640_ = l_Lean_Linter_getLinterValue(v___x_2639_, v_linterOpts_2435_);
v___y_2603_ = v___x_2640_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2641_; lean_object* v_name_2642_; uint8_t v___x_2643_; 
v___x_2641_ = l_Lean_linter_doc_deferred;
v_name_2642_ = lean_ctor_get(v___x_2641_, 0);
v___x_2643_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2642_, v_linterOpts_2435_);
v___y_2603_ = v___x_2643_;
goto v___jp_2602_;
}
v___jp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = lean_st_ref_get(v___y_2442_);
lean_dec(v___y_2442_);
lean_dec(v___x_2444_);
v___x_2445_ = l_Lean_Environment_header(v_env_2437_);
lean_dec_ref(v_env_2437_);
v___x_2446_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2445_);
v_sz_2447_ = lean_array_size(v___x_2446_);
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2438_, v___x_2446_, v_sz_2447_, v___x_2448_, v_docCheckedModules_2439_);
lean_dec_ref(v___x_2446_);
lean_dec(v_pkgRoot_2438_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2458_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_a_2443_);
lean_ctor_set(v___x_2454_, 1, v_a_2450_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v_a_2443_);
v_a_2459_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2449_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2449_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
v___jp_2467_:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2470_, 0, v___y_2469_);
v___y_2442_ = v___y_2468_;
v_a_2443_ = v___x_2470_;
goto v___jp_2441_;
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_mk_io_user_error(v_a_2472_);
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
v___jp_2475_:
{
if (lean_obj_tag(v_a_2477_) == 0)
{
lean_object* v_msg_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_msg_2478_ = lean_ctor_get(v_a_2477_, 1);
lean_inc_ref(v_msg_2478_);
lean_dec_ref_known(v_a_2477_, 2);
v___x_2479_ = l_Lean_MessageData_toString(v_msg_2478_);
v___x_2480_ = lean_mk_io_user_error(v___x_2479_);
v___x_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v_id_2482_; lean_object* v___x_2483_; 
v_id_2482_ = lean_ctor_get(v_a_2477_, 0);
lean_inc(v_id_2482_);
lean_dec_ref_known(v_a_2477_, 2);
v___x_2483_ = l_Lean_InternalExceptionId_getName(v_id_2482_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v_id_2482_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2486_ = l_Lean_Name_toString(v_a_2484_, v___y_2476_);
v___x_2487_ = lean_string_append(v___x_2485_, v___x_2486_);
lean_dec_ref(v___x_2486_);
v_a_2472_ = v___x_2487_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec_ref_known(v___x_2483_, 1);
v___x_2488_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2489_ = l_Nat_reprFast(v_id_2482_);
v___x_2490_ = lean_string_append(v___x_2488_, v___x_2489_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2492_ = lean_string_append(v___x_2490_, v___x_2491_);
v_a_2472_ = v___x_2492_;
goto v___jp_2471_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2494_);
lean_ctor_set(v___x_2495_, 1, v_docCheckedModules_2439_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
return v___x_2496_;
}
v___jp_2501_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = l_Lean_maxRecDepth;
v___x_2524_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2503_, v___x_2523_);
lean_inc_ref(v___y_2503_);
v___x_2525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2525_, 0, v_fileName_2509_);
lean_ctor_set(v___x_2525_, 1, v_fileMap_2510_);
lean_ctor_set(v___x_2525_, 2, v___y_2503_);
lean_ctor_set(v___x_2525_, 3, v_currRecDepth_2511_);
lean_ctor_set(v___x_2525_, 4, v___x_2524_);
lean_ctor_set(v___x_2525_, 5, v_ref_2512_);
lean_ctor_set(v___x_2525_, 6, v_currNamespace_2513_);
lean_ctor_set(v___x_2525_, 7, v_openDecls_2514_);
lean_ctor_set(v___x_2525_, 8, v_initHeartbeats_2515_);
lean_ctor_set(v___x_2525_, 9, v_maxHeartbeats_2516_);
lean_ctor_set(v___x_2525_, 10, v_quotContext_2517_);
lean_ctor_set(v___x_2525_, 11, v_currMacroScope_2518_);
lean_ctor_set(v___x_2525_, 12, v_cancelTk_x3f_2519_);
lean_ctor_set(v___x_2525_, 13, v_inheritedTraceOptions_2521_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*14, v___y_2502_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*14 + 1, v_suppressElabErrors_2520_);
lean_inc_ref(v___y_2504_);
v___x_2526_ = l_Lean_Doc_DeferredCheck_run(v___f_2500_, v___y_2504_, v___x_2525_, v___y_2522_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; uint8_t v___x_2528_; uint8_t v___x_2529_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = 1;
v___x_2529_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2498_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; size_t v_sz_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v___y_2522_);
v___x_2530_ = lean_box(0);
v_sz_2531_ = lean_array_size(v_a_2527_);
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2436_, v___y_2505_, v_a_2527_, v_sz_2531_, v___x_2532_, v___x_2530_, v___x_2525_);
lean_dec_ref_known(v___x_2525_, 14);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
lean_dec_ref_known(v___x_2533_, 1);
v___x_2534_ = lean_array_get_size(v_a_2527_);
lean_dec(v_a_2527_);
v___x_2535_ = lean_nat_dec_eq(v___x_2534_, v___y_2507_);
lean_dec(v___y_2507_);
if (v___x_2535_ == 0)
{
v___y_2468_ = v___y_2506_;
v___y_2469_ = v___y_2505_;
goto v___jp_2467_;
}
else
{
v___y_2468_ = v___y_2506_;
v___y_2469_ = v___x_2529_;
goto v___jp_2467_;
}
}
else
{
lean_object* v_a_2536_; 
lean_dec(v_a_2527_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v_docCheckedModules_2439_);
lean_dec(v_pkgRoot_2438_);
lean_dec_ref(v_env_2437_);
v_a_2536_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2533_, 1);
v___y_2476_ = v___y_2505_;
v_a_2477_ = v_a_2536_;
goto v___jp_2475_;
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2537_ = lean_mk_empty_array_with_capacity(v___y_2507_);
lean_dec(v___y_2507_);
v___x_2538_ = lean_box(v___y_2508_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v_sz_2540_ = lean_array_size(v_a_2527_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2529_, v_sp_2436_, v_a_2527_, v_sz_2540_, v___x_2541_, v___x_2539_, v___x_2525_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref_known(v___x_2525_, 14);
lean_dec(v_a_2527_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_fst_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2544_);
v_snd_2545_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_a_2543_);
v___x_2546_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2546_, 0, v_fst_2544_);
v___x_2547_ = lean_unbox(v_snd_2545_);
lean_dec(v_snd_2545_);
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*1, v___x_2547_);
v___y_2442_ = v___y_2506_;
v_a_2443_ = v___x_2546_;
goto v___jp_2441_;
}
else
{
lean_object* v_a_2548_; 
lean_dec(v___y_2506_);
lean_dec(v_docCheckedModules_2439_);
lean_dec(v_pkgRoot_2438_);
lean_dec_ref(v_env_2437_);
v_a_2548_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2542_, 1);
v___y_2476_ = v___y_2505_;
v_a_2477_ = v_a_2548_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_a_2549_; 
lean_dec_ref_known(v___x_2525_, 14);
lean_dec(v___y_2522_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v_docCheckedModules_2439_);
lean_dec(v_pkgRoot_2438_);
lean_dec_ref(v_env_2437_);
lean_dec(v_sp_2436_);
v_a_2549_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2526_, 1);
v___y_2476_ = v___y_2505_;
v_a_2477_ = v_a_2549_;
goto v___jp_2475_;
}
}
v___jp_2550_:
{
lean_object* v_fileName_2560_; lean_object* v_fileMap_2561_; lean_object* v_currRecDepth_2562_; lean_object* v_ref_2563_; lean_object* v_currNamespace_2564_; lean_object* v_openDecls_2565_; lean_object* v_initHeartbeats_2566_; lean_object* v_maxHeartbeats_2567_; lean_object* v_quotContext_2568_; lean_object* v_currMacroScope_2569_; lean_object* v_cancelTk_x3f_2570_; uint8_t v_suppressElabErrors_2571_; lean_object* v_inheritedTraceOptions_2572_; 
v_fileName_2560_ = lean_ctor_get(v___y_2558_, 0);
lean_inc_ref(v_fileName_2560_);
v_fileMap_2561_ = lean_ctor_get(v___y_2558_, 1);
lean_inc_ref(v_fileMap_2561_);
v_currRecDepth_2562_ = lean_ctor_get(v___y_2558_, 3);
lean_inc(v_currRecDepth_2562_);
v_ref_2563_ = lean_ctor_get(v___y_2558_, 5);
lean_inc(v_ref_2563_);
v_currNamespace_2564_ = lean_ctor_get(v___y_2558_, 6);
lean_inc(v_currNamespace_2564_);
v_openDecls_2565_ = lean_ctor_get(v___y_2558_, 7);
lean_inc(v_openDecls_2565_);
v_initHeartbeats_2566_ = lean_ctor_get(v___y_2558_, 8);
lean_inc(v_initHeartbeats_2566_);
v_maxHeartbeats_2567_ = lean_ctor_get(v___y_2558_, 9);
lean_inc(v_maxHeartbeats_2567_);
v_quotContext_2568_ = lean_ctor_get(v___y_2558_, 10);
lean_inc(v_quotContext_2568_);
v_currMacroScope_2569_ = lean_ctor_get(v___y_2558_, 11);
lean_inc(v_currMacroScope_2569_);
v_cancelTk_x3f_2570_ = lean_ctor_get(v___y_2558_, 12);
lean_inc(v_cancelTk_x3f_2570_);
v_suppressElabErrors_2571_ = lean_ctor_get_uint8(v___y_2558_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2572_ = lean_ctor_get(v___y_2558_, 13);
lean_inc_ref(v_inheritedTraceOptions_2572_);
lean_dec_ref(v___y_2558_);
v___y_2502_ = v___y_2551_;
v___y_2503_ = v___y_2552_;
v___y_2504_ = v___y_2553_;
v___y_2505_ = v___y_2554_;
v___y_2506_ = v___y_2555_;
v___y_2507_ = v___y_2556_;
v___y_2508_ = v___y_2557_;
v_fileName_2509_ = v_fileName_2560_;
v_fileMap_2510_ = v_fileMap_2561_;
v_currRecDepth_2511_ = v_currRecDepth_2562_;
v_ref_2512_ = v_ref_2563_;
v_currNamespace_2513_ = v_currNamespace_2564_;
v_openDecls_2514_ = v_openDecls_2565_;
v_initHeartbeats_2515_ = v_initHeartbeats_2566_;
v_maxHeartbeats_2516_ = v_maxHeartbeats_2567_;
v_quotContext_2517_ = v_quotContext_2568_;
v_currMacroScope_2518_ = v_currMacroScope_2569_;
v_cancelTk_x3f_2519_ = v_cancelTk_x3f_2570_;
v_suppressElabErrors_2520_ = v_suppressElabErrors_2571_;
v_inheritedTraceOptions_2521_ = v_inheritedTraceOptions_2572_;
v___y_2522_ = v___y_2559_;
goto v___jp_2501_;
}
v___jp_2573_:
{
if (v___y_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v_env_2584_; lean_object* v_nextMacroScope_2585_; lean_object* v_ngen_2586_; lean_object* v_auxDeclNGen_2587_; lean_object* v_traceState_2588_; lean_object* v_messages_2589_; lean_object* v_infoState_2590_; lean_object* v_snapshotTasks_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2600_; 
v___x_2583_ = lean_st_ref_take(v___y_2578_);
v_env_2584_ = lean_ctor_get(v___x_2583_, 0);
v_nextMacroScope_2585_ = lean_ctor_get(v___x_2583_, 1);
v_ngen_2586_ = lean_ctor_get(v___x_2583_, 2);
v_auxDeclNGen_2587_ = lean_ctor_get(v___x_2583_, 3);
v_traceState_2588_ = lean_ctor_get(v___x_2583_, 4);
v_messages_2589_ = lean_ctor_get(v___x_2583_, 6);
v_infoState_2590_ = lean_ctor_get(v___x_2583_, 7);
v_snapshotTasks_2591_ = lean_ctor_get(v___x_2583_, 8);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2583_, 5);
lean_dec(v_unused_2601_);
v___x_2593_ = v___x_2583_;
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snapshotTasks_2591_);
lean_inc(v_infoState_2590_);
lean_inc(v_messages_2589_);
lean_inc(v_traceState_2588_);
lean_inc(v_auxDeclNGen_2587_);
lean_inc(v_ngen_2586_);
lean_inc(v_nextMacroScope_2585_);
lean_inc(v_env_2584_);
lean_dec(v___x_2583_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = l_Lean_Kernel_enableDiag(v_env_2584_, v___y_2574_);
lean_inc_ref(v___y_2575_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 5, v___y_2575_);
lean_ctor_set(v___x_2593_, 0, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_nextMacroScope_2585_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_ngen_2586_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_auxDeclNGen_2587_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_traceState_2588_);
lean_ctor_set(v_reuseFailAlloc_2599_, 5, v___y_2575_);
lean_ctor_set(v_reuseFailAlloc_2599_, 6, v_messages_2589_);
lean_ctor_set(v_reuseFailAlloc_2599_, 7, v_infoState_2590_);
lean_ctor_set(v_reuseFailAlloc_2599_, 8, v_snapshotTasks_2591_);
v___x_2597_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_st_ref_put(v___y_2578_, v___x_2597_);
lean_inc(v___y_2578_);
v___y_2551_ = v___y_2574_;
v___y_2552_ = v___y_2576_;
v___y_2553_ = v___f_2499_;
v___y_2554_ = v___y_2577_;
v___y_2555_ = v___y_2578_;
v___y_2556_ = v___y_2579_;
v___y_2557_ = v___y_2580_;
v___y_2558_ = v___y_2581_;
v___y_2559_ = v___y_2578_;
goto v___jp_2550_;
}
}
}
else
{
lean_inc(v___y_2578_);
v___y_2551_ = v___y_2574_;
v___y_2552_ = v___y_2576_;
v___y_2553_ = v___f_2499_;
v___y_2554_ = v___y_2577_;
v___y_2555_ = v___y_2578_;
v___y_2556_ = v___y_2579_;
v___y_2557_ = v___y_2580_;
v___y_2558_ = v___y_2581_;
v___y_2559_ = v___y_2578_;
goto v___jp_2550_;
}
}
v___jp_2602_:
{
if (v___y_2603_ == 0)
{
uint8_t v___x_2604_; uint8_t v___x_2605_; 
lean_dec_ref(v___f_2500_);
lean_dec(v_pkgRoot_2438_);
lean_dec_ref(v_env_2437_);
lean_dec(v_sp_2436_);
v___x_2604_ = 1;
v___x_2605_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2498_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2606_, 0, v___y_2603_);
v___y_2494_ = v___x_2606_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2608_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set_uint8(v___x_2608_, sizeof(void*)*1, v___y_2603_);
v___y_2494_ = v___x_2608_;
goto v___jp_2493_;
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_env_2636_; uint8_t v___x_2637_; uint8_t v___x_2638_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2611_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2612_ = lean_io_get_num_heartbeats();
v___x_2613_ = l_Lean_firstFrontendMacroScope;
v___x_2614_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2615_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_box(0);
v___x_2618_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2619_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2620_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2621_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2437_);
v___x_2622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2622_, 0, v_env_2437_);
lean_ctor_set(v___x_2622_, 1, v___x_2614_);
lean_ctor_set(v___x_2622_, 2, v___x_2615_);
lean_ctor_set(v___x_2622_, 3, v___x_2618_);
lean_ctor_set(v___x_2622_, 4, v___x_2619_);
lean_ctor_set(v___x_2622_, 5, v___x_2610_);
lean_ctor_set(v___x_2622_, 6, v___x_2611_);
lean_ctor_set(v___x_2622_, 7, v___x_2620_);
lean_ctor_set(v___x_2622_, 8, v___x_2621_);
v___x_2623_ = lean_st_mk_ref(v___x_2622_);
v___x_2624_ = l_Lean_inheritedTraceOptions;
v___x_2625_ = lean_st_ref_get(v___x_2624_);
v___x_2626_ = lean_st_ref_get(v___x_2623_);
v___x_2627_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2628_ = l_Lean_instInhabitedFileMap_default;
v___x_2629_ = l_Lean_Options_empty;
v___x_2630_ = lean_unsigned_to_nat(1000u);
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2633_ = 0;
v___x_2634_ = lean_box(0);
lean_inc(v___x_2625_);
lean_inc(v___x_2612_);
v___x_2635_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2635_, 0, v___x_2627_);
lean_ctor_set(v___x_2635_, 1, v___x_2628_);
lean_ctor_set(v___x_2635_, 2, v___x_2629_);
lean_ctor_set(v___x_2635_, 3, v___x_2609_);
lean_ctor_set(v___x_2635_, 4, v___x_2630_);
lean_ctor_set(v___x_2635_, 5, v___x_2631_);
lean_ctor_set(v___x_2635_, 6, v___x_2616_);
lean_ctor_set(v___x_2635_, 7, v___x_2617_);
lean_ctor_set(v___x_2635_, 8, v___x_2612_);
lean_ctor_set(v___x_2635_, 9, v___x_2632_);
lean_ctor_set(v___x_2635_, 10, v___x_2616_);
lean_ctor_set(v___x_2635_, 11, v___x_2613_);
lean_ctor_set(v___x_2635_, 12, v___x_2634_);
lean_ctor_set(v___x_2635_, 13, v___x_2625_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*14, v___x_2633_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*14 + 1, v___x_2633_);
v_env_2636_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref(v_env_2636_);
lean_dec(v___x_2626_);
v___x_2637_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2638_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2636_);
lean_dec_ref(v_env_2636_);
if (v___x_2638_ == 0)
{
if (v___x_2637_ == 0)
{
lean_dec_ref_known(v___x_2635_, 14);
lean_inc(v___x_2623_);
v___y_2502_ = v___x_2637_;
v___y_2503_ = v___x_2629_;
v___y_2504_ = v___f_2499_;
v___y_2505_ = v___y_2603_;
v___y_2506_ = v___x_2623_;
v___y_2507_ = v___x_2609_;
v___y_2508_ = v___x_2633_;
v_fileName_2509_ = v___x_2627_;
v_fileMap_2510_ = v___x_2628_;
v_currRecDepth_2511_ = v___x_2609_;
v_ref_2512_ = v___x_2631_;
v_currNamespace_2513_ = v___x_2616_;
v_openDecls_2514_ = v___x_2617_;
v_initHeartbeats_2515_ = v___x_2612_;
v_maxHeartbeats_2516_ = v___x_2632_;
v_quotContext_2517_ = v___x_2616_;
v_currMacroScope_2518_ = v___x_2613_;
v_cancelTk_x3f_2519_ = v___x_2634_;
v_suppressElabErrors_2520_ = v___x_2633_;
v_inheritedTraceOptions_2521_ = v___x_2625_;
v___y_2522_ = v___x_2623_;
goto v___jp_2501_;
}
else
{
lean_dec(v___x_2625_);
lean_dec(v___x_2612_);
v___y_2574_ = v___x_2637_;
v___y_2575_ = v___x_2610_;
v___y_2576_ = v___x_2629_;
v___y_2577_ = v___y_2603_;
v___y_2578_ = v___x_2623_;
v___y_2579_ = v___x_2609_;
v___y_2580_ = v___x_2633_;
v___y_2581_ = v___x_2635_;
v___y_2582_ = v___x_2638_;
goto v___jp_2573_;
}
}
else
{
lean_dec(v___x_2625_);
lean_dec(v___x_2612_);
v___y_2574_ = v___x_2637_;
v___y_2575_ = v___x_2610_;
v___y_2576_ = v___x_2629_;
v___y_2577_ = v___y_2603_;
v___y_2578_ = v___x_2623_;
v___y_2579_ = v___x_2609_;
v___y_2580_ = v___x_2633_;
v___y_2581_ = v___x_2635_;
v___y_2582_ = v___x_2637_;
goto v___jp_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2644_, lean_object* v_linterOpts_2645_, lean_object* v_sp_2646_, lean_object* v_env_2647_, lean_object* v_pkgRoot_2648_, lean_object* v_docCheckedModules_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2644_, v_linterOpts_2645_, v_sp_2646_, v_env_2647_, v_pkgRoot_2648_, v_docCheckedModules_2649_);
lean_dec_ref(v_linterOpts_2645_);
lean_dec_ref(v_args_2644_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2652_, uint8_t v___y_2653_, lean_object* v_as_2654_, size_t v_sz_2655_, size_t v_i_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2652_, v___y_2653_, v_as_2654_, v_sz_2655_, v_i_2656_, v_b_2657_, v___y_2658_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2662_, lean_object* v___y_2663_, lean_object* v_as_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v___y_10012__boxed_2671_; size_t v_sz_boxed_2672_; size_t v_i_boxed_2673_; lean_object* v_res_2674_; 
v___y_10012__boxed_2671_ = lean_unbox(v___y_2663_);
v_sz_boxed_2672_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2673_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2662_, v___y_10012__boxed_2671_, v_as_2664_, v_sz_boxed_2672_, v_i_boxed_2673_, v_b_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec_ref(v_as_2664_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2678_, lean_object* v_as_2679_, size_t v_sz_2680_, size_t v_i_2681_, lean_object* v_b_2682_){
_start:
{
lean_object* v_a_2685_; uint8_t v_anyUnlocated_2689_; 
v_anyUnlocated_2689_ = lean_usize_dec_lt(v_i_2681_, v_sz_2680_);
if (v_anyUnlocated_2689_ == 0)
{
lean_object* v___x_2690_; 
lean_dec(v_fst_2678_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_b_2682_);
return v___x_2690_;
}
else
{
lean_object* v_fst_2691_; lean_object* v_snd_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2729_; 
v_fst_2691_ = lean_ctor_get(v_b_2682_, 0);
v_snd_2692_ = lean_ctor_get(v_b_2682_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_b_2682_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2694_ = v_b_2682_;
v_isShared_2695_ = v_isSharedCheck_2729_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_snd_2692_);
lean_inc(v_fst_2691_);
lean_dec(v_b_2682_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2729_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_a_2696_; lean_object* v_position_x3f_2697_; 
v_a_2696_ = lean_array_uget_borrowed(v_as_2679_, v_i_2681_);
v_position_x3f_2697_ = lean_ctor_get(v_a_2696_, 2);
if (lean_obj_tag(v_position_x3f_2697_) == 0)
{
lean_object* v_linter_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v_snd_2692_);
v_linter_2698_ = lean_ctor_get(v_a_2696_, 0);
v___x_2699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2698_);
v___x_2700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2698_, v_anyUnlocated_2689_);
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2703_ = lean_string_append(v___x_2701_, v___x_2702_);
lean_inc(v_fst_2678_);
v___x_2704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2678_, v_anyUnlocated_2689_);
v___x_2705_ = lean_string_append(v___x_2703_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2707_ = lean_string_append(v___x_2705_, v___x_2706_);
v___x_2708_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_2707_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2711_; 
lean_dec_ref_known(v___x_2708_, 1);
v___x_2709_ = lean_box(v_anyUnlocated_2689_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___x_2709_);
v___x_2711_ = v___x_2694_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_fst_2691_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
v_a_2685_ = v___x_2711_;
goto v___jp_2684_;
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_del_object(v___x_2694_);
lean_dec(v_fst_2691_);
lean_dec(v_fst_2678_);
v_a_2713_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2708_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2708_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v_linter_2721_; lean_object* v_file_2722_; lean_object* v_val_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v_linter_2721_ = lean_ctor_get(v_a_2696_, 0);
v_file_2722_ = lean_ctor_get(v_a_2696_, 3);
v_val_2723_ = lean_ctor_get(v_position_x3f_2697_, 0);
lean_inc(v_linter_2721_);
lean_inc(v_val_2723_);
lean_inc_ref(v_file_2722_);
v___x_2724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2724_, 0, v_file_2722_);
lean_ctor_set(v___x_2724_, 1, v_val_2723_);
lean_ctor_set(v___x_2724_, 2, v_linter_2721_);
v___x_2725_ = lean_array_push(v_fst_2691_, v___x_2724_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2725_);
v___x_2727_ = v___x_2694_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_snd_2692_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
v_a_2685_ = v___x_2727_;
goto v___jp_2684_;
}
}
}
}
v___jp_2684_:
{
size_t v___x_2686_; size_t v___x_2687_; 
v___x_2686_ = ((size_t)1ULL);
v___x_2687_ = lean_usize_add(v_i_2681_, v___x_2686_);
v_i_2681_ = v___x_2687_;
v_b_2682_ = v_a_2685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2730_, lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2730_, v_as_2731_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2739_, size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_b_2742_){
_start:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_b_2742_);
return v___x_2745_;
}
else
{
lean_object* v_a_2746_; lean_object* v_fst_2747_; lean_object* v_snd_2748_; lean_object* v_fst_2749_; lean_object* v_snd_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2773_; 
v_a_2746_ = lean_array_uget_borrowed(v_as_2739_, v_i_2741_);
v_fst_2747_ = lean_ctor_get(v_a_2746_, 0);
v_snd_2748_ = lean_ctor_get(v_a_2746_, 1);
v_fst_2749_ = lean_ctor_get(v_b_2742_, 0);
v_snd_2750_ = lean_ctor_get(v_b_2742_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_b_2742_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2752_ = v_b_2742_;
v_isShared_2753_ = v_isSharedCheck_2773_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_snd_2750_);
lean_inc(v_fst_2749_);
lean_dec(v_b_2742_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2773_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_fst_2749_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_snd_2750_);
v___x_2755_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
size_t v_sz_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v_sz_2756_ = lean_array_size(v_snd_2748_);
v___x_2757_ = ((size_t)0ULL);
lean_inc(v_fst_2747_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2747_, v_snd_2748_, v_sz_2756_, v___x_2757_, v___x_2755_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_fst_2760_; lean_object* v_snd_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2771_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v_fst_2760_ = lean_ctor_get(v_a_2759_, 0);
v_snd_2761_ = lean_ctor_get(v_a_2759_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2763_ = v_a_2759_;
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_snd_2761_);
lean_inc(v_fst_2760_);
lean_dec(v_a_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_fst_2760_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_snd_2761_);
v___x_2766_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
size_t v___x_2767_; size_t v___x_2768_; 
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2741_, v___x_2767_);
v_i_2741_ = v___x_2768_;
v_b_2742_ = v___x_2766_;
goto _start;
}
}
}
else
{
return v___x_2758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2774_, lean_object* v_sz_2775_, lean_object* v_i_2776_, lean_object* v_b_2777_, lean_object* v___y_2778_){
_start:
{
size_t v_sz_boxed_2779_; size_t v_i_boxed_2780_; lean_object* v_res_2781_; 
v_sz_boxed_2779_ = lean_unbox_usize(v_sz_2775_);
lean_dec(v_sz_2775_);
v_i_boxed_2780_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2774_, v_sz_boxed_2779_, v_i_boxed_2780_, v_b_2777_);
lean_dec_ref(v_as_2774_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_linterOpts_2782_, lean_object* v_as_2783_, size_t v_i_2784_, size_t v_stop_2785_, lean_object* v_b_2786_){
_start:
{
lean_object* v___y_2788_; uint8_t v___x_2792_; 
v___x_2792_ = lean_usize_dec_eq(v_i_2784_, v_stop_2785_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v_linter_2794_; uint8_t v___x_2795_; 
v___x_2793_ = lean_array_uget_borrowed(v_as_2783_, v_i_2784_);
v_linter_2794_ = lean_ctor_get(v___x_2793_, 0);
v___x_2795_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2794_, v_linterOpts_2782_);
if (v___x_2795_ == 0)
{
v___y_2788_ = v_b_2786_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2796_; 
lean_inc(v___x_2793_);
v___x_2796_ = lean_array_push(v_b_2786_, v___x_2793_);
v___y_2788_ = v___x_2796_;
goto v___jp_2787_;
}
}
else
{
return v_b_2786_;
}
v___jp_2787_:
{
size_t v___x_2789_; size_t v___x_2790_; 
v___x_2789_ = ((size_t)1ULL);
v___x_2790_ = lean_usize_add(v_i_2784_, v___x_2789_);
v_i_2784_ = v___x_2790_;
v_b_2786_ = v___y_2788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_linterOpts_2797_, lean_object* v_as_2798_, lean_object* v_i_2799_, lean_object* v_stop_2800_, lean_object* v_b_2801_){
_start:
{
size_t v_i_boxed_2802_; size_t v_stop_boxed_2803_; lean_object* v_res_2804_; 
v_i_boxed_2802_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_stop_boxed_2803_ = lean_unbox_usize(v_stop_2800_);
lean_dec(v_stop_2800_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2797_, v_as_2798_, v_i_boxed_2802_, v_stop_boxed_2803_, v_b_2801_);
lean_dec_ref(v_as_2798_);
lean_dec_ref(v_linterOpts_2797_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2807_, lean_object* v_as_2808_, size_t v_i_2809_, size_t v_stop_2810_, lean_object* v_b_2811_){
_start:
{
lean_object* v___y_2813_; uint8_t v___x_2817_; 
v___x_2817_ = lean_usize_dec_eq(v_i_2809_, v_stop_2810_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v_fst_2819_; lean_object* v_snd_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2844_; 
v___x_2818_ = lean_array_uget(v_as_2808_, v_i_2809_);
v_fst_2819_ = lean_ctor_get(v___x_2818_, 0);
v_snd_2820_ = lean_ctor_get(v___x_2818_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2822_ = v___x_2818_;
v_isShared_2823_ = v_isSharedCheck_2844_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_snd_2820_);
lean_inc(v_fst_2819_);
lean_dec(v___x_2818_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2844_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___y_2825_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = lean_array_get_size(v_snd_2820_);
v___x_2835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2836_ = lean_nat_dec_lt(v___x_2833_, v___x_2834_);
if (v___x_2836_ == 0)
{
lean_dec(v_snd_2820_);
v___y_2825_ = v___x_2835_;
goto v___jp_2824_;
}
else
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_le(v___x_2834_, v___x_2834_);
if (v___x_2837_ == 0)
{
if (v___x_2836_ == 0)
{
lean_dec(v_snd_2820_);
v___y_2825_ = v___x_2835_;
goto v___jp_2824_;
}
else
{
size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = lean_usize_of_nat(v___x_2834_);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2807_, v_snd_2820_, v___x_2838_, v___x_2839_, v___x_2835_);
lean_dec(v_snd_2820_);
v___y_2825_ = v___x_2840_;
goto v___jp_2824_;
}
}
else
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = lean_usize_of_nat(v___x_2834_);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2807_, v_snd_2820_, v___x_2841_, v___x_2842_, v___x_2835_);
lean_dec(v_snd_2820_);
v___y_2825_ = v___x_2843_;
goto v___jp_2824_;
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2826_ = lean_array_get_size(v___y_2825_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v___x_2828_ = lean_nat_dec_eq(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2830_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v___y_2825_);
v___x_2830_ = v___x_2822_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_fst_2819_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___y_2825_);
v___x_2830_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_array_push(v_b_2811_, v___x_2830_);
v___y_2813_ = v___x_2831_;
goto v___jp_2812_;
}
}
else
{
lean_dec_ref(v___y_2825_);
lean_del_object(v___x_2822_);
lean_dec(v_fst_2819_);
v___y_2813_ = v_b_2811_;
goto v___jp_2812_;
}
}
}
}
else
{
return v_b_2811_;
}
v___jp_2812_:
{
size_t v___x_2814_; size_t v___x_2815_; 
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2809_, v___x_2814_);
v_i_2809_ = v___x_2815_;
v_b_2811_ = v___y_2813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2845_, lean_object* v_as_2846_, lean_object* v_i_2847_, lean_object* v_stop_2848_, lean_object* v_b_2849_){
_start:
{
size_t v_i_boxed_2850_; size_t v_stop_boxed_2851_; lean_object* v_res_2852_; 
v_i_boxed_2850_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_stop_boxed_2851_ = lean_unbox_usize(v_stop_2848_);
lean_dec(v_stop_2848_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2845_, v_as_2846_, v_i_boxed_2850_, v_stop_boxed_2851_, v_b_2849_);
lean_dec_ref(v_as_2846_);
lean_dec_ref(v_linterOpts_2845_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2853_, lean_object* v_as_2854_, lean_object* v_start_2855_, lean_object* v_stop_2856_){
_start:
{
lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2858_ = lean_nat_dec_lt(v_start_2855_, v_stop_2856_);
if (v___x_2858_ == 0)
{
return v___x_2857_;
}
else
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = lean_array_get_size(v_as_2854_);
v___x_2860_ = lean_nat_dec_le(v_stop_2856_, v___x_2859_);
if (v___x_2860_ == 0)
{
uint8_t v___x_2861_; 
v___x_2861_ = lean_nat_dec_lt(v_start_2855_, v___x_2859_);
if (v___x_2861_ == 0)
{
return v___x_2857_;
}
else
{
size_t v___x_2862_; size_t v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = lean_usize_of_nat(v_start_2855_);
v___x_2863_ = lean_usize_of_nat(v___x_2859_);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2853_, v_as_2854_, v___x_2862_, v___x_2863_, v___x_2857_);
return v___x_2864_;
}
}
else
{
size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_usize_of_nat(v_start_2855_);
v___x_2866_ = lean_usize_of_nat(v_stop_2856_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2853_, v_as_2854_, v___x_2865_, v___x_2866_, v___x_2857_);
return v___x_2867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2868_, lean_object* v_as_2869_, lean_object* v_start_2870_, lean_object* v_stop_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2868_, v_as_2869_, v_start_2870_, v_stop_2871_);
lean_dec(v_stop_2871_);
lean_dec(v_start_2870_);
lean_dec_ref(v_as_2869_);
lean_dec_ref(v_linterOpts_2868_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2873_, lean_object* v_init_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v_k_2877_; lean_object* v_v_2878_; lean_object* v_l_2879_; lean_object* v_r_2880_; lean_object* v___x_2881_; lean_object* v_a_2882_; lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2897_; 
v_k_2877_ = lean_ctor_get(v_x_2875_, 1);
lean_inc(v_k_2877_);
v_v_2878_ = lean_ctor_get(v_x_2875_, 2);
lean_inc(v_v_2878_);
v_l_2879_ = lean_ctor_get(v_x_2875_, 3);
lean_inc(v_l_2879_);
v_r_2880_ = lean_ctor_get(v_x_2875_, 4);
lean_inc(v_r_2880_);
lean_dec_ref_known(v_x_2875_, 5);
lean_inc(v_fst_2873_);
v___x_2881_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2873_, v_init_2874_, v_l_2879_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
v_a_2883_ = lean_ctor_get(v_a_2882_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_a_2882_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2885_ = v_a_2882_;
v_isShared_2886_ = v_isSharedCheck_2897_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v_a_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2897_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
uint8_t v_anyUnlocated_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v_anyUnlocated_2887_ = 1;
v___x_2888_ = l_Lean_Name_toString(v_k_2877_, v_anyUnlocated_2887_);
lean_inc(v_fst_2873_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 0);
lean_ctor_set(v___x_2885_, 0, v_fst_2873_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_fst_2873_);
v___x_2890_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
double v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_float_of_nat(v_v_2878_);
v___x_2892_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2888_);
lean_ctor_set(v___x_2893_, 1, v___x_2890_);
lean_ctor_set(v___x_2893_, 2, v___x_2892_);
v___x_2894_ = lean_array_push(v_a_2883_, v___x_2893_);
v_init_2874_ = v___x_2894_;
v_x_2875_ = v_r_2880_;
goto _start;
}
}
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec(v_fst_2873_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_init_2874_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2900_, lean_object* v_init_2901_, lean_object* v_x_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2900_, v_init_2901_, v_x_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(lean_object* v_t_2905_, lean_object* v_k_2906_, lean_object* v_fallback_2907_){
_start:
{
if (lean_obj_tag(v_t_2905_) == 0)
{
lean_object* v_k_2908_; lean_object* v_v_2909_; lean_object* v_l_2910_; lean_object* v_r_2911_; uint8_t v___x_2912_; 
v_k_2908_ = lean_ctor_get(v_t_2905_, 1);
v_v_2909_ = lean_ctor_get(v_t_2905_, 2);
v_l_2910_ = lean_ctor_get(v_t_2905_, 3);
v_r_2911_ = lean_ctor_get(v_t_2905_, 4);
v___x_2912_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2906_, v_k_2908_);
switch(v___x_2912_)
{
case 0:
{
v_t_2905_ = v_l_2910_;
goto _start;
}
case 1:
{
lean_inc(v_v_2909_);
return v_v_2909_;
}
default: 
{
v_t_2905_ = v_r_2911_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2907_);
return v_fallback_2907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg___boxed(lean_object* v_t_2915_, lean_object* v_k_2916_, lean_object* v_fallback_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_t_2915_, v_k_2916_, v_fallback_2917_);
lean_dec(v_fallback_2917_);
lean_dec(v_k_2916_);
lean_dec(v_t_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2919_, size_t v_i_2920_, size_t v_stop_2921_, lean_object* v_b_2922_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_usize_dec_eq(v_i_2920_, v_stop_2921_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v_linter_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; 
v___x_2924_ = lean_array_uget_borrowed(v_as_2919_, v_i_2920_);
v_linter_2925_ = lean_ctor_get(v___x_2924_, 0);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_b_2922_, v_linter_2925_, v___x_2926_);
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_add(v___x_2927_, v___x_2928_);
lean_dec(v___x_2927_);
lean_inc(v_linter_2925_);
v___x_2930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2925_, v___x_2929_, v_b_2922_);
v___x_2931_ = ((size_t)1ULL);
v___x_2932_ = lean_usize_add(v_i_2920_, v___x_2931_);
v_i_2920_ = v___x_2932_;
v_b_2922_ = v___x_2930_;
goto _start;
}
else
{
return v_b_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2934_, lean_object* v_i_2935_, lean_object* v_stop_2936_, lean_object* v_b_2937_){
_start:
{
size_t v_i_boxed_2938_; size_t v_stop_boxed_2939_; lean_object* v_res_2940_; 
v_i_boxed_2938_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_stop_boxed_2939_ = lean_unbox_usize(v_stop_2936_);
lean_dec(v_stop_2936_);
v_res_2940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2934_, v_i_boxed_2938_, v_stop_boxed_2939_, v_b_2937_);
lean_dec_ref(v_as_2934_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2941_, size_t v_sz_2942_, size_t v_i_2943_, lean_object* v_b_2944_){
_start:
{
lean_object* v_a_2947_; uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_lt(v_i_2943_, v_sz_2942_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_b_2944_);
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v_fst_2954_; lean_object* v_snd_2955_; lean_object* v___y_2957_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v_a_2953_ = lean_array_uget_borrowed(v_as_2941_, v_i_2943_);
v_fst_2954_ = lean_ctor_get(v_a_2953_, 0);
v_snd_2955_ = lean_ctor_get(v_a_2953_, 1);
v___x_2979_ = lean_box(1);
v___x_2980_ = lean_unsigned_to_nat(0u);
v___x_2981_ = lean_array_get_size(v_snd_2955_);
v___x_2982_ = lean_nat_dec_lt(v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
v___y_2957_ = v___x_2979_;
goto v___jp_2956_;
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_nat_dec_le(v___x_2981_, v___x_2981_);
if (v___x_2983_ == 0)
{
if (v___x_2982_ == 0)
{
v___y_2957_ = v___x_2979_;
goto v___jp_2956_;
}
else
{
size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = ((size_t)0ULL);
v___x_2985_ = lean_usize_of_nat(v___x_2981_);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2955_, v___x_2984_, v___x_2985_, v___x_2979_);
v___y_2957_ = v___x_2986_;
goto v___jp_2956_;
}
}
else
{
size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = lean_usize_of_nat(v___x_2981_);
v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2955_, v___x_2987_, v___x_2988_, v___x_2979_);
v___y_2957_ = v___x_2989_;
goto v___jp_2956_;
}
}
v___jp_2956_:
{
lean_object* v___x_2958_; 
lean_inc(v_fst_2954_);
v___x_2958_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2954_, v_b_2944_, v___y_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_a_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_a_2960_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_a_2960_);
lean_dec(v_a_2959_);
v_a_2947_ = v_a_2960_;
goto v___jp_2946_;
}
else
{
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2970_; 
v_a_2961_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2963_ = v___x_2958_;
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2958_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
if (lean_obj_tag(v_a_2961_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v_a_2961_, 1);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 0);
lean_ctor_set(v___x_2963_, 0, v_a_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
else
{
lean_object* v_a_2969_; 
lean_del_object(v___x_2963_);
v_a_2969_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_a_2961_, 1);
v_a_2947_ = v_a_2969_;
goto v___jp_2946_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2958_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2958_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
v___jp_2946_:
{
size_t v___x_2948_; size_t v___x_2949_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2943_, v___x_2948_);
v_i_2943_ = v___x_2949_;
v_b_2944_ = v_a_2947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2990_, lean_object* v_sz_2991_, lean_object* v_i_2992_, lean_object* v_b_2993_, lean_object* v___y_2994_){
_start:
{
size_t v_sz_boxed_2995_; size_t v_i_boxed_2996_; lean_object* v_res_2997_; 
v_sz_boxed_2995_ = lean_unbox_usize(v_sz_2991_);
lean_dec(v_sz_2991_);
v_i_boxed_2996_ = lean_unbox_usize(v_i_2992_);
lean_dec(v_i_2992_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2990_, v_sz_boxed_2995_, v_i_boxed_2996_, v_b_2993_);
lean_dec_ref(v_as_2990_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2998_, size_t v_sz_2999_, size_t v_i_3000_, lean_object* v_b_3001_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_usize_dec_lt(v_i_3000_, v_sz_2999_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_b_3001_);
return v___x_3004_;
}
else
{
lean_object* v_a_3005_; lean_object* v_message_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3005_ = lean_array_uget_borrowed(v_as_2998_, v_i_3000_);
v_message_3006_ = lean_ctor_get(v_a_3005_, 1);
v___x_3007_ = 0;
lean_inc_ref(v_message_3006_);
v___x_3008_ = l_Lean_SerialMessage_toString(v_message_3006_, v___x_3007_);
v___x_3009_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; size_t v___x_3011_; size_t v___x_3012_; 
lean_dec_ref_known(v___x_3009_, 1);
v___x_3010_ = lean_box(0);
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_add(v_i_3000_, v___x_3011_);
v_i_3000_ = v___x_3012_;
v_b_3001_ = v___x_3010_;
goto _start;
}
else
{
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_3014_, lean_object* v_sz_3015_, lean_object* v_i_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_){
_start:
{
size_t v_sz_boxed_3019_; size_t v_i_boxed_3020_; lean_object* v_res_3021_; 
v_sz_boxed_3019_ = lean_unbox_usize(v_sz_3015_);
lean_dec(v_sz_3015_);
v_i_boxed_3020_ = lean_unbox_usize(v_i_3016_);
lean_dec(v_i_3016_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_3014_, v_sz_boxed_3019_, v_i_boxed_3020_, v_b_3017_);
lean_dec_ref(v_as_3014_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3024_, size_t v_sz_3025_, size_t v_i_3026_, lean_object* v_b_3027_){
_start:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_usize_dec_lt(v_i_3026_, v_sz_3025_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_b_3027_);
return v___x_3030_;
}
else
{
lean_object* v_a_3031_; lean_object* v_fst_3032_; lean_object* v_snd_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v_a_3031_ = lean_array_uget_borrowed(v_as_3024_, v_i_3026_);
v_fst_3032_ = lean_ctor_get(v_a_3031_, 0);
v_snd_3033_ = lean_ctor_get(v_a_3031_, 1);
v___x_3034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3032_);
v___x_3035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3032_, v___x_3029_);
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3038_ = lean_string_append(v___x_3036_, v___x_3037_);
v___x_3039_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3038_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v___x_3040_; size_t v_sz_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
lean_dec_ref_known(v___x_3039_, 1);
v___x_3040_ = lean_box(0);
v_sz_3041_ = lean_array_size(v_snd_3033_);
v___x_3042_ = ((size_t)0ULL);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3033_, v_sz_3041_, v___x_3042_, v___x_3040_);
if (lean_obj_tag(v___x_3043_) == 0)
{
size_t v___x_3044_; size_t v___x_3045_; 
lean_dec_ref_known(v___x_3043_, 1);
v___x_3044_ = ((size_t)1ULL);
v___x_3045_ = lean_usize_add(v_i_3026_, v___x_3044_);
v_i_3026_ = v___x_3045_;
v_b_3027_ = v___x_3040_;
goto _start;
}
else
{
return v___x_3043_;
}
}
else
{
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3047_, lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3047_, v_sz_boxed_3052_, v_i_boxed_3053_, v_b_3050_);
lean_dec_ref(v_as_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3061_, lean_object* v_linterOpts_3062_, lean_object* v_env_3063_, lean_object* v_mod_3064_){
_start:
{
uint8_t v_lintOnly_3066_; uint8_t v_mode_3067_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3138_; lean_object* v___x_3144_; lean_object* v_textGroups_3145_; 
v_lintOnly_3066_ = lean_ctor_get_uint8(v_args_3061_, sizeof(void*)*3);
v_mode_3067_ = lean_ctor_get_uint8(v_args_3061_, sizeof(void*)*3 + 1);
v___x_3144_ = l_Lean_Name_getRoot(v_mod_3064_);
v_textGroups_3145_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3063_, v___x_3144_);
lean_dec(v___x_3144_);
if (v_lintOnly_3066_ == 0)
{
v___y_3138_ = v_textGroups_3145_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_array_get_size(v_textGroups_3145_);
v___x_3148_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3062_, v_textGroups_3145_, v___x_3146_, v___x_3147_);
lean_dec_ref(v_textGroups_3145_);
v___y_3138_ = v___x_3148_;
goto v___jp_3137_;
}
v___jp_3068_:
{
switch(v_mode_3067_)
{
case 0:
{
lean_object* v___x_3071_; size_t v_sz_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = lean_box(0);
v_sz_3072_ = lean_array_size(v___y_3069_);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3069_, v_sz_3072_, v___x_3073_, v___x_3071_);
lean_dec_ref(v___y_3069_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3082_; 
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v___x_3074_, 0);
lean_dec(v_unused_3083_);
v___x_3076_ = v___x_3074_;
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v___x_3074_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3078_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3078_, 0, v___y_3070_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3078_);
v___x_3080_ = v___x_3076_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
v_a_3084_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3074_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3074_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
case 1:
{
lean_object* v___x_3092_; size_t v_sz_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3092_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3093_ = lean_array_size(v___y_3069_);
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3069_, v_sz_3093_, v___x_3094_, v___x_3092_);
lean_dec_ref(v___y_3069_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3107_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3107_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3107_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_fst_3100_; lean_object* v_snd_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3105_; 
v_fst_3100_ = lean_ctor_get(v_a_3096_, 0);
lean_inc(v_fst_3100_);
v_snd_3101_ = lean_ctor_get(v_a_3096_, 1);
lean_inc(v_snd_3101_);
lean_dec(v_a_3096_);
v___x_3102_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3102_, 0, v_fst_3100_);
v___x_3103_ = lean_unbox(v_snd_3101_);
lean_dec(v_snd_3101_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*1, v___x_3103_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3102_);
v___x_3105_ = v___x_3098_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3102_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
v_a_3108_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3095_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3095_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
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
default: 
{
lean_object* v_codeQualityEntries_3116_; size_t v_sz_3117_; size_t v___x_3118_; lean_object* v___x_3119_; 
v_codeQualityEntries_3116_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1));
v_sz_3117_ = lean_array_size(v___y_3069_);
v___x_3118_ = ((size_t)0ULL);
v___x_3119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3069_, v_sz_3117_, v___x_3118_, v_codeQualityEntries_3116_);
lean_dec_ref(v___y_3069_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3128_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_a_3129_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3119_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3119_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
v___jp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3139_ = lean_array_get_size(v___y_3138_);
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_nat_dec_eq(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
uint8_t v___x_3142_; 
v___x_3142_ = 1;
v___y_3069_ = v___y_3138_;
v___y_3070_ = v___x_3142_;
goto v___jp_3068_;
}
else
{
uint8_t v___x_3143_; 
v___x_3143_ = 0;
v___y_3069_ = v___y_3138_;
v___y_3070_ = v___x_3143_;
goto v___jp_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3149_, lean_object* v_linterOpts_3150_, lean_object* v_env_3151_, lean_object* v_mod_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3149_, v_linterOpts_3150_, v_env_3151_, v_mod_3152_);
lean_dec(v_mod_3152_);
lean_dec_ref(v_env_3151_);
lean_dec_ref(v_linterOpts_3150_);
lean_dec_ref(v_args_3149_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_00_u03b4_3155_, lean_object* v_t_3156_, lean_object* v_k_3157_, lean_object* v_fallback_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_t_3156_, v_k_3157_, v_fallback_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_00_u03b4_3160_, lean_object* v_t_3161_, lean_object* v_k_3162_, lean_object* v_fallback_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_00_u03b4_3160_, v_t_3161_, v_k_3162_, v_fallback_3163_);
lean_dec(v_fallback_3163_);
lean_dec(v_k_3162_);
lean_dec(v_t_3161_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3165_, lean_object* v_____r_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3170_, 0, v___y_3165_);
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3172_, lean_object* v_____r_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___y_16313__boxed_3177_; lean_object* v_res_3178_; 
v___y_16313__boxed_3177_ = lean_unbox(v___y_3172_);
v_res_3178_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16313__boxed_3177_, v_____r_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2(lean_object* v_b_3179_, lean_object* v_acc_3180_, lean_object* v_i_3181_){
_start:
{
lean_object* v_keyArray_3186_; lean_object* v_valueArray_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_keyArray_3186_ = lean_ctor_get(v_b_3179_, 1);
v_valueArray_3187_ = lean_ctor_get(v_b_3179_, 2);
v___x_3188_ = lean_array_get_size(v_keyArray_3186_);
v___x_3189_ = lean_nat_dec_lt(v_i_3181_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec(v_i_3181_);
return v_acc_3180_;
}
else
{
lean_object* v___x_3190_; uint8_t v_isSome_3191_; 
v___x_3190_ = lean_array_fget_borrowed(v_keyArray_3186_, v_i_3181_);
v_isSome_3191_ = lean_noption_is_some(v___x_3190_);
if (v_isSome_3191_ == 0)
{
goto v___jp_3182_;
}
else
{
lean_object* v___x_3192_; uint8_t v_isSome_3193_; 
v___x_3192_ = lean_array_fget_borrowed(v_valueArray_3187_, v_i_3181_);
v_isSome_3193_ = lean_noption_is_some(v___x_3192_);
if (v_isSome_3193_ == 0)
{
goto v___jp_3182_;
}
else
{
lean_object* v_val_3194_; lean_object* v_val_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_inc(v___x_3190_);
v_val_3194_ = lean_noption_get(v___x_3190_);
lean_inc(v___x_3192_);
v_val_3195_ = lean_noption_get(v___x_3192_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v_val_3194_);
lean_ctor_set(v___x_3196_, 1, v_val_3195_);
v___x_3197_ = lean_array_push(v_acc_3180_, v___x_3196_);
v___x_3198_ = lean_unsigned_to_nat(1u);
v___x_3199_ = lean_nat_add(v_i_3181_, v___x_3198_);
lean_dec(v_i_3181_);
v_acc_3180_ = v___x_3197_;
v_i_3181_ = v___x_3199_;
goto _start;
}
}
}
v___jp_3182_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3184_ = lean_nat_add(v_i_3181_, v___x_3183_);
lean_dec(v_i_3181_);
v_i_3181_ = v___x_3184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2___boxed(lean_object* v_b_3201_, lean_object* v_acc_3202_, lean_object* v_i_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2(v_b_3201_, v_acc_3202_, v_i_3203_);
lean_dec_ref(v_b_3201_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_init_3205_, lean_object* v_b_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1_spec__2(v_b_3206_, v_init_3205_, v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_init_3209_, lean_object* v_b_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_init_3209_, v_b_3210_);
lean_dec_ref(v_b_3210_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(lean_object* v_fst_3212_, lean_object* v_init_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_object* v_k_3216_; lean_object* v_v_3217_; lean_object* v_l_3218_; lean_object* v_r_3219_; lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v_a_3222_; lean_object* v_fst_3223_; lean_object* v_snd_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3239_; 
v_k_3216_ = lean_ctor_get(v_x_3214_, 1);
lean_inc(v_k_3216_);
v_v_3217_ = lean_ctor_get(v_x_3214_, 2);
lean_inc(v_v_3217_);
v_l_3218_ = lean_ctor_get(v_x_3214_, 3);
lean_inc(v_l_3218_);
v_r_3219_ = lean_ctor_get(v_x_3214_, 4);
lean_inc(v_r_3219_);
lean_dec_ref_known(v_x_3214_, 5);
lean_inc_ref(v_fst_3212_);
v___x_3220_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(v_fst_3212_, v_init_3213_, v_l_3218_);
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
v_a_3222_ = lean_ctor_get(v_a_3221_, 0);
lean_inc(v_a_3222_);
lean_dec(v_a_3221_);
v_fst_3223_ = lean_ctor_get(v_k_3216_, 0);
v_snd_3224_ = lean_ctor_get(v_k_3216_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_k_3216_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3226_ = v_k_3216_;
v_isShared_3227_ = v_isSharedCheck_3239_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snd_3224_);
lean_inc(v_fst_3223_);
lean_dec(v_k_3216_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3239_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_optName_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v_optName_3228_ = lean_ctor_get(v_fst_3212_, 1);
v___x_3229_ = 1;
lean_inc(v_optName_3228_);
v___x_3230_ = l_Lean_Name_toString(v_optName_3228_, v___x_3229_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set_tag(v___x_3226_, 1);
v___x_3232_ = v___x_3226_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_fst_3223_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_snd_3224_);
v___x_3232_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
double v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3233_ = lean_float_of_nat(v_v_3217_);
v___x_3234_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_3234_, 0, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3230_);
lean_ctor_set(v___x_3235_, 1, v___x_3232_);
lean_ctor_set(v___x_3235_, 2, v___x_3234_);
v___x_3236_ = lean_array_push(v_a_3222_, v___x_3235_);
v_init_3213_ = v___x_3236_;
v_x_3214_ = v_r_3219_;
goto _start;
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_dec_ref(v_fst_3212_);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_init_3213_);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg___boxed(lean_object* v_fst_3242_, lean_object* v_init_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(v_fst_3242_, v_init_3243_, v_x_3244_);
return v_res_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__0);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
lean_ctor_set(v___x_3252_, 2, v___x_3251_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
lean_ctor_set(v___x_3252_, 4, v___x_3250_);
lean_ctor_set(v___x_3252_, 5, v___x_3250_);
lean_ctor_set(v___x_3252_, 6, v___x_3250_);
lean_ctor_set(v___x_3252_, 7, v___x_3250_);
lean_ctor_set(v___x_3252_, 8, v___x_3250_);
lean_ctor_set(v___x_3252_, 9, v___x_3250_);
lean_ctor_set(v___x_3252_, 10, v___x_3250_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_unsigned_to_nat(32u);
v___x_3254_ = lean_mk_empty_array_with_capacity(v___x_3253_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4(void){
_start:
{
size_t v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3256_ = ((size_t)5ULL);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_unsigned_to_nat(32u);
v___x_3259_ = lean_mk_empty_array_with_capacity(v___x_3258_);
v___x_3260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3261_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___x_3259_);
lean_ctor_set(v___x_3261_, 2, v___x_3257_);
lean_ctor_set(v___x_3261_, 3, v___x_3257_);
lean_ctor_set_usize(v___x_3261_, 4, v___x_3256_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3262_ = lean_box(1);
v___x_3263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__4);
v___x_3264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3263_);
lean_ctor_set(v___x_3265_, 2, v___x_3262_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3268_ = l_Lean_stringToMessageData(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__14));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__16));
v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__18));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3287_, lean_object* v_declHint_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v_env_3292_; uint8_t v___x_3293_; 
v___x_3291_ = lean_st_ref_get(v___y_3289_);
v_env_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc_ref(v_env_3292_);
lean_dec(v___x_3291_);
v___x_3293_ = l_Lean_Name_isAnonymous(v_declHint_3288_);
if (v___x_3293_ == 0)
{
uint8_t v_isExporting_3294_; 
v_isExporting_3294_ = lean_ctor_get_uint8(v_env_3292_, sizeof(void*)*8);
if (v_isExporting_3294_ == 0)
{
lean_object* v___x_3295_; 
lean_dec_ref(v_env_3292_);
lean_dec(v_declHint_3288_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_msg_3287_);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; uint8_t v___x_3297_; 
lean_inc_ref(v_env_3292_);
v___x_3296_ = l_Lean_Environment_setExporting(v_env_3292_, v___x_3293_);
lean_inc(v_declHint_3288_);
lean_inc_ref(v___x_3296_);
v___x_3297_ = l_Lean_Environment_contains(v___x_3296_, v_declHint_3288_, v_isExporting_3294_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
lean_dec_ref(v___x_3296_);
lean_dec_ref(v_env_3292_);
lean_dec(v_declHint_3288_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_msg_3287_);
return v___x_3298_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v_c_3304_; lean_object* v___x_3305_; 
v___x_3299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2);
v___x_3300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3301_ = l_Lean_Options_empty;
v___x_3302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3296_);
lean_ctor_set(v___x_3302_, 1, v___x_3299_);
lean_ctor_set(v___x_3302_, 2, v___x_3300_);
lean_ctor_set(v___x_3302_, 3, v___x_3301_);
lean_inc(v_declHint_3288_);
v___x_3303_ = l_Lean_MessageData_ofConstName(v_declHint_3288_, v___x_3293_);
v_c_3304_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3304_, 0, v___x_3302_);
lean_ctor_set(v_c_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3292_, v_declHint_3288_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_dec_ref(v_env_3292_);
lean_dec(v_declHint_3288_);
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v_c_3304_);
v___x_3308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_note(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_msg_3287_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
else
{
lean_object* v_val_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3348_; 
v_val_3313_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3315_ = v___x_3305_;
v_isShared_3316_ = v_isSharedCheck_3348_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_val_3313_);
lean_dec(v___x_3305_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3348_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_mod_3320_; uint8_t v___x_3321_; 
v___x_3317_ = lean_box(0);
v___x_3318_ = l_Lean_Environment_header(v_env_3292_);
lean_dec_ref(v_env_3292_);
v___x_3319_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3318_);
v_mod_3320_ = lean_array_get(v___x_3317_, v___x_3319_, v_val_3313_);
lean_dec(v_val_3313_);
lean_dec_ref(v___x_3319_);
v___x_3321_ = l_Lean_isPrivateName(v_declHint_3288_);
lean_dec(v_declHint_3288_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v_c_3304_);
v___x_3324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = l_Lean_MessageData_ofName(v_mod_3320_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__15);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_MessageData_note(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_msg_3287_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3331_);
v___x_3333_ = v___x_3315_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v_c_3304_);
v___x_3337_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__17);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_MessageData_ofName(v_mod_3320_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__19);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = l_Lean_MessageData_note(v___x_3342_);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_msg_3287_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3344_);
v___x_3346_ = v___x_3315_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3349_; 
lean_dec_ref(v_env_3292_);
lean_dec(v_declHint_3288_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_msg_3287_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3350_, lean_object* v_declHint_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg(v_msg_3350_, v_declHint_3351_, v___y_3352_);
lean_dec(v___y_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14(lean_object* v_msg_3355_, lean_object* v_declHint_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3370_; 
v___x_3360_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg(v_msg_3355_, v_declHint_3356_, v___y_3358_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3370_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3370_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3365_ = l_Lean_unknownIdentifierMessageTag;
v___x_3366_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_a_3361_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3366_);
v___x_3368_ = v___x_3363_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14___boxed(lean_object* v_msg_3371_, lean_object* v_declHint_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14(v_msg_3371_, v_declHint_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v_env_3382_; lean_object* v_options_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3381_ = lean_st_ref_get(v___y_3379_);
v_env_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc_ref(v_env_3382_);
lean_dec(v___x_3381_);
v_options_3383_ = lean_ctor_get(v___y_3378_, 2);
v___x_3384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__2);
v___x_3385_ = lean_unsigned_to_nat(32u);
v___x_3386_ = lean_mk_empty_array_with_capacity(v___x_3385_);
lean_dec_ref(v___x_3386_);
v___x_3387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg___closed__5);
lean_inc_ref(v_options_3383_);
v___x_3388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3388_, 0, v_env_3382_);
lean_ctor_set(v___x_3388_, 1, v___x_3384_);
lean_ctor_set(v___x_3388_, 2, v___x_3387_);
lean_ctor_set(v___x_3388_, 3, v_options_3383_);
v___x_3389_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v_msgData_3377_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18(v_msgData_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_ref_3400_; lean_object* v___x_3401_; lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3410_; 
v_ref_3400_ = lean_ctor_get(v___y_3397_, 5);
v___x_3401_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17_spec__18(v_msg_3396_, v___y_3397_, v___y_3398_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3410_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3410_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_inc(v_ref_3400_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_ref_3400_);
lean_ctor_set(v___x_3406_, 1, v_a_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 1);
lean_ctor_set(v___x_3404_, 0, v___x_3406_);
v___x_3408_ = v___x_3404_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg(v_msg_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg(lean_object* v_ref_3416_, lean_object* v_msg_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_fileName_3421_; lean_object* v_fileMap_3422_; lean_object* v_options_3423_; lean_object* v_currRecDepth_3424_; lean_object* v_maxRecDepth_3425_; lean_object* v_ref_3426_; lean_object* v_currNamespace_3427_; lean_object* v_openDecls_3428_; lean_object* v_initHeartbeats_3429_; lean_object* v_maxHeartbeats_3430_; lean_object* v_quotContext_3431_; lean_object* v_currMacroScope_3432_; uint8_t v_diag_3433_; lean_object* v_cancelTk_x3f_3434_; uint8_t v_suppressElabErrors_3435_; lean_object* v_inheritedTraceOptions_3436_; lean_object* v_ref_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_fileName_3421_ = lean_ctor_get(v___y_3418_, 0);
v_fileMap_3422_ = lean_ctor_get(v___y_3418_, 1);
v_options_3423_ = lean_ctor_get(v___y_3418_, 2);
v_currRecDepth_3424_ = lean_ctor_get(v___y_3418_, 3);
v_maxRecDepth_3425_ = lean_ctor_get(v___y_3418_, 4);
v_ref_3426_ = lean_ctor_get(v___y_3418_, 5);
v_currNamespace_3427_ = lean_ctor_get(v___y_3418_, 6);
v_openDecls_3428_ = lean_ctor_get(v___y_3418_, 7);
v_initHeartbeats_3429_ = lean_ctor_get(v___y_3418_, 8);
v_maxHeartbeats_3430_ = lean_ctor_get(v___y_3418_, 9);
v_quotContext_3431_ = lean_ctor_get(v___y_3418_, 10);
v_currMacroScope_3432_ = lean_ctor_get(v___y_3418_, 11);
v_diag_3433_ = lean_ctor_get_uint8(v___y_3418_, sizeof(void*)*14);
v_cancelTk_x3f_3434_ = lean_ctor_get(v___y_3418_, 12);
v_suppressElabErrors_3435_ = lean_ctor_get_uint8(v___y_3418_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3436_ = lean_ctor_get(v___y_3418_, 13);
v_ref_3437_ = l_Lean_replaceRef(v_ref_3416_, v_ref_3426_);
lean_inc_ref(v_inheritedTraceOptions_3436_);
lean_inc(v_cancelTk_x3f_3434_);
lean_inc(v_currMacroScope_3432_);
lean_inc(v_quotContext_3431_);
lean_inc(v_maxHeartbeats_3430_);
lean_inc(v_initHeartbeats_3429_);
lean_inc(v_openDecls_3428_);
lean_inc(v_currNamespace_3427_);
lean_inc(v_maxRecDepth_3425_);
lean_inc(v_currRecDepth_3424_);
lean_inc_ref(v_options_3423_);
lean_inc_ref(v_fileMap_3422_);
lean_inc_ref(v_fileName_3421_);
v___x_3438_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3438_, 0, v_fileName_3421_);
lean_ctor_set(v___x_3438_, 1, v_fileMap_3422_);
lean_ctor_set(v___x_3438_, 2, v_options_3423_);
lean_ctor_set(v___x_3438_, 3, v_currRecDepth_3424_);
lean_ctor_set(v___x_3438_, 4, v_maxRecDepth_3425_);
lean_ctor_set(v___x_3438_, 5, v_ref_3437_);
lean_ctor_set(v___x_3438_, 6, v_currNamespace_3427_);
lean_ctor_set(v___x_3438_, 7, v_openDecls_3428_);
lean_ctor_set(v___x_3438_, 8, v_initHeartbeats_3429_);
lean_ctor_set(v___x_3438_, 9, v_maxHeartbeats_3430_);
lean_ctor_set(v___x_3438_, 10, v_quotContext_3431_);
lean_ctor_set(v___x_3438_, 11, v_currMacroScope_3432_);
lean_ctor_set(v___x_3438_, 12, v_cancelTk_x3f_3434_);
lean_ctor_set(v___x_3438_, 13, v_inheritedTraceOptions_3436_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*14, v_diag_3433_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*14 + 1, v_suppressElabErrors_3435_);
v___x_3439_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg(v_msg_3417_, v___x_3438_, v___y_3419_);
lean_dec_ref_known(v___x_3438_, 14);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3440_, lean_object* v_msg_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg(v_ref_3440_, v_msg_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v_ref_3440_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg(lean_object* v_ref_3446_, lean_object* v_msg_3447_, lean_object* v_declHint_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v_a_3453_; lean_object* v___x_3454_; 
v___x_3452_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14(v_msg_3447_, v_declHint_3448_, v___y_3449_, v___y_3450_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg(v_ref_3446_, v_a_3453_, v___y_3449_, v___y_3450_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3455_, lean_object* v_msg_3456_, lean_object* v_declHint_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg(v_ref_3455_, v_msg_3456_, v_declHint_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v_ref_3455_);
return v_res_3461_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__0));
v___x_3464_ = l_Lean_stringToMessageData(v___x_3463_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg(lean_object* v_ref_3467_, lean_object* v_constName_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3472_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__1);
v___x_3473_ = 0;
lean_inc(v_constName_3468_);
v___x_3474_ = l_Lean_MessageData_ofConstName(v_constName_3468_, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3472_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___closed__2);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg(v_ref_3467_, v___x_3477_, v_constName_3468_, v___y_3469_, v___y_3470_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg___boxed(lean_object* v_ref_3479_, lean_object* v_constName_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg(v_ref_3479_, v_constName_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_ref_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_ref_3489_; lean_object* v___x_3490_; 
v_ref_3489_ = lean_ctor_get(v___y_3486_, 5);
v___x_3490_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg(v_ref_3489_, v_constName_3485_, v___y_3486_, v___y_3487_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; lean_object* v_env_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3500_ = lean_st_ref_get(v___y_3498_);
v_env_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc_ref(v_env_3501_);
lean_dec(v___x_3500_);
v___x_3502_ = 0;
lean_inc(v_constName_3496_);
v___x_3503_ = l_Lean_Environment_find_x3f(v_env_3501_, v_constName_3496_, v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3496_, v___y_3497_, v___y_3498_);
return v___x_3504_;
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_constName_3496_);
v_val_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_val_3505_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set_tag(v___x_3507_, 0);
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_val_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
lean_inc(v_declName_3518_);
v___x_3522_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3549_; 
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v___x_3522_, 0);
lean_dec(v_unused_3550_);
v___x_3524_ = v___x_3522_;
v_isShared_3525_ = v_isSharedCheck_3549_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v___x_3522_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3549_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v_env_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_st_ref_get(v___y_3520_);
v_env_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc_ref(v_env_3527_);
lean_dec(v___x_3526_);
v___x_3528_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3527_, v_declName_3518_);
lean_dec(v_declName_3518_);
lean_dec_ref(v_env_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_box(0);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3529_);
v___x_3531_ = v___x_3524_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
else
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3548_; 
v_val_3533_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3535_ = v___x_3528_;
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v___x_3528_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v_env_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3537_ = lean_st_ref_get(v___y_3520_);
v_env_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc_ref(v_env_3538_);
lean_dec(v___x_3537_);
v___x_3539_ = lean_box(0);
v___x_3540_ = l_Lean_Environment_allImportedModuleNames(v_env_3538_);
lean_dec_ref(v_env_3538_);
v___x_3541_ = lean_array_get(v___x_3539_, v___x_3540_, v_val_3533_);
lean_dec(v_val_3533_);
lean_dec_ref(v___x_3540_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3541_);
v___x_3543_ = v___x_3535_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3543_);
v___x_3545_ = v___x_3524_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_declName_3518_);
v_a_3551_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3522_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3522_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_k_3564_, lean_object* v_v_3565_, lean_object* v_t_3566_){
_start:
{
lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; 
if (lean_obj_tag(v_t_3566_) == 0)
{
lean_object* v_size_3581_; lean_object* v_k_3582_; lean_object* v_v_3583_; lean_object* v_l_3584_; lean_object* v_r_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3845_; 
v_size_3581_ = lean_ctor_get(v_t_3566_, 0);
v_k_3582_ = lean_ctor_get(v_t_3566_, 1);
v_v_3583_ = lean_ctor_get(v_t_3566_, 2);
v_l_3584_ = lean_ctor_get(v_t_3566_, 3);
v_r_3585_ = lean_ctor_get(v_t_3566_, 4);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_t_3566_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3587_ = v_t_3566_;
v_isShared_3588_ = v_isSharedCheck_3845_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_r_3585_);
lean_inc(v_l_3584_);
lean_inc(v_v_3583_);
lean_inc(v_k_3582_);
lean_inc(v_size_3581_);
lean_dec(v_t_3566_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3845_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; uint8_t v___y_3639_; lean_object* v_fst_3839_; lean_object* v_snd_3840_; lean_object* v_fst_3841_; lean_object* v_snd_3842_; uint8_t v___x_3843_; 
v_fst_3839_ = lean_ctor_get(v_k_3564_, 0);
v_snd_3840_ = lean_ctor_get(v_k_3564_, 1);
v_fst_3841_ = lean_ctor_get(v_k_3582_, 0);
v_snd_3842_ = lean_ctor_get(v_k_3582_, 1);
v___x_3843_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3839_, v_fst_3841_);
if (v___x_3843_ == 1)
{
uint8_t v___x_3844_; 
v___x_3844_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3840_, v_snd_3842_);
v___y_3639_ = v___x_3844_;
goto v___jp_3638_;
}
else
{
v___y_3639_ = v___x_3843_;
goto v___jp_3638_;
}
v___jp_3589_:
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3597_ = lean_nat_add(v___y_3594_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec(v___y_3594_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 3, v___y_3593_);
lean_ctor_set(v___x_3587_, 0, v___x_3597_);
v___x_3599_ = v___x_3587_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v___y_3593_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_r_3585_);
v___x_3599_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3600_, 0, v___y_3592_);
lean_ctor_set(v___x_3600_, 1, v___y_3591_);
lean_ctor_set(v___x_3600_, 2, v___y_3595_);
lean_ctor_set(v___x_3600_, 3, v___y_3590_);
lean_ctor_set(v___x_3600_, 4, v___x_3599_);
return v___x_3600_;
}
}
v___jp_3602_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = lean_nat_add(v___y_3612_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec(v___y_3612_);
v___x_3616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___y_3605_);
lean_ctor_set(v___x_3616_, 2, v___y_3608_);
lean_ctor_set(v___x_3616_, 3, v___y_3609_);
lean_ctor_set(v___x_3616_, 4, v___y_3613_);
v___x_3617_ = lean_nat_add(v___y_3603_, v___y_3610_);
lean_dec(v___y_3610_);
if (lean_obj_tag(v___y_3607_) == 0)
{
lean_object* v_size_3618_; 
v_size_3618_ = lean_ctor_get(v___y_3607_, 0);
lean_inc(v_size_3618_);
v___y_3590_ = v___x_3616_;
v___y_3591_ = v___y_3604_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___x_3617_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v_size_3618_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
v___y_3590_ = v___x_3616_;
v___y_3591_ = v___y_3604_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___x_3617_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v___x_3619_;
goto v___jp_3589_;
}
}
v___jp_3620_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_nat_add(v___y_3624_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec(v___y_3624_);
v___x_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_k_3582_);
lean_ctor_set(v___x_3634_, 2, v_v_3583_);
lean_ctor_set(v___x_3634_, 3, v_l_3584_);
lean_ctor_set(v___x_3634_, 4, v___y_3625_);
v___x_3635_ = lean_nat_add(v___y_3627_, v___y_3621_);
lean_dec(v___y_3621_);
if (lean_obj_tag(v___y_3628_) == 0)
{
lean_object* v_size_3636_; 
v_size_3636_ = lean_ctor_get(v___y_3628_, 0);
lean_inc(v_size_3636_);
v___y_3568_ = v___y_3622_;
v___y_3569_ = v___y_3623_;
v___y_3570_ = v___x_3634_;
v___y_3571_ = v___x_3635_;
v___y_3572_ = v___y_3626_;
v___y_3573_ = v___y_3628_;
v___y_3574_ = v___y_3629_;
v___y_3575_ = v___y_3630_;
v___y_3576_ = v___y_3631_;
v___y_3577_ = v_size_3636_;
goto v___jp_3567_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_unsigned_to_nat(0u);
v___y_3568_ = v___y_3622_;
v___y_3569_ = v___y_3623_;
v___y_3570_ = v___x_3634_;
v___y_3571_ = v___x_3635_;
v___y_3572_ = v___y_3626_;
v___y_3573_ = v___y_3628_;
v___y_3574_ = v___y_3629_;
v___y_3575_ = v___y_3630_;
v___y_3576_ = v___y_3631_;
v___y_3577_ = v___x_3637_;
goto v___jp_3567_;
}
}
v___jp_3638_:
{
switch(v___y_3639_)
{
case 0:
{
lean_object* v_impl_3640_; lean_object* v___x_3641_; 
lean_dec(v_size_3581_);
v_impl_3640_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_k_3564_, v_v_3565_, v_l_3584_);
v___x_3641_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3585_) == 0)
{
lean_object* v_size_3642_; lean_object* v_size_3643_; lean_object* v_k_3644_; lean_object* v_v_3645_; lean_object* v_l_3646_; lean_object* v_r_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_size_3642_ = lean_ctor_get(v_r_3585_, 0);
v_size_3643_ = lean_ctor_get(v_impl_3640_, 0);
lean_inc(v_size_3643_);
v_k_3644_ = lean_ctor_get(v_impl_3640_, 1);
lean_inc(v_k_3644_);
v_v_3645_ = lean_ctor_get(v_impl_3640_, 2);
lean_inc(v_v_3645_);
v_l_3646_ = lean_ctor_get(v_impl_3640_, 3);
lean_inc(v_l_3646_);
v_r_3647_ = lean_ctor_get(v_impl_3640_, 4);
lean_inc(v_r_3647_);
v___x_3648_ = lean_unsigned_to_nat(3u);
v___x_3649_ = lean_nat_mul(v___x_3648_, v_size_3642_);
v___x_3650_ = lean_nat_dec_lt(v___x_3649_, v_size_3643_);
lean_dec(v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
lean_dec(v_r_3647_);
lean_dec(v_l_3646_);
lean_dec(v_v_3645_);
lean_dec(v_k_3644_);
lean_del_object(v___x_3587_);
v___x_3651_ = lean_nat_add(v___x_3641_, v_size_3643_);
lean_dec(v_size_3643_);
v___x_3652_ = lean_nat_add(v___x_3651_, v_size_3642_);
lean_dec(v___x_3651_);
v___x_3653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v_k_3582_);
lean_ctor_set(v___x_3653_, 2, v_v_3583_);
lean_ctor_set(v___x_3653_, 3, v_impl_3640_);
lean_ctor_set(v___x_3653_, 4, v_r_3585_);
return v___x_3653_;
}
else
{
lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3690_; 
v_isSharedCheck_3690_ = !lean_is_exclusive(v_impl_3640_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; 
v_unused_3691_ = lean_ctor_get(v_impl_3640_, 4);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_impl_3640_, 3);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_impl_3640_, 2);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_impl_3640_, 1);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_impl_3640_, 0);
lean_dec(v_unused_3695_);
v___x_3655_ = v_impl_3640_;
v_isShared_3656_ = v_isSharedCheck_3690_;
goto v_resetjp_3654_;
}
else
{
lean_dec(v_impl_3640_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3690_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v_size_3657_; lean_object* v_size_3658_; lean_object* v_k_3659_; lean_object* v_v_3660_; lean_object* v_l_3661_; lean_object* v_r_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v_size_3657_ = lean_ctor_get(v_l_3646_, 0);
v_size_3658_ = lean_ctor_get(v_r_3647_, 0);
v_k_3659_ = lean_ctor_get(v_r_3647_, 1);
v_v_3660_ = lean_ctor_get(v_r_3647_, 2);
v_l_3661_ = lean_ctor_get(v_r_3647_, 3);
v_r_3662_ = lean_ctor_get(v_r_3647_, 4);
v___x_3663_ = lean_unsigned_to_nat(2u);
v___x_3664_ = lean_nat_mul(v___x_3663_, v_size_3657_);
v___x_3665_ = lean_nat_dec_lt(v_size_3658_, v___x_3664_);
lean_dec(v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
lean_inc(v_r_3662_);
lean_inc(v_l_3661_);
lean_inc(v_v_3660_);
lean_inc(v_k_3659_);
lean_del_object(v___x_3655_);
lean_dec(v_r_3647_);
v___x_3666_ = lean_nat_add(v___x_3641_, v_size_3643_);
lean_dec(v_size_3643_);
v___x_3667_ = lean_nat_add(v___x_3666_, v_size_3642_);
lean_dec(v___x_3666_);
v___x_3668_ = lean_nat_add(v___x_3641_, v_size_3657_);
if (lean_obj_tag(v_l_3661_) == 0)
{
lean_object* v_size_3669_; 
v_size_3669_ = lean_ctor_get(v_l_3661_, 0);
lean_inc(v_size_3669_);
lean_inc(v_size_3642_);
v___y_3603_ = v___x_3641_;
v___y_3604_ = v_k_3659_;
v___y_3605_ = v_k_3644_;
v___y_3606_ = v___x_3667_;
v___y_3607_ = v_r_3662_;
v___y_3608_ = v_v_3645_;
v___y_3609_ = v_l_3646_;
v___y_3610_ = v_size_3642_;
v___y_3611_ = v_v_3660_;
v___y_3612_ = v___x_3668_;
v___y_3613_ = v_l_3661_;
v___y_3614_ = v_size_3669_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3642_);
v___y_3603_ = v___x_3641_;
v___y_3604_ = v_k_3659_;
v___y_3605_ = v_k_3644_;
v___y_3606_ = v___x_3667_;
v___y_3607_ = v_r_3662_;
v___y_3608_ = v_v_3645_;
v___y_3609_ = v_l_3646_;
v___y_3610_ = v_size_3642_;
v___y_3611_ = v_v_3660_;
v___y_3612_ = v___x_3668_;
v___y_3613_ = v_l_3661_;
v___y_3614_ = v___x_3670_;
goto v___jp_3602_;
}
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_del_object(v___x_3587_);
v___x_3671_ = lean_nat_add(v___x_3641_, v_size_3643_);
lean_dec(v_size_3643_);
v___x_3672_ = lean_nat_add(v___x_3671_, v_size_3642_);
lean_dec(v___x_3671_);
v___x_3673_ = lean_nat_add(v___x_3641_, v_size_3642_);
v___x_3674_ = lean_nat_add(v___x_3673_, v_size_3658_);
lean_dec(v___x_3673_);
lean_inc_ref(v_r_3585_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 4, v_r_3585_);
lean_ctor_set(v___x_3655_, 3, v_r_3647_);
lean_ctor_set(v___x_3655_, 2, v_v_3583_);
lean_ctor_set(v___x_3655_, 1, v_k_3582_);
lean_ctor_set(v___x_3655_, 0, v___x_3674_);
v___x_3676_ = v___x_3655_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_r_3647_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v_r_3585_);
v___x_3676_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_isSharedCheck_3683_ = !lean_is_exclusive(v_r_3585_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; lean_object* v_unused_3688_; 
v_unused_3684_ = lean_ctor_get(v_r_3585_, 4);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_r_3585_, 3);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_r_3585_, 2);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_r_3585_, 1);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_r_3585_, 0);
lean_dec(v_unused_3688_);
v___x_3678_ = v_r_3585_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v_r_3585_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 4, v___x_3676_);
lean_ctor_set(v___x_3678_, 3, v_l_3646_);
lean_ctor_set(v___x_3678_, 2, v_v_3645_);
lean_ctor_set(v___x_3678_, 1, v_k_3644_);
lean_ctor_set(v___x_3678_, 0, v___x_3672_);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_k_3644_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_v_3645_);
lean_ctor_set(v_reuseFailAlloc_3682_, 3, v_l_3646_);
lean_ctor_set(v_reuseFailAlloc_3682_, 4, v___x_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3696_; 
lean_del_object(v___x_3587_);
v_l_3696_ = lean_ctor_get(v_impl_3640_, 3);
lean_inc(v_l_3696_);
if (lean_obj_tag(v_l_3696_) == 0)
{
lean_object* v_r_3697_; lean_object* v_k_3698_; lean_object* v_v_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3708_; 
v_r_3697_ = lean_ctor_get(v_impl_3640_, 4);
v_k_3698_ = lean_ctor_get(v_impl_3640_, 1);
v_v_3699_ = lean_ctor_get(v_impl_3640_, 2);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_impl_3640_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; 
v_unused_3709_ = lean_ctor_get(v_impl_3640_, 3);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_impl_3640_, 0);
lean_dec(v_unused_3710_);
v___x_3701_ = v_impl_3640_;
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_r_3697_);
lean_inc(v_v_3699_);
lean_inc(v_k_3698_);
lean_dec(v_impl_3640_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3697_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 3, v_r_3697_);
lean_ctor_set(v___x_3701_, 2, v_v_3583_);
lean_ctor_set(v___x_3701_, 1, v_k_3582_);
lean_ctor_set(v___x_3701_, 0, v___x_3641_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_r_3697_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_r_3697_);
v___x_3705_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3703_);
lean_ctor_set(v___x_3706_, 1, v_k_3698_);
lean_ctor_set(v___x_3706_, 2, v_v_3699_);
lean_ctor_set(v___x_3706_, 3, v_l_3696_);
lean_ctor_set(v___x_3706_, 4, v___x_3705_);
return v___x_3706_;
}
}
}
else
{
lean_object* v_r_3711_; 
v_r_3711_ = lean_ctor_get(v_impl_3640_, 4);
lean_inc(v_r_3711_);
if (lean_obj_tag(v_r_3711_) == 0)
{
lean_object* v_k_3712_; lean_object* v_v_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3734_; 
v_k_3712_ = lean_ctor_get(v_impl_3640_, 1);
v_v_3713_ = lean_ctor_get(v_impl_3640_, 2);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_impl_3640_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3735_ = lean_ctor_get(v_impl_3640_, 4);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_impl_3640_, 3);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_impl_3640_, 0);
lean_dec(v_unused_3737_);
v___x_3715_ = v_impl_3640_;
v_isShared_3716_ = v_isSharedCheck_3734_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_v_3713_);
lean_inc(v_k_3712_);
lean_dec(v_impl_3640_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3734_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_k_3717_; lean_object* v_v_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3730_; 
v_k_3717_ = lean_ctor_get(v_r_3711_, 1);
v_v_3718_ = lean_ctor_get(v_r_3711_, 2);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_r_3711_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3731_ = lean_ctor_get(v_r_3711_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3711_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3711_, 0);
lean_dec(v_unused_3733_);
v___x_3720_ = v_r_3711_;
v_isShared_3721_ = v_isSharedCheck_3730_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_v_3718_);
lean_inc(v_k_3717_);
lean_dec(v_r_3711_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3730_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3722_ = lean_unsigned_to_nat(3u);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 4, v_l_3696_);
lean_ctor_set(v___x_3720_, 3, v_l_3696_);
lean_ctor_set(v___x_3720_, 2, v_v_3713_);
lean_ctor_set(v___x_3720_, 1, v_k_3712_);
lean_ctor_set(v___x_3720_, 0, v___x_3641_);
v___x_3724_ = v___x_3720_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3712_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3713_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_l_3696_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3696_);
v___x_3724_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3726_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 4, v_l_3696_);
lean_ctor_set(v___x_3715_, 2, v_v_3583_);
lean_ctor_set(v___x_3715_, 1, v_k_3582_);
lean_ctor_set(v___x_3715_, 0, v___x_3641_);
v___x_3726_ = v___x_3715_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_l_3696_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_l_3696_);
v___x_3726_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3722_);
lean_ctor_set(v___x_3727_, 1, v_k_3717_);
lean_ctor_set(v___x_3727_, 2, v_v_3718_);
lean_ctor_set(v___x_3727_, 3, v___x_3724_);
lean_ctor_set(v___x_3727_, 4, v___x_3726_);
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_unsigned_to_nat(2u);
v___x_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v_k_3582_);
lean_ctor_set(v___x_3739_, 2, v_v_3583_);
lean_ctor_set(v___x_3739_, 3, v_impl_3640_);
lean_ctor_set(v___x_3739_, 4, v_r_3711_);
return v___x_3739_;
}
}
}
}
case 1:
{
lean_object* v___x_3740_; 
lean_del_object(v___x_3587_);
lean_dec(v_v_3583_);
lean_dec(v_k_3582_);
v___x_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3740_, 0, v_size_3581_);
lean_ctor_set(v___x_3740_, 1, v_k_3564_);
lean_ctor_set(v___x_3740_, 2, v_v_3565_);
lean_ctor_set(v___x_3740_, 3, v_l_3584_);
lean_ctor_set(v___x_3740_, 4, v_r_3585_);
return v___x_3740_;
}
default: 
{
lean_object* v_impl_3741_; lean_object* v___x_3742_; 
lean_del_object(v___x_3587_);
lean_dec(v_size_3581_);
v_impl_3741_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_k_3564_, v_v_3565_, v_r_3585_);
v___x_3742_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3584_) == 0)
{
lean_object* v_size_3743_; lean_object* v_size_3744_; lean_object* v_k_3745_; lean_object* v_v_3746_; lean_object* v_l_3747_; lean_object* v_r_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v_size_3743_ = lean_ctor_get(v_l_3584_, 0);
v_size_3744_ = lean_ctor_get(v_impl_3741_, 0);
lean_inc(v_size_3744_);
v_k_3745_ = lean_ctor_get(v_impl_3741_, 1);
lean_inc(v_k_3745_);
v_v_3746_ = lean_ctor_get(v_impl_3741_, 2);
lean_inc(v_v_3746_);
v_l_3747_ = lean_ctor_get(v_impl_3741_, 3);
lean_inc(v_l_3747_);
v_r_3748_ = lean_ctor_get(v_impl_3741_, 4);
lean_inc(v_r_3748_);
v___x_3749_ = lean_unsigned_to_nat(3u);
v___x_3750_ = lean_nat_mul(v___x_3749_, v_size_3743_);
v___x_3751_ = lean_nat_dec_lt(v___x_3750_, v_size_3744_);
lean_dec(v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec(v_r_3748_);
lean_dec(v_l_3747_);
lean_dec(v_v_3746_);
lean_dec(v_k_3745_);
v___x_3752_ = lean_nat_add(v___x_3742_, v_size_3743_);
v___x_3753_ = lean_nat_add(v___x_3752_, v_size_3744_);
lean_dec(v_size_3744_);
lean_dec(v___x_3752_);
v___x_3754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v_k_3582_);
lean_ctor_set(v___x_3754_, 2, v_v_3583_);
lean_ctor_set(v___x_3754_, 3, v_l_3584_);
lean_ctor_set(v___x_3754_, 4, v_impl_3741_);
return v___x_3754_;
}
else
{
lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3789_; 
v_isSharedCheck_3789_ = !lean_is_exclusive(v_impl_3741_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; lean_object* v_unused_3791_; lean_object* v_unused_3792_; lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3790_ = lean_ctor_get(v_impl_3741_, 4);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_impl_3741_, 3);
lean_dec(v_unused_3791_);
v_unused_3792_ = lean_ctor_get(v_impl_3741_, 2);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_impl_3741_, 1);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_impl_3741_, 0);
lean_dec(v_unused_3794_);
v___x_3756_ = v_impl_3741_;
v_isShared_3757_ = v_isSharedCheck_3789_;
goto v_resetjp_3755_;
}
else
{
lean_dec(v_impl_3741_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3789_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v_size_3758_; lean_object* v_k_3759_; lean_object* v_v_3760_; lean_object* v_l_3761_; lean_object* v_r_3762_; lean_object* v_size_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_size_3758_ = lean_ctor_get(v_l_3747_, 0);
v_k_3759_ = lean_ctor_get(v_l_3747_, 1);
v_v_3760_ = lean_ctor_get(v_l_3747_, 2);
v_l_3761_ = lean_ctor_get(v_l_3747_, 3);
v_r_3762_ = lean_ctor_get(v_l_3747_, 4);
v_size_3763_ = lean_ctor_get(v_r_3748_, 0);
v___x_3764_ = lean_unsigned_to_nat(2u);
v___x_3765_ = lean_nat_mul(v___x_3764_, v_size_3763_);
v___x_3766_ = lean_nat_dec_lt(v_size_3758_, v___x_3765_);
lean_dec(v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_inc(v_size_3763_);
lean_inc(v_r_3762_);
lean_inc(v_l_3761_);
lean_inc(v_v_3760_);
lean_inc(v_k_3759_);
lean_del_object(v___x_3756_);
lean_dec(v_l_3747_);
v___x_3767_ = lean_nat_add(v___x_3742_, v_size_3743_);
v___x_3768_ = lean_nat_add(v___x_3767_, v_size_3744_);
lean_dec(v_size_3744_);
if (lean_obj_tag(v_l_3761_) == 0)
{
lean_object* v_size_3769_; 
v_size_3769_ = lean_ctor_get(v_l_3761_, 0);
lean_inc(v_size_3769_);
v___y_3621_ = v_size_3763_;
v___y_3622_ = v_r_3748_;
v___y_3623_ = v___x_3768_;
v___y_3624_ = v___x_3767_;
v___y_3625_ = v_l_3761_;
v___y_3626_ = v_k_3745_;
v___y_3627_ = v___x_3742_;
v___y_3628_ = v_r_3762_;
v___y_3629_ = v_v_3760_;
v___y_3630_ = v_k_3759_;
v___y_3631_ = v_v_3746_;
v___y_3632_ = v_size_3769_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_unsigned_to_nat(0u);
v___y_3621_ = v_size_3763_;
v___y_3622_ = v_r_3748_;
v___y_3623_ = v___x_3768_;
v___y_3624_ = v___x_3767_;
v___y_3625_ = v_l_3761_;
v___y_3626_ = v_k_3745_;
v___y_3627_ = v___x_3742_;
v___y_3628_ = v_r_3762_;
v___y_3629_ = v_v_3760_;
v___y_3630_ = v_k_3759_;
v___y_3631_ = v_v_3746_;
v___y_3632_ = v___x_3770_;
goto v___jp_3620_;
}
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3771_ = lean_nat_add(v___x_3742_, v_size_3743_);
v___x_3772_ = lean_nat_add(v___x_3771_, v_size_3744_);
lean_dec(v_size_3744_);
v___x_3773_ = lean_nat_add(v___x_3771_, v_size_3758_);
lean_dec(v___x_3771_);
lean_inc_ref(v_l_3584_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 4, v_l_3747_);
lean_ctor_set(v___x_3756_, 3, v_l_3584_);
lean_ctor_set(v___x_3756_, 2, v_v_3583_);
lean_ctor_set(v___x_3756_, 1, v_k_3582_);
lean_ctor_set(v___x_3756_, 0, v___x_3773_);
v___x_3775_ = v___x_3756_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3788_, 3, v_l_3584_);
lean_ctor_set(v_reuseFailAlloc_3788_, 4, v_l_3747_);
v___x_3775_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_isSharedCheck_3782_ = !lean_is_exclusive(v_l_3584_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; 
v_unused_3783_ = lean_ctor_get(v_l_3584_, 4);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_l_3584_, 3);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_l_3584_, 2);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_l_3584_, 1);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_l_3584_, 0);
lean_dec(v_unused_3787_);
v___x_3777_ = v_l_3584_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_dec(v_l_3584_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 4, v_r_3748_);
lean_ctor_set(v___x_3777_, 3, v___x_3775_);
lean_ctor_set(v___x_3777_, 2, v_v_3746_);
lean_ctor_set(v___x_3777_, 1, v_k_3745_);
lean_ctor_set(v___x_3777_, 0, v___x_3772_);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3745_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3746_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_r_3748_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3795_; 
v_l_3795_ = lean_ctor_get(v_impl_3741_, 3);
lean_inc(v_l_3795_);
if (lean_obj_tag(v_l_3795_) == 0)
{
lean_object* v_r_3796_; lean_object* v_k_3797_; lean_object* v_v_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3819_; 
v_r_3796_ = lean_ctor_get(v_impl_3741_, 4);
v_k_3797_ = lean_ctor_get(v_impl_3741_, 1);
v_v_3798_ = lean_ctor_get(v_impl_3741_, 2);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_impl_3741_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3820_ = lean_ctor_get(v_impl_3741_, 3);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_impl_3741_, 0);
lean_dec(v_unused_3821_);
v___x_3800_ = v_impl_3741_;
v_isShared_3801_ = v_isSharedCheck_3819_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_r_3796_);
lean_inc(v_v_3798_);
lean_inc(v_k_3797_);
lean_dec(v_impl_3741_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3819_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_k_3802_; lean_object* v_v_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3815_; 
v_k_3802_ = lean_ctor_get(v_l_3795_, 1);
v_v_3803_ = lean_ctor_get(v_l_3795_, 2);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_l_3795_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3816_ = lean_ctor_get(v_l_3795_, 4);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_l_3795_, 3);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_l_3795_, 0);
lean_dec(v_unused_3818_);
v___x_3805_ = v_l_3795_;
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
lean_dec(v_l_3795_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3796_, 2);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 4, v_r_3796_);
lean_ctor_set(v___x_3805_, 3, v_r_3796_);
lean_ctor_set(v___x_3805_, 2, v_v_3583_);
lean_ctor_set(v___x_3805_, 1, v_k_3582_);
lean_ctor_set(v___x_3805_, 0, v___x_3742_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_r_3796_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_r_3796_);
v___x_3809_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
lean_inc(v_r_3796_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 3, v_r_3796_);
lean_ctor_set(v___x_3800_, 0, v___x_3742_);
v___x_3811_ = v___x_3800_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3797_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_r_3796_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3796_);
v___x_3811_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3807_);
lean_ctor_set(v___x_3812_, 1, v_k_3802_);
lean_ctor_set(v___x_3812_, 2, v_v_3803_);
lean_ctor_set(v___x_3812_, 3, v___x_3809_);
lean_ctor_set(v___x_3812_, 4, v___x_3811_);
return v___x_3812_;
}
}
}
}
}
else
{
lean_object* v_r_3822_; 
v_r_3822_ = lean_ctor_get(v_impl_3741_, 4);
lean_inc(v_r_3822_);
if (lean_obj_tag(v_r_3822_) == 0)
{
lean_object* v_k_3823_; lean_object* v_v_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3833_; 
v_k_3823_ = lean_ctor_get(v_impl_3741_, 1);
v_v_3824_ = lean_ctor_get(v_impl_3741_, 2);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_impl_3741_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; 
v_unused_3834_ = lean_ctor_get(v_impl_3741_, 4);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_impl_3741_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_impl_3741_, 0);
lean_dec(v_unused_3836_);
v___x_3826_ = v_impl_3741_;
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_v_3824_);
lean_inc(v_k_3823_);
lean_dec(v_impl_3741_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3833_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3828_ = lean_unsigned_to_nat(3u);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 4, v_l_3795_);
lean_ctor_set(v___x_3826_, 2, v_v_3583_);
lean_ctor_set(v___x_3826_, 1, v_k_3582_);
lean_ctor_set(v___x_3826_, 0, v___x_3742_);
v___x_3830_ = v___x_3826_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3582_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3583_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_l_3795_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_l_3795_);
v___x_3830_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3828_);
lean_ctor_set(v___x_3831_, 1, v_k_3823_);
lean_ctor_set(v___x_3831_, 2, v_v_3824_);
lean_ctor_set(v___x_3831_, 3, v___x_3830_);
lean_ctor_set(v___x_3831_, 4, v_r_3822_);
return v___x_3831_;
}
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = lean_unsigned_to_nat(2u);
v___x_3838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v_k_3582_);
lean_ctor_set(v___x_3838_, 2, v_v_3583_);
lean_ctor_set(v___x_3838_, 3, v_r_3822_);
lean_ctor_set(v___x_3838_, 4, v_impl_3741_);
return v___x_3838_;
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
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
lean_ctor_set(v___x_3847_, 1, v_k_3564_);
lean_ctor_set(v___x_3847_, 2, v_v_3565_);
lean_ctor_set(v___x_3847_, 3, v_t_3566_);
lean_ctor_set(v___x_3847_, 4, v_t_3566_);
return v___x_3847_;
}
v___jp_3567_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = lean_nat_add(v___y_3571_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec(v___y_3571_);
v___x_3579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
lean_ctor_set(v___x_3579_, 1, v___y_3572_);
lean_ctor_set(v___x_3579_, 2, v___y_3576_);
lean_ctor_set(v___x_3579_, 3, v___y_3573_);
lean_ctor_set(v___x_3579_, 4, v___y_3568_);
v___x_3580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3580_, 0, v___y_3569_);
lean_ctor_set(v___x_3580_, 1, v___y_3575_);
lean_ctor_set(v___x_3580_, 2, v___y_3574_);
lean_ctor_set(v___x_3580_, 3, v___y_3570_);
lean_ctor_set(v___x_3580_, 4, v___x_3579_);
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg(lean_object* v_t_3848_, lean_object* v_k_3849_, lean_object* v_fallback_3850_){
_start:
{
if (lean_obj_tag(v_t_3848_) == 0)
{
lean_object* v_k_3851_; lean_object* v_v_3852_; lean_object* v_l_3853_; lean_object* v_r_3854_; uint8_t v___y_3856_; lean_object* v_fst_3859_; lean_object* v_snd_3860_; lean_object* v_fst_3861_; lean_object* v_snd_3862_; uint8_t v___x_3863_; 
v_k_3851_ = lean_ctor_get(v_t_3848_, 1);
v_v_3852_ = lean_ctor_get(v_t_3848_, 2);
v_l_3853_ = lean_ctor_get(v_t_3848_, 3);
v_r_3854_ = lean_ctor_get(v_t_3848_, 4);
v_fst_3859_ = lean_ctor_get(v_k_3849_, 0);
v_snd_3860_ = lean_ctor_get(v_k_3849_, 1);
v_fst_3861_ = lean_ctor_get(v_k_3851_, 0);
v_snd_3862_ = lean_ctor_get(v_k_3851_, 1);
v___x_3863_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3859_, v_fst_3861_);
if (v___x_3863_ == 1)
{
uint8_t v___x_3864_; 
v___x_3864_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3860_, v_snd_3862_);
v___y_3856_ = v___x_3864_;
goto v___jp_3855_;
}
else
{
v___y_3856_ = v___x_3863_;
goto v___jp_3855_;
}
v___jp_3855_:
{
switch(v___y_3856_)
{
case 0:
{
v_t_3848_ = v_l_3853_;
goto _start;
}
case 1:
{
lean_inc(v_v_3852_);
return v_v_3852_;
}
default: 
{
v_t_3848_ = v_r_3854_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_3850_);
return v_fallback_3850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg___boxed(lean_object* v_t_3865_, lean_object* v_k_3866_, lean_object* v_fallback_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg(v_t_3865_, v_k_3866_, v_fallback_3867_);
lean_dec(v_fallback_3867_);
lean_dec_ref(v_k_3866_);
lean_dec(v_t_3865_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v___x_3869_, lean_object* v_as_3870_, size_t v_sz_3871_, size_t v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_lt(v_i_3872_, v_sz_3871_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec(v___x_3869_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_b_3873_);
return v___x_3878_;
}
else
{
lean_object* v_a_3879_; lean_object* v_fst_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3908_; 
v_a_3879_ = lean_array_uget(v_as_3870_, v_i_3872_);
v_fst_3880_ = lean_ctor_get(v_a_3879_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; 
v_unused_3909_ = lean_ctor_get(v_a_3879_, 1);
lean_dec(v_unused_3909_);
v___x_3882_ = v_a_3879_;
v_isShared_3883_ = v_isSharedCheck_3908_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_fst_3880_);
lean_dec(v_a_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3908_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; 
lean_inc(v_fst_3880_);
v___x_3884_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3880_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; lean_object* v___y_3888_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3886_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_3885_) == 0)
{
lean_inc(v___x_3869_);
v___y_3888_ = v___x_3869_;
goto v___jp_3887_;
}
else
{
lean_object* v_val_3899_; 
v_val_3899_ = lean_ctor_get(v_a_3885_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_a_3885_, 1);
v___y_3888_ = v_val_3899_;
goto v___jp_3887_;
}
v___jp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v_fst_3880_);
lean_ctor_set(v___x_3882_, 0, v___y_3888_);
v___x_3890_ = v___x_3882_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___y_3888_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_fst_3880_);
v___x_3890_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; 
v___x_3891_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg(v_b_3873_, v___x_3890_, v___x_3886_);
v___x_3892_ = lean_unsigned_to_nat(1u);
v___x_3893_ = lean_nat_add(v___x_3891_, v___x_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v___x_3890_, v___x_3893_, v_b_3873_);
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_add(v_i_3872_, v___x_3895_);
v_i_3872_ = v___x_3896_;
v_b_3873_ = v___x_3894_;
goto _start;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_del_object(v___x_3882_);
lean_dec(v_fst_3880_);
lean_dec(v_b_3873_);
lean_dec(v___x_3869_);
v_a_3900_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3884_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3884_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___boxed(lean_object* v___x_3910_, lean_object* v_as_3911_, lean_object* v_sz_3912_, lean_object* v_i_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3912_);
lean_dec(v_sz_3912_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3913_);
lean_dec(v_i_3913_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(v___x_3910_, v_as_3911_, v_sz_boxed_3918_, v_i_boxed_3919_, v_b_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v_as_3911_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v___x_3921_, lean_object* v_as_3922_, size_t v_sz_3923_, size_t v_i_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_a_3930_; uint8_t v___x_3934_; 
v___x_3934_ = lean_usize_dec_lt(v_i_3924_, v_sz_3923_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; 
lean_dec(v___x_3921_);
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_b_3925_);
return v___x_3935_;
}
else
{
lean_object* v_a_3936_; lean_object* v_snd_3937_; lean_object* v_fst_3938_; lean_object* v_size_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; size_t v_sz_3943_; size_t v___x_3944_; lean_object* v___x_3945_; 
v_a_3936_ = lean_array_uget_borrowed(v_as_3922_, v_i_3924_);
v_snd_3937_ = lean_ctor_get(v_a_3936_, 1);
v_fst_3938_ = lean_ctor_get(v_a_3936_, 0);
v_size_3939_ = lean_ctor_get(v_snd_3937_, 0);
v___x_3940_ = lean_box(1);
v___x_3941_ = lean_mk_empty_array_with_capacity(v_size_3939_);
v___x_3942_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v___x_3941_, v_snd_3937_);
v_sz_3943_ = lean_array_size(v___x_3942_);
v___x_3944_ = ((size_t)0ULL);
lean_inc(v___x_3921_);
v___x_3945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(v___x_3921_, v___x_3942_, v_sz_3943_, v___x_3944_, v___x_3940_, v___y_3926_, v___y_3927_);
lean_dec_ref(v___x_3942_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
lean_inc(v_fst_3938_);
v___x_3947_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(v_fst_3938_, v_b_3925_, v_a_3946_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v_a_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
v_a_3949_ = lean_ctor_get(v_a_3948_, 0);
lean_inc(v_a_3949_);
lean_dec(v_a_3948_);
v_a_3930_ = v_a_3949_;
goto v___jp_3929_;
}
else
{
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3959_; 
v_a_3950_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3952_ = v___x_3947_;
v_isShared_3953_ = v_isSharedCheck_3959_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3947_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3959_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
if (lean_obj_tag(v_a_3950_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3956_; 
lean_dec(v___x_3921_);
v_a_3954_ = lean_ctor_get(v_a_3950_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v_a_3950_, 1);
if (v_isShared_3953_ == 0)
{
lean_ctor_set_tag(v___x_3952_, 0);
lean_ctor_set(v___x_3952_, 0, v_a_3954_);
v___x_3956_ = v___x_3952_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
else
{
lean_object* v_a_3958_; 
lean_del_object(v___x_3952_);
v_a_3958_ = lean_ctor_get(v_a_3950_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v_a_3950_, 1);
v_a_3930_ = v_a_3958_;
goto v___jp_3929_;
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v___x_3921_);
v_a_3960_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3947_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3947_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v_b_3925_);
lean_dec(v___x_3921_);
v_a_3968_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3945_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3945_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
v___jp_3929_:
{
size_t v___x_3931_; size_t v___x_3932_; 
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_add(v_i_3924_, v___x_3931_);
v_i_3924_ = v___x_3932_;
v_b_3925_ = v_a_3930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v___x_3976_, lean_object* v_as_3977_, lean_object* v_sz_3978_, lean_object* v_i_3979_, lean_object* v_b_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_sz_boxed_3984_; size_t v_i_boxed_3985_; lean_object* v_res_3986_; 
v_sz_boxed_3984_ = lean_unbox_usize(v_sz_3978_);
lean_dec(v_sz_3978_);
v_i_boxed_3985_ = lean_unbox_usize(v_i_3979_);
lean_dec(v_i_3979_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v___x_3976_, v_as_3977_, v_sz_boxed_3984_, v_i_boxed_3985_, v_b_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec_ref(v_as_3977_);
return v_res_3986_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(uint8_t v___y_3987_, lean_object* v_as_3988_, size_t v_i_3989_, size_t v_stop_3990_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_usize_dec_eq(v_i_3989_, v_stop_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v_snd_3993_; lean_object* v_size_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3992_ = lean_array_uget_borrowed(v_as_3988_, v_i_3989_);
v_snd_3993_ = lean_ctor_get(v___x_3992_, 1);
v_size_3994_ = lean_ctor_get(v_snd_3993_, 0);
v___x_3995_ = 1;
v___x_3996_ = lean_unsigned_to_nat(0u);
v___x_3997_ = lean_nat_dec_eq(v_size_3994_, v___x_3996_);
if (v___x_3997_ == 0)
{
return v___x_3995_;
}
else
{
if (v___y_3987_ == 0)
{
size_t v___x_3998_; size_t v___x_3999_; 
v___x_3998_ = ((size_t)1ULL);
v___x_3999_ = lean_usize_add(v_i_3989_, v___x_3998_);
v_i_3989_ = v___x_3999_;
goto _start;
}
else
{
return v___x_3995_;
}
}
}
else
{
uint8_t v___x_4001_; 
v___x_4001_ = 0;
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___y_4002_, lean_object* v_as_4003_, lean_object* v_i_4004_, lean_object* v_stop_4005_){
_start:
{
uint8_t v___y_17793__boxed_4006_; size_t v_i_boxed_4007_; size_t v_stop_boxed_4008_; uint8_t v_res_4009_; lean_object* v_r_4010_; 
v___y_17793__boxed_4006_ = lean_unbox(v___y_4002_);
v_i_boxed_4007_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_stop_boxed_4008_ = lean_unbox_usize(v_stop_4005_);
lean_dec(v_stop_4005_);
v_res_4009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___y_17793__boxed_4006_, v_as_4003_, v_i_boxed_4007_, v_stop_boxed_4008_);
lean_dec_ref(v_as_4003_);
v_r_4010_ = lean_box(v_res_4009_);
return v_r_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_fst_4012_, lean_object* v_sp_4013_, lean_object* v___x_4014_, lean_object* v_as_4015_, size_t v_sz_4016_, size_t v_i_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_a_4023_; uint8_t v___x_4027_; 
v___x_4027_ = lean_usize_dec_lt(v_i_4017_, v_sz_4016_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v_b_4018_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v_fst_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4165_; 
v_a_4029_ = lean_array_uget(v_as_4015_, v_i_4017_);
v_fst_4030_ = lean_ctor_get(v_a_4029_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_a_4029_, 1);
lean_dec(v_unused_4166_);
v___x_4032_ = v_a_4029_;
v_isShared_4033_ = v_isSharedCheck_4165_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_fst_4030_);
lean_dec(v_a_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4165_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; 
lean_inc(v_fst_4030_);
v___x_4034_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_4030_, v___y_4019_, v___y_4020_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
if (lean_obj_tag(v_a_4035_) == 0)
{
lean_object* v_fst_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4070_; 
v_fst_4036_ = lean_ctor_get(v_b_4018_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_b_4018_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v_b_4018_, 1);
lean_dec(v_unused_4071_);
v___x_4038_ = v_b_4018_;
v_isShared_4039_ = v_isSharedCheck_4070_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_fst_4036_);
lean_dec(v_b_4018_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4070_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_optName_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_optName_4040_ = lean_ctor_get(v_fst_4012_, 1);
v___x_4041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___closed__0));
v___x_4042_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_4030_, v___x_4027_);
v___x_4043_ = lean_string_append(v___x_4041_, v___x_4042_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_4045_ = lean_string_append(v___x_4043_, v___x_4044_);
lean_inc(v_optName_4040_);
v___x_4046_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_4040_, v___x_4027_);
v___x_4047_ = lean_string_append(v___x_4045_, v___x_4046_);
lean_dec_ref(v___x_4046_);
v___x_4048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_4049_ = lean_string_append(v___x_4047_, v___x_4048_);
v___x_4050_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_4049_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4053_; 
lean_dec_ref_known(v___x_4050_, 1);
lean_del_object(v___x_4032_);
v___x_4051_ = lean_box(v___x_4027_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 1, v___x_4051_);
v___x_4053_ = v___x_4038_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_fst_4036_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
v_a_4023_ = v___x_4053_;
goto v___jp_4022_;
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4069_; 
lean_del_object(v___x_4038_);
lean_dec(v_fst_4036_);
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v_a_4055_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4057_ = v___x_4050_;
v_isShared_4058_ = v_isSharedCheck_4069_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4050_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4069_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_ref_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4064_; 
v_ref_4059_ = lean_ctor_get(v___y_4019_, 5);
v___x_4060_ = lean_io_error_to_string(v_a_4055_);
v___x_4061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
v___x_4062_ = l_Lean_MessageData_ofFormat(v___x_4061_);
lean_inc(v_ref_4059_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4062_);
lean_ctor_set(v___x_4032_, 0, v_ref_4059_);
v___x_4064_ = v___x_4032_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_ref_4059_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4066_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4064_);
v___x_4066_ = v___x_4057_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
else
{
lean_object* v_fst_4072_; lean_object* v_snd_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4156_; 
v_fst_4072_ = lean_ctor_get(v_b_4018_, 0);
v_snd_4073_ = lean_ctor_get(v_b_4018_, 1);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_b_4018_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4075_ = v_b_4018_;
v_isShared_4076_ = v_isSharedCheck_4156_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_snd_4073_);
lean_inc(v_fst_4072_);
lean_dec(v_b_4018_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4156_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v_val_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4155_; 
v_val_4077_ = lean_ctor_get(v_a_4035_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_a_4035_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4079_ = v_a_4035_;
v_isShared_4080_ = v_isSharedCheck_4155_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_val_4077_);
lean_dec(v_a_4035_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4155_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4030_, v___y_4019_, v___y_4020_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___y_4084_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
if (lean_obj_tag(v_a_4082_) == 0)
{
lean_inc(v___x_4014_);
v___y_4084_ = v___x_4014_;
goto v___jp_4083_;
}
else
{
lean_object* v_val_4146_; 
v_val_4146_ = lean_ctor_get(v_a_4082_, 0);
lean_inc(v_val_4146_);
lean_dec_ref_known(v_a_4082_, 1);
v___y_4084_ = v_val_4146_;
goto v___jp_4083_;
}
v___jp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v___y_4084_);
lean_inc(v_sp_4013_);
v___x_4086_ = l_Lean_SearchPath_findWithExt(v_sp_4013_, v___x_4085_, v___y_4084_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
if (lean_obj_tag(v_a_4087_) == 0)
{
lean_object* v_optName_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec(v_val_4077_);
lean_dec(v_snd_4073_);
v_optName_4088_ = lean_ctor_get(v_fst_4012_, 1);
v___x_4089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
v___x_4090_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_4084_, v___x_4027_);
v___x_4091_ = lean_string_append(v___x_4089_, v___x_4090_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_4093_ = lean_string_append(v___x_4091_, v___x_4092_);
lean_inc(v_optName_4088_);
v___x_4094_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_4088_, v___x_4027_);
v___x_4095_ = lean_string_append(v___x_4093_, v___x_4094_);
lean_dec_ref(v___x_4094_);
v___x_4096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_4097_ = lean_string_append(v___x_4095_, v___x_4096_);
v___x_4098_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_4097_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec_ref_known(v___x_4098_, 1);
lean_del_object(v___x_4079_);
lean_del_object(v___x_4032_);
v___x_4099_ = lean_box(v___x_4027_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 1, v___x_4099_);
v___x_4101_ = v___x_4075_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_fst_4072_);
lean_ctor_set(v_reuseFailAlloc_4102_, 1, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
v_a_4023_ = v___x_4101_;
goto v___jp_4022_;
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4119_; 
lean_del_object(v___x_4075_);
lean_dec(v_fst_4072_);
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v_a_4103_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4105_ = v___x_4098_;
v_isShared_4106_ = v_isSharedCheck_4119_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4098_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4119_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v_ref_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v_ref_4107_ = lean_ctor_get(v___y_4019_, 5);
v___x_4108_ = lean_io_error_to_string(v_a_4103_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set_tag(v___x_4079_, 3);
lean_ctor_set(v___x_4079_, 0, v___x_4108_);
v___x_4110_ = v___x_4079_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; lean_object* v___x_4113_; 
v___x_4111_ = l_Lean_MessageData_ofFormat(v___x_4110_);
lean_inc(v_ref_4107_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4111_);
lean_ctor_set(v___x_4032_, 0, v_ref_4107_);
v___x_4113_ = v___x_4032_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_ref_4107_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4115_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4113_);
v___x_4115_ = v___x_4105_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
else
{
lean_object* v_range_4120_; lean_object* v_val_4121_; lean_object* v_pos_4122_; lean_object* v_optName_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec(v___y_4084_);
lean_del_object(v___x_4079_);
lean_del_object(v___x_4032_);
v_range_4120_ = lean_ctor_get(v_val_4077_, 0);
lean_inc_ref(v_range_4120_);
lean_dec(v_val_4077_);
v_val_4121_ = lean_ctor_get(v_a_4087_, 0);
lean_inc(v_val_4121_);
lean_dec_ref_known(v_a_4087_, 1);
v_pos_4122_ = lean_ctor_get(v_range_4120_, 0);
lean_inc_ref(v_pos_4122_);
lean_dec_ref(v_range_4120_);
v_optName_4123_ = lean_ctor_get(v_fst_4012_, 1);
lean_inc(v_optName_4123_);
v___x_4124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4124_, 0, v_val_4121_);
lean_ctor_set(v___x_4124_, 1, v_pos_4122_);
lean_ctor_set(v___x_4124_, 2, v_optName_4123_);
v___x_4125_ = lean_array_push(v_fst_4072_, v___x_4124_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4125_);
v___x_4127_ = v___x_4075_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_snd_4073_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
v_a_4023_ = v___x_4127_;
goto v___jp_4022_;
}
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v___y_4084_);
lean_dec(v_val_4077_);
lean_del_object(v___x_4075_);
lean_dec(v_snd_4073_);
lean_dec(v_fst_4072_);
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v_a_4129_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4131_ = v___x_4086_;
v_isShared_4132_ = v_isSharedCheck_4145_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4086_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4145_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v_ref_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v_ref_4133_ = lean_ctor_get(v___y_4019_, 5);
v___x_4134_ = lean_io_error_to_string(v_a_4129_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set_tag(v___x_4079_, 3);
lean_ctor_set(v___x_4079_, 0, v___x_4134_);
v___x_4136_ = v___x_4079_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4137_ = l_Lean_MessageData_ofFormat(v___x_4136_);
lean_inc(v_ref_4133_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 1, v___x_4137_);
lean_ctor_set(v___x_4032_, 0, v_ref_4133_);
v___x_4139_ = v___x_4032_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_ref_4133_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4141_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v___x_4139_);
v___x_4141_ = v___x_4131_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_del_object(v___x_4079_);
lean_dec(v_val_4077_);
lean_del_object(v___x_4075_);
lean_dec(v_snd_4073_);
lean_dec(v_fst_4072_);
lean_del_object(v___x_4032_);
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v_a_4147_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4081_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4081_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_del_object(v___x_4032_);
lean_dec(v_fst_4030_);
lean_dec_ref(v_b_4018_);
lean_dec(v___x_4014_);
lean_dec(v_sp_4013_);
lean_dec_ref(v_fst_4012_);
v_a_4157_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4034_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4034_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
v___jp_4022_:
{
size_t v___x_4024_; size_t v___x_4025_; 
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_4017_, v___x_4024_);
v_i_4017_ = v___x_4025_;
v_b_4018_ = v_a_4023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_fst_4167_, lean_object* v_sp_4168_, lean_object* v___x_4169_, lean_object* v_as_4170_, lean_object* v_sz_4171_, lean_object* v_i_4172_, lean_object* v_b_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
size_t v_sz_boxed_4177_; size_t v_i_boxed_4178_; lean_object* v_res_4179_; 
v_sz_boxed_4177_ = lean_unbox_usize(v_sz_4171_);
lean_dec(v_sz_4171_);
v_i_boxed_4178_ = lean_unbox_usize(v_i_4172_);
lean_dec(v_i_4172_);
v_res_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_fst_4167_, v_sp_4168_, v___x_4169_, v_as_4170_, v_sz_boxed_4177_, v_i_boxed_4178_, v_b_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_as_4170_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_sp_4180_, lean_object* v___x_4181_, lean_object* v_as_4182_, size_t v_sz_4183_, size_t v_i_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v___x_4189_; 
v___x_4189_ = lean_usize_dec_lt(v_i_4184_, v_sz_4183_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; 
lean_dec(v___x_4181_);
lean_dec(v_sp_4180_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_b_4185_);
return v___x_4190_;
}
else
{
lean_object* v_a_4191_; lean_object* v_snd_4192_; lean_object* v_fst_4193_; lean_object* v_fst_4194_; lean_object* v_snd_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4221_; 
v_a_4191_ = lean_array_uget_borrowed(v_as_4182_, v_i_4184_);
v_snd_4192_ = lean_ctor_get(v_a_4191_, 1);
v_fst_4193_ = lean_ctor_get(v_a_4191_, 0);
v_fst_4194_ = lean_ctor_get(v_b_4185_, 0);
v_snd_4195_ = lean_ctor_get(v_b_4185_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_b_4185_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4197_ = v_b_4185_;
v_isShared_4198_ = v_isSharedCheck_4221_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_snd_4195_);
lean_inc(v_fst_4194_);
lean_dec(v_b_4185_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4221_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_size_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4203_; 
v_size_4199_ = lean_ctor_get(v_snd_4192_, 0);
v___x_4200_ = lean_mk_empty_array_with_capacity(v_size_4199_);
v___x_4201_ = l_Std_DHashMap_Raw_foldM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v___x_4200_, v_snd_4192_);
if (v_isShared_4198_ == 0)
{
v___x_4203_ = v___x_4197_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_fst_4194_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_snd_4195_);
v___x_4203_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
size_t v_sz_4204_; size_t v___x_4205_; lean_object* v___x_4206_; 
v_sz_4204_ = lean_array_size(v___x_4201_);
v___x_4205_ = ((size_t)0ULL);
lean_inc(v___x_4181_);
lean_inc(v_sp_4180_);
lean_inc(v_fst_4193_);
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_fst_4193_, v_sp_4180_, v___x_4181_, v___x_4201_, v_sz_4204_, v___x_4205_, v___x_4203_, v___y_4186_, v___y_4187_);
lean_dec_ref(v___x_4201_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v_fst_4208_; lean_object* v_snd_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4219_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
v_fst_4208_ = lean_ctor_get(v_a_4207_, 0);
v_snd_4209_ = lean_ctor_get(v_a_4207_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_a_4207_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4211_ = v_a_4207_;
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_snd_4209_);
lean_inc(v_fst_4208_);
lean_dec(v_a_4207_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_fst_4208_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_snd_4209_);
v___x_4214_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
size_t v___x_4215_; size_t v___x_4216_; 
v___x_4215_ = ((size_t)1ULL);
v___x_4216_ = lean_usize_add(v_i_4184_, v___x_4215_);
v_i_4184_ = v___x_4216_;
v_b_4185_ = v___x_4214_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4181_);
lean_dec(v_sp_4180_);
return v___x_4206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_sp_4222_, lean_object* v___x_4223_, lean_object* v_as_4224_, lean_object* v_sz_4225_, lean_object* v_i_4226_, lean_object* v_b_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4225_);
lean_dec(v_sz_4225_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4226_);
lean_dec(v_i_4226_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_sp_4222_, v___x_4223_, v_as_4224_, v_sz_boxed_4231_, v_i_boxed_4232_, v_b_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec_ref(v_as_4224_);
return v_res_4233_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4240_ = l_Lean_maxRecDepth;
v___x_4241_ = l_Lean_Options_empty;
v___x_4242_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4241_, v___x_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4243_, lean_object* v_linterOpts_4244_, lean_object* v_sp_4245_, lean_object* v_env_4246_, lean_object* v_mod_4247_){
_start:
{
lean_object* v_msg_4250_; lean_object* v_a_4255_; lean_object* v_a_4259_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v_a_4290_; lean_object* v___y_4294_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; uint8_t v___y_4301_; lean_object* v___y_4302_; uint8_t v___y_4303_; uint8_t v___y_4304_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v_env_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; lean_object* v___y_4388_; uint8_t v___y_4389_; lean_object* v___y_4416_; lean_object* v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___x_4428_; lean_object* v___x_4429_; uint8_t v___x_4430_; lean_object* v_fileName_4432_; lean_object* v_fileMap_4433_; lean_object* v_currRecDepth_4434_; lean_object* v_ref_4435_; lean_object* v_currNamespace_4436_; lean_object* v_openDecls_4437_; lean_object* v_initHeartbeats_4438_; lean_object* v_maxHeartbeats_4439_; lean_object* v_quotContext_4440_; lean_object* v_currMacroScope_4441_; lean_object* v_cancelTk_x3f_4442_; uint8_t v_suppressElabErrors_4443_; lean_object* v_inheritedTraceOptions_4444_; lean_object* v___y_4445_; uint8_t v___y_4461_; uint8_t v___x_4481_; 
v___x_4273_ = lean_unsigned_to_nat(0u);
v___x_4274_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4275_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4276_ = lean_io_get_num_heartbeats();
v___x_4277_ = l_Lean_firstFrontendMacroScope;
v___x_4278_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4279_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4280_ = lean_box(0);
v___x_4281_ = lean_box(0);
v___x_4282_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4283_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4284_ = 1;
v___x_4285_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4286_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4287_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4287_, 0, v_env_4246_);
lean_ctor_set(v___x_4287_, 1, v___x_4278_);
lean_ctor_set(v___x_4287_, 2, v___x_4279_);
lean_ctor_set(v___x_4287_, 3, v___x_4282_);
lean_ctor_set(v___x_4287_, 4, v___x_4283_);
lean_ctor_set(v___x_4287_, 5, v___x_4274_);
lean_ctor_set(v___x_4287_, 6, v___x_4275_);
lean_ctor_set(v___x_4287_, 7, v___x_4285_);
lean_ctor_set(v___x_4287_, 8, v___x_4286_);
v___x_4288_ = lean_st_mk_ref(v___x_4287_);
v___x_4373_ = l_Lean_inheritedTraceOptions;
v___x_4374_ = lean_st_ref_get(v___x_4373_);
v___x_4375_ = lean_st_ref_get(v___x_4288_);
v_env_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc_ref(v_env_4376_);
lean_dec(v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4378_ = l_Lean_instInhabitedFileMap_default;
v___x_4379_ = l_Lean_Options_empty;
v___x_4380_ = lean_box(0);
v___x_4381_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4382_ = 0;
v___x_4428_ = lean_box(0);
v___x_4429_ = l_Lean_Name_getRoot(v_mod_4247_);
v___x_4430_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4481_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4376_);
lean_dec_ref(v_env_4376_);
if (v___x_4481_ == 0)
{
if (v___x_4430_ == 0)
{
lean_inc(v___x_4288_);
v_fileName_4432_ = v___x_4377_;
v_fileMap_4433_ = v___x_4378_;
v_currRecDepth_4434_ = v___x_4273_;
v_ref_4435_ = v___x_4380_;
v_currNamespace_4436_ = v___x_4280_;
v_openDecls_4437_ = v___x_4281_;
v_initHeartbeats_4438_ = v___x_4276_;
v_maxHeartbeats_4439_ = v___x_4381_;
v_quotContext_4440_ = v___x_4280_;
v_currMacroScope_4441_ = v___x_4277_;
v_cancelTk_x3f_4442_ = v___x_4428_;
v_suppressElabErrors_4443_ = v___x_4382_;
v_inheritedTraceOptions_4444_ = v___x_4374_;
v___y_4445_ = v___x_4288_;
goto v___jp_4431_;
}
else
{
v___y_4461_ = v___x_4481_;
goto v___jp_4460_;
}
}
else
{
v___y_4461_ = v___x_4430_;
goto v___jp_4460_;
}
v___jp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = l_Lean_MessageData_toString(v_msg_4250_);
v___x_4252_ = lean_mk_io_user_error(v___x_4251_);
v___x_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
return v___x_4253_;
}
v___jp_4254_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_mk_io_user_error(v_a_4255_);
v___x_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
v___jp_4258_:
{
if (lean_obj_tag(v_a_4259_) == 0)
{
lean_object* v_msg_4260_; 
v_msg_4260_ = lean_ctor_get(v_a_4259_, 1);
lean_inc_ref(v_msg_4260_);
lean_dec_ref_known(v_a_4259_, 2);
v_msg_4250_ = v_msg_4260_;
goto v___jp_4249_;
}
else
{
lean_object* v_id_4261_; lean_object* v___x_4262_; 
v_id_4261_ = lean_ctor_get(v_a_4259_, 0);
lean_inc(v_id_4261_);
lean_dec_ref_known(v_a_4259_, 2);
v___x_4262_ = l_Lean_InternalExceptionId_getName(v_id_4261_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec(v_id_4261_);
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4265_ = 1;
v___x_4266_ = l_Lean_Name_toString(v_a_4263_, v___x_4265_);
v___x_4267_ = lean_string_append(v___x_4264_, v___x_4266_);
lean_dec_ref(v___x_4266_);
v_a_4255_ = v___x_4267_;
goto v___jp_4254_;
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
lean_dec_ref_known(v___x_4262_, 1);
v___x_4268_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4269_ = l_Nat_reprFast(v_id_4261_);
v___x_4270_ = lean_string_append(v___x_4268_, v___x_4269_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4272_ = lean_string_append(v___x_4270_, v___x_4271_);
v_a_4255_ = v___x_4272_;
goto v___jp_4254_;
}
}
}
v___jp_4289_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_st_ref_get(v___x_4288_);
lean_dec(v___x_4288_);
lean_dec(v___x_4291_);
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_a_4290_);
return v___x_4292_;
}
v___jp_4293_:
{
lean_object* v_a_4295_; 
v_a_4295_ = lean_ctor_get(v___y_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref(v___y_4294_);
v_a_4290_ = v_a_4295_;
goto v___jp_4289_;
}
v___jp_4296_:
{
switch(v___y_4301_)
{
case 0:
{
lean_dec(v_sp_4245_);
if (v___y_4304_ == 0)
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec_ref(v___y_4302_);
lean_dec_ref(v___y_4299_);
lean_dec_ref(v___y_4298_);
v___x_4305_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4247_, v___x_4284_);
v___x_4307_ = lean_string_append(v___x_4305_, v___x_4306_);
lean_dec_ref(v___x_4306_);
v___x_4308_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4309_ = lean_string_append(v___x_4307_, v___x_4308_);
v___x_4310_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_4309_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v___x_4312_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4304_, v_a_4311_, v___y_4300_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4300_);
v___y_4294_ = v___x_4312_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4297_);
lean_dec(v___x_4288_);
v_a_4313_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4315_ = v___x_4310_;
v_isShared_4316_ = v_isSharedCheck_4322_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4310_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4322_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4317_ = lean_io_error_to_string(v_a_4313_);
if (v_isShared_4316_ == 0)
{
lean_ctor_set_tag(v___x_4315_, 3);
lean_ctor_set(v___x_4315_, 0, v___x_4317_);
v___x_4319_ = v___x_4315_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_MessageData_ofFormat(v___x_4319_);
v_msg_4250_ = v___x_4320_;
goto v___jp_4249_;
}
}
}
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4323_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4247_, v___y_4304_);
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
lean_dec_ref(v___x_4324_);
v___x_4326_ = lean_array_get_size(v___y_4298_);
lean_dec_ref(v___y_4298_);
v___x_4327_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4299_, v___y_4302_, v___x_4284_, v___x_4325_, v___x_4326_, v___x_4284_, v___y_4300_, v___y_4297_);
lean_dec_ref(v___y_4302_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4329_ = l_Lean_MessageData_toString(v_a_4328_);
v___x_4330_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(v___x_4329_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4304_, v_a_4331_, v___y_4300_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4300_);
v___y_4294_ = v___x_4332_;
goto v___jp_4293_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4297_);
lean_dec(v___x_4288_);
v_a_4333_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4335_ = v___x_4330_;
v_isShared_4336_ = v_isSharedCheck_4342_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4330_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4342_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4337_ = lean_io_error_to_string(v_a_4333_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 3);
lean_ctor_set(v___x_4335_, 0, v___x_4337_);
v___x_4339_ = v___x_4335_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_MessageData_ofFormat(v___x_4339_);
v_msg_4250_ = v___x_4340_;
goto v___jp_4249_;
}
}
}
}
else
{
lean_object* v_a_4343_; 
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4297_);
lean_dec(v___x_4288_);
v_a_4343_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4327_, 1);
v_a_4259_ = v_a_4343_;
goto v___jp_4258_;
}
}
}
case 1:
{
lean_object* v___x_4344_; lean_object* v_env_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; size_t v_sz_4349_; size_t v___x_4350_; lean_object* v___x_4351_; 
lean_dec_ref(v___y_4302_);
lean_dec_ref(v___y_4298_);
lean_dec(v_mod_4247_);
v___x_4344_ = lean_st_ref_get(v___y_4297_);
v_env_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_ref(v_env_4345_);
lean_dec(v___x_4344_);
v___x_4346_ = l_Lean_Environment_mainModule(v_env_4345_);
lean_dec_ref(v_env_4345_);
v___x_4347_ = lean_box(v___y_4303_);
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4286_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v_sz_4349_ = lean_array_size(v___y_4299_);
v___x_4350_ = ((size_t)0ULL);
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_sp_4245_, v___x_4346_, v___y_4299_, v_sz_4349_, v___x_4350_, v___x_4348_, v___y_4300_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4299_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v_fst_4353_; lean_object* v_snd_4354_; lean_object* v___x_4355_; uint8_t v___x_4356_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v_fst_4353_ = lean_ctor_get(v_a_4352_, 0);
lean_inc(v_fst_4353_);
v_snd_4354_ = lean_ctor_get(v_a_4352_, 1);
lean_inc(v_snd_4354_);
lean_dec(v_a_4352_);
v___x_4355_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4355_, 0, v_fst_4353_);
v___x_4356_ = lean_unbox(v_snd_4354_);
lean_dec(v_snd_4354_);
lean_ctor_set_uint8(v___x_4355_, sizeof(void*)*1, v___x_4356_);
v_a_4290_ = v___x_4355_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4357_; 
lean_dec(v___x_4288_);
v_a_4357_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4351_, 1);
v_a_4259_ = v_a_4357_;
goto v___jp_4258_;
}
}
default: 
{
lean_object* v___x_4358_; lean_object* v_env_4359_; lean_object* v___x_4360_; size_t v_sz_4361_; size_t v___x_4362_; lean_object* v___x_4363_; 
lean_dec_ref(v___y_4302_);
lean_dec_ref(v___y_4298_);
lean_dec(v_mod_4247_);
lean_dec(v_sp_4245_);
v___x_4358_ = lean_st_ref_get(v___y_4297_);
v_env_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc_ref(v_env_4359_);
lean_dec(v___x_4358_);
v___x_4360_ = l_Lean_Environment_mainModule(v_env_4359_);
lean_dec_ref(v_env_4359_);
v_sz_4361_ = lean_array_size(v___y_4299_);
v___x_4362_ = ((size_t)0ULL);
v___x_4363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v___x_4360_, v___y_4299_, v_sz_4361_, v___x_4362_, v___x_4286_, v___y_4300_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4299_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4363_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4363_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 2);
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
v_a_4290_ = v___x_4369_;
goto v___jp_4289_;
}
}
}
else
{
lean_object* v_a_4372_; 
lean_dec(v___x_4288_);
v_a_4372_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4363_, 1);
v_a_4259_ = v_a_4372_;
goto v___jp_4258_;
}
}
}
}
v___jp_4383_:
{
if (v___y_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_inc_ref(v___y_4385_);
v___x_4390_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4388_, v___y_4385_, v___y_4386_, v___y_4384_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
v___x_4392_ = lean_array_get_size(v_a_4391_);
v___x_4393_ = lean_nat_dec_lt(v___x_4273_, v___x_4392_);
if (v___x_4393_ == 0)
{
v___y_4297_ = v___y_4384_;
v___y_4298_ = v___y_4385_;
v___y_4299_ = v_a_4391_;
v___y_4300_ = v___y_4386_;
v___y_4301_ = v___y_4387_;
v___y_4302_ = v___y_4388_;
v___y_4303_ = v___y_4389_;
v___y_4304_ = v___y_4389_;
goto v___jp_4296_;
}
else
{
if (v___x_4393_ == 0)
{
v___y_4297_ = v___y_4384_;
v___y_4298_ = v___y_4385_;
v___y_4299_ = v_a_4391_;
v___y_4300_ = v___y_4386_;
v___y_4301_ = v___y_4387_;
v___y_4302_ = v___y_4388_;
v___y_4303_ = v___y_4389_;
v___y_4304_ = v___y_4389_;
goto v___jp_4296_;
}
else
{
size_t v___x_4394_; size_t v___x_4395_; uint8_t v___x_4396_; 
v___x_4394_ = ((size_t)0ULL);
v___x_4395_ = lean_usize_of_nat(v___x_4392_);
v___x_4396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___y_4389_, v_a_4391_, v___x_4394_, v___x_4395_);
v___y_4297_ = v___y_4384_;
v___y_4298_ = v___y_4385_;
v___y_4299_ = v_a_4391_;
v___y_4300_ = v___y_4386_;
v___y_4301_ = v___y_4387_;
v___y_4302_ = v___y_4388_;
v___y_4303_ = v___y_4389_;
v___y_4304_ = v___x_4396_;
goto v___jp_4296_;
}
}
}
else
{
lean_object* v_a_4397_; 
lean_dec_ref(v___y_4388_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec(v___x_4288_);
lean_dec(v_mod_4247_);
lean_dec(v_sp_4245_);
v_a_4397_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4390_, 1);
v_a_4259_ = v_a_4397_;
goto v___jp_4258_;
}
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
lean_dec_ref(v___y_4388_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec(v_sp_4245_);
v___x_4398_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4399_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4247_, v___y_4389_);
v___x_4400_ = lean_string_append(v___x_4398_, v___x_4399_);
lean_dec_ref(v___x_4399_);
v___x_4401_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4402_ = lean_string_append(v___x_4400_, v___x_4401_);
v___x_4403_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_4402_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v___x_4404_; 
lean_dec_ref_known(v___x_4403_, 1);
v___x_4404_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4290_ = v___x_4404_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v___x_4288_);
v_a_4405_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4407_ = v___x_4403_;
v_isShared_4408_ = v_isSharedCheck_4414_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4403_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4414_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4411_; 
v___x_4409_ = lean_io_error_to_string(v_a_4405_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set_tag(v___x_4407_, 3);
lean_ctor_set(v___x_4407_, 0, v___x_4409_);
v___x_4411_ = v___x_4407_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4409_);
v___x_4411_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_MessageData_ofFormat(v___x_4411_);
v_msg_4250_ = v___x_4412_;
goto v___jp_4249_;
}
}
}
}
}
v___jp_4415_:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4420_, v___y_4417_, v___y_4416_);
lean_dec(v___y_4420_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = lean_array_get_size(v_a_4422_);
v___x_4424_ = lean_nat_dec_eq(v___x_4423_, v___x_4273_);
if (v___x_4424_ == 0)
{
v___y_4384_ = v___y_4416_;
v___y_4385_ = v_a_4422_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___y_4418_;
v___y_4388_ = v___y_4419_;
v___y_4389_ = v___x_4424_;
goto v___jp_4383_;
}
else
{
uint8_t v___x_4425_; uint8_t v___x_4426_; 
v___x_4425_ = 0;
v___x_4426_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4418_, v___x_4425_);
v___y_4384_ = v___y_4416_;
v___y_4385_ = v_a_4422_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___y_4418_;
v___y_4388_ = v___y_4419_;
v___y_4389_ = v___x_4426_;
goto v___jp_4383_;
}
}
else
{
lean_object* v_a_4427_; 
lean_dec_ref(v___y_4419_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec(v___x_4288_);
lean_dec(v_mod_4247_);
lean_dec(v_sp_4245_);
v_a_4427_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4421_, 1);
v_a_4259_ = v_a_4427_;
goto v___jp_4258_;
}
}
v___jp_4431_:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4429_, v___y_4445_);
lean_dec(v___x_4429_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4458_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4458_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4458_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
uint8_t v_lintOnly_4451_; uint8_t v_mode_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v_lintOnly_4451_ = lean_ctor_get_uint8(v_args_4243_, sizeof(void*)*3);
v_mode_4452_ = lean_ctor_get_uint8(v_args_4243_, sizeof(void*)*3 + 1);
v___x_4453_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4441_);
lean_inc(v_quotContext_4440_);
lean_inc(v_maxHeartbeats_4439_);
lean_inc(v_openDecls_4437_);
lean_inc(v_currNamespace_4436_);
lean_inc(v_ref_4435_);
lean_inc_ref(v_fileMap_4433_);
lean_inc_ref(v_fileName_4432_);
v___x_4454_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4454_, 0, v_fileName_4432_);
lean_ctor_set(v___x_4454_, 1, v_fileMap_4433_);
lean_ctor_set(v___x_4454_, 2, v___x_4379_);
lean_ctor_set(v___x_4454_, 3, v_currRecDepth_4434_);
lean_ctor_set(v___x_4454_, 4, v___x_4453_);
lean_ctor_set(v___x_4454_, 5, v_ref_4435_);
lean_ctor_set(v___x_4454_, 6, v_currNamespace_4436_);
lean_ctor_set(v___x_4454_, 7, v_openDecls_4437_);
lean_ctor_set(v___x_4454_, 8, v_initHeartbeats_4438_);
lean_ctor_set(v___x_4454_, 9, v_maxHeartbeats_4439_);
lean_ctor_set(v___x_4454_, 10, v_quotContext_4440_);
lean_ctor_set(v___x_4454_, 11, v_currMacroScope_4441_);
lean_ctor_set(v___x_4454_, 12, v_cancelTk_x3f_4442_);
lean_ctor_set(v___x_4454_, 13, v_inheritedTraceOptions_4444_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*14, v___x_4430_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*14 + 1, v_suppressElabErrors_4443_);
if (v_lintOnly_4451_ == 0)
{
lean_del_object(v___x_4449_);
lean_dec_ref(v_linterOpts_4244_);
v___y_4416_ = v___y_4445_;
v___y_4417_ = v___x_4454_;
v___y_4418_ = v_mode_4452_;
v___y_4419_ = v_a_4447_;
v___y_4420_ = v___x_4428_;
goto v___jp_4415_;
}
else
{
lean_object* v___x_4456_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set_tag(v___x_4449_, 1);
lean_ctor_set(v___x_4449_, 0, v_linterOpts_4244_);
v___x_4456_ = v___x_4449_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_linterOpts_4244_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
v___y_4416_ = v___y_4445_;
v___y_4417_ = v___x_4454_;
v___y_4418_ = v_mode_4452_;
v___y_4419_ = v_a_4447_;
v___y_4420_ = v___x_4456_;
goto v___jp_4415_;
}
}
}
}
else
{
lean_object* v_a_4459_; 
lean_dec(v___y_4445_);
lean_dec_ref(v_inheritedTraceOptions_4444_);
lean_dec(v_cancelTk_x3f_4442_);
lean_dec(v_initHeartbeats_4438_);
lean_dec(v_currRecDepth_4434_);
lean_dec(v___x_4288_);
lean_dec(v_mod_4247_);
lean_dec(v_sp_4245_);
lean_dec_ref(v_linterOpts_4244_);
v_a_4459_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4446_, 1);
v_a_4259_ = v_a_4459_;
goto v___jp_4258_;
}
}
v___jp_4460_:
{
if (v___y_4461_ == 0)
{
lean_object* v___x_4462_; lean_object* v_env_4463_; lean_object* v_nextMacroScope_4464_; lean_object* v_ngen_4465_; lean_object* v_auxDeclNGen_4466_; lean_object* v_traceState_4467_; lean_object* v_messages_4468_; lean_object* v_infoState_4469_; lean_object* v_snapshotTasks_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4479_; 
v___x_4462_ = lean_st_ref_take(v___x_4288_);
v_env_4463_ = lean_ctor_get(v___x_4462_, 0);
v_nextMacroScope_4464_ = lean_ctor_get(v___x_4462_, 1);
v_ngen_4465_ = lean_ctor_get(v___x_4462_, 2);
v_auxDeclNGen_4466_ = lean_ctor_get(v___x_4462_, 3);
v_traceState_4467_ = lean_ctor_get(v___x_4462_, 4);
v_messages_4468_ = lean_ctor_get(v___x_4462_, 6);
v_infoState_4469_ = lean_ctor_get(v___x_4462_, 7);
v_snapshotTasks_4470_ = lean_ctor_get(v___x_4462_, 8);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v___x_4462_, 5);
lean_dec(v_unused_4480_);
v___x_4472_ = v___x_4462_;
v_isShared_4473_ = v_isSharedCheck_4479_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_snapshotTasks_4470_);
lean_inc(v_infoState_4469_);
lean_inc(v_messages_4468_);
lean_inc(v_traceState_4467_);
lean_inc(v_auxDeclNGen_4466_);
lean_inc(v_ngen_4465_);
lean_inc(v_nextMacroScope_4464_);
lean_inc(v_env_4463_);
lean_dec(v___x_4462_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4479_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = l_Lean_Kernel_enableDiag(v_env_4463_, v___x_4430_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 5, v___x_4274_);
lean_ctor_set(v___x_4472_, 0, v___x_4474_);
v___x_4476_ = v___x_4472_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_nextMacroScope_4464_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_ngen_4465_);
lean_ctor_set(v_reuseFailAlloc_4478_, 3, v_auxDeclNGen_4466_);
lean_ctor_set(v_reuseFailAlloc_4478_, 4, v_traceState_4467_);
lean_ctor_set(v_reuseFailAlloc_4478_, 5, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4478_, 6, v_messages_4468_);
lean_ctor_set(v_reuseFailAlloc_4478_, 7, v_infoState_4469_);
lean_ctor_set(v_reuseFailAlloc_4478_, 8, v_snapshotTasks_4470_);
v___x_4476_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_st_ref_put(v___x_4288_, v___x_4476_);
lean_inc(v___x_4288_);
v_fileName_4432_ = v___x_4377_;
v_fileMap_4433_ = v___x_4378_;
v_currRecDepth_4434_ = v___x_4273_;
v_ref_4435_ = v___x_4380_;
v_currNamespace_4436_ = v___x_4280_;
v_openDecls_4437_ = v___x_4281_;
v_initHeartbeats_4438_ = v___x_4276_;
v_maxHeartbeats_4439_ = v___x_4381_;
v_quotContext_4440_ = v___x_4280_;
v_currMacroScope_4441_ = v___x_4277_;
v_cancelTk_x3f_4442_ = v___x_4428_;
v_suppressElabErrors_4443_ = v___x_4382_;
v_inheritedTraceOptions_4444_ = v___x_4374_;
v___y_4445_ = v___x_4288_;
goto v___jp_4431_;
}
}
}
else
{
lean_inc(v___x_4288_);
v_fileName_4432_ = v___x_4377_;
v_fileMap_4433_ = v___x_4378_;
v_currRecDepth_4434_ = v___x_4273_;
v_ref_4435_ = v___x_4380_;
v_currNamespace_4436_ = v___x_4280_;
v_openDecls_4437_ = v___x_4281_;
v_initHeartbeats_4438_ = v___x_4276_;
v_maxHeartbeats_4439_ = v___x_4381_;
v_quotContext_4440_ = v___x_4280_;
v_currMacroScope_4441_ = v___x_4277_;
v_cancelTk_x3f_4442_ = v___x_4428_;
v_suppressElabErrors_4443_ = v___x_4382_;
v_inheritedTraceOptions_4444_ = v___x_4374_;
v___y_4445_ = v___x_4288_;
goto v___jp_4431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4482_, lean_object* v_linterOpts_4483_, lean_object* v_sp_4484_, lean_object* v_env_4485_, lean_object* v_mod_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4482_, v_linterOpts_4483_, v_sp_4484_, v_env_4485_, v_mod_4486_);
lean_dec_ref(v_args_4482_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_00_u03b4_4489_, lean_object* v_t_4490_, lean_object* v_k_4491_, lean_object* v_fallback_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___redArg(v_t_4490_, v_k_4491_, v_fallback_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_00_u03b4_4494_, lean_object* v_t_4495_, lean_object* v_k_4496_, lean_object* v_fallback_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_00_u03b4_4494_, v_t_4495_, v_k_4496_, v_fallback_4497_);
lean_dec(v_fallback_4497_);
lean_dec_ref(v_k_4496_);
lean_dec(v_t_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b2_4499_, lean_object* v_k_4500_, lean_object* v_v_4501_, lean_object* v_t_4502_, lean_object* v_hl_4503_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_k_4500_, v_v_4501_, v_t_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v_fst_4505_, lean_object* v_init_4506_, lean_object* v_x_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___redArg(v_fst_4505_, v_init_4506_, v_x_4507_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v_fst_4512_, lean_object* v_init_4513_, lean_object* v_x_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v_fst_4512_, v_init_4513_, v_x_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4519_, lean_object* v_constName_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4520_, v___y_4521_, v___y_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4525_, lean_object* v_constName_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4525_, v_constName_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11(lean_object* v_00_u03b1_4531_, lean_object* v_ref_4532_, lean_object* v_constName_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___redArg(v_ref_4532_, v_constName_4533_, v___y_4534_, v___y_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_00_u03b1_4538_, lean_object* v_ref_4539_, lean_object* v_constName_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11(v_00_u03b1_4538_, v_ref_4539_, v_constName_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v_ref_4539_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13(lean_object* v_00_u03b1_4545_, lean_object* v_ref_4546_, lean_object* v_msg_4547_, lean_object* v_declHint_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___redArg(v_ref_4546_, v_msg_4547_, v_declHint_4548_, v___y_4549_, v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13___boxed(lean_object* v_00_u03b1_4553_, lean_object* v_ref_4554_, lean_object* v_msg_4555_, lean_object* v_declHint_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13(v_00_u03b1_4553_, v_ref_4554_, v_msg_4555_, v_declHint_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v_ref_4554_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15(lean_object* v_msg_4561_, lean_object* v_declHint_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___redArg(v_msg_4561_, v_declHint_4562_, v___y_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4567_, lean_object* v_declHint_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__14_spec__15(v_msg_4567_, v_declHint_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_4573_, lean_object* v_ref_4574_, lean_object* v_msg_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___redArg(v_ref_4574_, v_msg_4575_, v___y_4576_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4580_, lean_object* v_ref_4581_, lean_object* v_msg_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15(v_00_u03b1_4580_, v_ref_4581_, v_msg_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v_ref_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4587_, lean_object* v_msg_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___redArg(v_msg_4588_, v___y_4589_, v___y_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4593_, lean_object* v_msg_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__11_spec__13_spec__15_spec__17(v_00_u03b1_4593_, v_msg_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = lean_enable_initializer_execution();
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_compacted_region_free(v_region_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4606_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4612_, lean_object* v_k_4613_, uint8_t v_v_4614_){
_start:
{
lean_object* v_map_4615_; uint8_t v_hasTrace_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4630_; 
v_map_4615_ = lean_ctor_get(v_o_4612_, 0);
v_hasTrace_4616_ = lean_ctor_get_uint8(v_o_4612_, sizeof(void*)*1);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_o_4612_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4618_ = v_o_4612_;
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_map_4615_);
lean_dec(v_o_4612_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4620_, 0, v_v_4614_);
lean_inc(v_k_4613_);
v___x_4621_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4613_, v___x_4620_, v_map_4615_);
if (v_hasTrace_4616_ == 0)
{
lean_object* v___x_4622_; uint8_t v___x_4623_; lean_object* v___x_4625_; 
v___x_4622_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4623_ = l_Lean_Name_isPrefixOf(v___x_4622_, v_k_4613_);
lean_dec(v_k_4613_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4621_);
v___x_4625_ = v___x_4618_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4621_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*1, v___x_4623_);
return v___x_4625_;
}
}
else
{
lean_object* v___x_4628_; 
lean_dec(v_k_4613_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4621_);
v___x_4628_ = v___x_4618_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4621_);
lean_ctor_set_uint8(v_reuseFailAlloc_4629_, sizeof(void*)*1, v_hasTrace_4616_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4631_, lean_object* v_k_4632_, lean_object* v_v_4633_){
_start:
{
uint8_t v_v_boxed_4634_; lean_object* v_res_4635_; 
v_v_boxed_4634_ = lean_unbox(v_v_4633_);
v_res_4635_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4631_, v_k_4632_, v_v_boxed_4634_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_4636_){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; uint32_t v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4638_ = lean_unsigned_to_nat(80u);
v___x_4639_ = l_Lean_Json_pretty(v_s_4636_, v___x_4638_);
v___x_4640_ = 10;
v___x_4641_ = lean_string_push(v___x_4639_, v___x_4640_);
v___x_4642_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__27(v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v_s_4643_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_as_4646_, size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_b_4649_){
_start:
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_usize_dec_lt(v_i_4648_, v_sz_4647_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_b_4649_);
return v___x_4652_;
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v_a_4653_ = lean_array_uget_borrowed(v_as_4646_, v_i_4648_);
lean_inc(v_a_4653_);
v___x_4654_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4653_);
v___x_4655_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v___x_4654_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v___x_4656_; size_t v___x_4657_; size_t v___x_4658_; 
lean_dec_ref_known(v___x_4655_, 1);
v___x_4656_ = lean_box(0);
v___x_4657_ = ((size_t)1ULL);
v___x_4658_ = lean_usize_add(v_i_4648_, v___x_4657_);
v_i_4648_ = v___x_4658_;
v_b_4649_ = v___x_4656_;
goto _start;
}
else
{
return v___x_4655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_as_4660_, lean_object* v_sz_4661_, lean_object* v_i_4662_, lean_object* v_b_4663_, lean_object* v___y_4664_){
_start:
{
size_t v_sz_boxed_4665_; size_t v_i_boxed_4666_; lean_object* v_res_4667_; 
v_sz_boxed_4665_ = lean_unbox_usize(v_sz_4661_);
lean_dec(v_sz_4661_);
v_i_boxed_4666_ = lean_unbox_usize(v_i_4662_);
lean_dec(v_i_4662_);
v_res_4667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v_as_4660_, v_sz_boxed_4665_, v_i_boxed_4666_, v_b_4663_);
lean_dec_ref(v_as_4660_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_as_4668_, size_t v_i_4669_, size_t v_stop_4670_, lean_object* v_b_4671_){
_start:
{
uint8_t v___x_4672_; 
v___x_4672_ = lean_usize_dec_eq(v_i_4669_, v_stop_4670_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; lean_object* v_fst_4674_; lean_object* v_snd_4675_; uint8_t v___x_4676_; lean_object* v___x_4677_; size_t v___x_4678_; size_t v___x_4679_; 
v___x_4673_ = lean_array_uget_borrowed(v_as_4668_, v_i_4669_);
v_fst_4674_ = lean_ctor_get(v___x_4673_, 0);
v_snd_4675_ = lean_ctor_get(v___x_4673_, 1);
v___x_4676_ = lean_unbox(v_snd_4675_);
lean_inc(v_fst_4674_);
v___x_4677_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4671_, v_fst_4674_, v___x_4676_);
v___x_4678_ = ((size_t)1ULL);
v___x_4679_ = lean_usize_add(v_i_4669_, v___x_4678_);
v_i_4669_ = v___x_4679_;
v_b_4671_ = v___x_4677_;
goto _start;
}
else
{
return v_b_4671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_as_4681_, lean_object* v_i_4682_, lean_object* v_stop_4683_, lean_object* v_b_4684_){
_start:
{
size_t v_i_boxed_4685_; size_t v_stop_boxed_4686_; lean_object* v_res_4687_; 
v_i_boxed_4685_ = lean_unbox_usize(v_i_4682_);
lean_dec(v_i_4682_);
v_stop_boxed_4686_ = lean_unbox_usize(v_stop_4683_);
lean_dec(v_stop_4683_);
v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_as_4681_, v_i_boxed_4685_, v_stop_boxed_4686_, v_b_4684_);
lean_dec_ref(v_as_4681_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(lean_object* v___x_4697_, lean_object* v_args_4698_, lean_object* v___x_4699_, lean_object* v_as_4700_, size_t v_sz_4701_, size_t v_i_4702_, lean_object* v_b_4703_){
_start:
{
lean_object* v_a_4706_; lean_object* v___x_4710_; uint8_t v_anyFailed_4711_; uint8_t v_anyUnlocated_4712_; lean_object* v___x_4713_; lean_object* v_envLinterModule_4714_; uint8_t v___x_4715_; 
v___x_4710_ = lean_unsigned_to_nat(0u);
v_anyFailed_4711_ = lean_nat_dec_eq(v___x_4697_, v___x_4710_);
v_anyUnlocated_4712_ = 1;
v___x_4713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3));
v_envLinterModule_4714_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4714_, 0, v___x_4713_);
lean_ctor_set_uint8(v_envLinterModule_4714_, sizeof(void*)*1, v_anyFailed_4711_);
lean_ctor_set_uint8(v_envLinterModule_4714_, sizeof(void*)*1 + 1, v_anyUnlocated_4712_);
lean_ctor_set_uint8(v_envLinterModule_4714_, sizeof(void*)*1 + 2, v_anyFailed_4711_);
v___x_4715_ = lean_usize_dec_lt(v_i_4702_, v_sz_4701_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; 
lean_dec_ref_known(v_envLinterModule_4714_, 1);
lean_dec(v___x_4699_);
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v_b_4703_);
return v___x_4716_;
}
else
{
lean_object* v___x_4717_; lean_object* v_a_4718_; lean_object* v___x_4719_; 
v___x_4717_ = lean_enable_initializer_execution();
v_a_4718_ = lean_array_uget_borrowed(v_as_4700_, v_i_4702_);
lean_inc(v_a_4718_);
v___x_4719_ = l_Lean_findOLean(v_a_4718_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4719_, 1);
v___x_4721_ = l_Lean_readModuleData(v_a_4720_);
lean_dec(v_a_4720_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v_fst_4723_; lean_object* v_snd_4724_; uint8_t v___x_4725_; lean_object* v_snd_4726_; lean_object* v_snd_4727_; lean_object* v_snd_4728_; lean_object* v_fst_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4957_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4721_, 1);
v_fst_4723_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_fst_4723_);
v_snd_4724_ = lean_ctor_get(v_a_4722_, 1);
lean_inc(v_snd_4724_);
lean_dec(v_a_4722_);
v___x_4725_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4723_);
lean_dec(v_fst_4723_);
v_snd_4726_ = lean_ctor_get(v_b_4703_, 1);
lean_inc(v_snd_4726_);
v_snd_4727_ = lean_ctor_get(v_snd_4726_, 1);
lean_inc(v_snd_4727_);
v_snd_4728_ = lean_ctor_get(v_snd_4727_, 1);
lean_inc(v_snd_4728_);
v_fst_4729_ = lean_ctor_get(v_b_4703_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v_b_4703_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v_b_4703_, 1);
lean_dec(v_unused_4958_);
v___x_4731_ = v_b_4703_;
v_isShared_4732_ = v_isSharedCheck_4957_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_fst_4729_);
lean_dec(v_b_4703_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4957_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v_fst_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4955_; 
v_fst_4733_ = lean_ctor_get(v_snd_4726_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v_snd_4726_);
if (v_isSharedCheck_4955_ == 0)
{
lean_object* v_unused_4956_; 
v_unused_4956_ = lean_ctor_get(v_snd_4726_, 1);
lean_dec(v_unused_4956_);
v___x_4735_ = v_snd_4726_;
v_isShared_4736_ = v_isSharedCheck_4955_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_fst_4733_);
lean_dec(v_snd_4726_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4955_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_fst_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4953_; 
v_fst_4737_ = lean_ctor_get(v_snd_4727_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_snd_4727_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; 
v_unused_4954_ = lean_ctor_get(v_snd_4727_, 1);
lean_dec(v_unused_4954_);
v___x_4739_ = v_snd_4727_;
v_isShared_4740_ = v_isSharedCheck_4953_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_fst_4737_);
lean_dec(v_snd_4727_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4953_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_fst_4741_; lean_object* v_snd_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4952_; 
v_fst_4741_ = lean_ctor_get(v_snd_4728_, 0);
v_snd_4742_ = lean_ctor_get(v_snd_4728_, 1);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_snd_4728_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4744_ = v_snd_4728_;
v_isShared_4745_ = v_isSharedCheck_4952_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_snd_4742_);
lean_inc(v_fst_4741_);
lean_dec(v_snd_4728_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4952_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v_anyFailed_4749_; uint8_t v_anyUnlocated_4750_; lean_object* v_records_4751_; lean_object* v_codeQualityEntries_4752_; lean_object* v___y_4846_; lean_object* v___y_4847_; uint8_t v_anyFailed_4848_; uint8_t v_anyUnlocated_4849_; lean_object* v_records_4850_; lean_object* v_codeQualityEntries_4851_; lean_object* v___y_4869_; lean_object* v___y_4870_; uint8_t v___y_4911_; 
if (v___x_4725_ == 0)
{
uint8_t v___x_4950_; 
v___x_4950_ = 2;
v___y_4911_ = v___x_4950_;
goto v___jp_4910_;
}
else
{
uint8_t v___x_4951_; 
v___x_4951_ = 1;
v___y_4911_ = v___x_4951_;
goto v___jp_4910_;
}
v___jp_4746_:
{
uint8_t v_mode_4753_; uint8_t v___x_4754_; uint8_t v___x_4755_; 
v_mode_4753_ = lean_ctor_get_uint8(v_args_4698_, sizeof(void*)*3 + 1);
v___x_4754_ = 2;
v___x_4755_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4753_, v___x_4754_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = l_Lean_Name_getRoot(v_a_4718_);
lean_inc(v___x_4699_);
v___x_4757_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4698_, v___y_4748_, v___x_4699_, v___y_4747_, v___x_4756_, v_snd_4742_);
lean_dec_ref(v___y_4748_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v_outcome_4759_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4757_, 1);
v_outcome_4759_ = lean_ctor_get(v_a_4758_, 0);
if (lean_obj_tag(v_outcome_4759_) == 0)
{
uint8_t v_failed_4760_; 
v_failed_4760_ = lean_ctor_get_uint8(v_outcome_4759_, 0);
if (v_failed_4760_ == 0)
{
lean_object* v_checkedModules_4761_; lean_object* v___x_4763_; 
v_checkedModules_4761_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_checkedModules_4761_);
lean_dec(v_a_4758_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 1, v_checkedModules_4761_);
lean_ctor_set(v___x_4744_, 0, v_codeQualityEntries_4752_);
v___x_4763_ = v___x_4744_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_codeQualityEntries_4752_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_checkedModules_4761_);
v___x_4763_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4765_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___x_4763_);
lean_ctor_set(v___x_4739_, 0, v_records_4751_);
v___x_4765_ = v___x_4739_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_records_4751_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v___x_4763_);
v___x_4765_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4766_ = lean_box(v_anyUnlocated_4750_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4765_);
lean_ctor_set(v___x_4735_, 0, v___x_4766_);
v___x_4768_ = v___x_4735_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v___x_4765_);
v___x_4768_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4769_ = lean_box(v_anyFailed_4749_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4768_);
lean_ctor_set(v___x_4731_, 0, v___x_4769_);
v___x_4771_ = v___x_4731_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4769_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v___x_4768_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
v_a_4706_ = v___x_4771_;
goto v___jp_4705_;
}
}
}
}
}
else
{
lean_object* v_checkedModules_4776_; lean_object* v___x_4778_; 
v_checkedModules_4776_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_checkedModules_4776_);
lean_dec(v_a_4758_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 1, v_checkedModules_4776_);
lean_ctor_set(v___x_4744_, 0, v_codeQualityEntries_4752_);
v___x_4778_ = v___x_4744_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_codeQualityEntries_4752_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_checkedModules_4776_);
v___x_4778_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4780_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___x_4778_);
lean_ctor_set(v___x_4739_, 0, v_records_4751_);
v___x_4780_ = v___x_4739_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_records_4751_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4781_ = lean_box(v_anyUnlocated_4750_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4780_);
lean_ctor_set(v___x_4735_, 0, v___x_4781_);
v___x_4783_ = v___x_4735_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v___x_4780_);
v___x_4783_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4784_ = lean_box(v_anyUnlocated_4712_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4783_);
lean_ctor_set(v___x_4731_, 0, v___x_4784_);
v___x_4786_ = v___x_4731_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v___x_4783_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
v_a_4706_ = v___x_4786_;
goto v___jp_4705_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4791_; lean_object* v_records_4792_; uint8_t v_unlocated_4793_; lean_object* v___x_4794_; 
lean_inc_ref(v_outcome_4759_);
v_checkedModules_4791_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_checkedModules_4791_);
lean_dec(v_a_4758_);
v_records_4792_ = lean_ctor_get(v_outcome_4759_, 0);
lean_inc_ref(v_records_4792_);
v_unlocated_4793_ = lean_ctor_get_uint8(v_outcome_4759_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4759_, 1);
v___x_4794_ = l_Array_append___redArg(v_records_4751_, v_records_4792_);
lean_dec_ref(v_records_4792_);
if (v_unlocated_4793_ == 0)
{
lean_object* v___x_4796_; 
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 1, v_checkedModules_4791_);
lean_ctor_set(v___x_4744_, 0, v_codeQualityEntries_4752_);
v___x_4796_ = v___x_4744_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_codeQualityEntries_4752_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v_checkedModules_4791_);
v___x_4796_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4798_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___x_4796_);
lean_ctor_set(v___x_4739_, 0, v___x_4794_);
v___x_4798_ = v___x_4739_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4799_ = lean_box(v_anyUnlocated_4750_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4798_);
lean_ctor_set(v___x_4735_, 0, v___x_4799_);
v___x_4801_ = v___x_4735_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v___x_4798_);
v___x_4801_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4802_ = lean_box(v_anyFailed_4749_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4801_);
lean_ctor_set(v___x_4731_, 0, v___x_4802_);
v___x_4804_ = v___x_4731_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v___x_4801_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
v_a_4706_ = v___x_4804_;
goto v___jp_4705_;
}
}
}
}
}
else
{
lean_object* v___x_4810_; 
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 1, v_checkedModules_4791_);
lean_ctor_set(v___x_4744_, 0, v_codeQualityEntries_4752_);
v___x_4810_ = v___x_4744_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_codeQualityEntries_4752_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_checkedModules_4791_);
v___x_4810_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
lean_object* v___x_4812_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___x_4810_);
lean_ctor_set(v___x_4739_, 0, v___x_4794_);
v___x_4812_ = v___x_4739_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4821_, 1, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4813_ = lean_box(v_anyUnlocated_4712_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4812_);
lean_ctor_set(v___x_4735_, 0, v___x_4813_);
v___x_4815_ = v___x_4735_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4812_);
v___x_4815_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4816_ = lean_box(v_anyFailed_4749_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4815_);
lean_ctor_set(v___x_4731_, 0, v___x_4816_);
v___x_4818_ = v___x_4731_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v___x_4815_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
v_a_4706_ = v___x_4818_;
goto v___jp_4705_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_dec_ref(v_codeQualityEntries_4752_);
lean_dec_ref(v_records_4751_);
lean_del_object(v___x_4744_);
lean_del_object(v___x_4739_);
lean_del_object(v___x_4735_);
lean_del_object(v___x_4731_);
lean_dec(v___x_4699_);
v_a_4823_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4757_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4757_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
else
{
lean_object* v___x_4832_; 
lean_dec_ref(v___y_4748_);
lean_dec_ref(v___y_4747_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v_codeQualityEntries_4752_);
v___x_4832_ = v___x_4744_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_codeQualityEntries_4752_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_snd_4742_);
v___x_4832_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
lean_object* v___x_4834_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v___x_4832_);
lean_ctor_set(v___x_4739_, 0, v_records_4751_);
v___x_4834_ = v___x_4739_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_records_4751_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4835_ = lean_box(v_anyUnlocated_4750_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4834_);
lean_ctor_set(v___x_4735_, 0, v___x_4835_);
v___x_4837_ = v___x_4735_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___x_4834_);
v___x_4837_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4838_ = lean_box(v_anyFailed_4749_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4837_);
lean_ctor_set(v___x_4731_, 0, v___x_4838_);
v___x_4840_ = v___x_4731_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___x_4837_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
v_a_4706_ = v___x_4840_;
goto v___jp_4705_;
}
}
}
}
}
}
v___jp_4845_:
{
lean_object* v___x_4852_; 
lean_inc(v_a_4718_);
lean_inc_ref(v___y_4846_);
lean_inc(v___x_4699_);
lean_inc_ref(v___y_4847_);
v___x_4852_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4698_, v___y_4847_, v___x_4699_, v___y_4846_, v_a_4718_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
switch(lean_obj_tag(v_a_4853_))
{
case 0:
{
uint8_t v_failed_4854_; 
v_failed_4854_ = lean_ctor_get_uint8(v_a_4853_, 0);
lean_dec_ref_known(v_a_4853_, 0);
if (v_failed_4854_ == 0)
{
v___y_4747_ = v___y_4846_;
v___y_4748_ = v___y_4847_;
v_anyFailed_4749_ = v_anyFailed_4848_;
v_anyUnlocated_4750_ = v_anyUnlocated_4849_;
v_records_4751_ = v_records_4850_;
v_codeQualityEntries_4752_ = v_codeQualityEntries_4851_;
goto v___jp_4746_;
}
else
{
v___y_4747_ = v___y_4846_;
v___y_4748_ = v___y_4847_;
v_anyFailed_4749_ = v_anyUnlocated_4712_;
v_anyUnlocated_4750_ = v_anyUnlocated_4849_;
v_records_4751_ = v_records_4850_;
v_codeQualityEntries_4752_ = v_codeQualityEntries_4851_;
goto v___jp_4746_;
}
}
case 1:
{
lean_object* v_records_4855_; uint8_t v_unlocated_4856_; lean_object* v___x_4857_; 
v_records_4855_ = lean_ctor_get(v_a_4853_, 0);
lean_inc_ref(v_records_4855_);
v_unlocated_4856_ = lean_ctor_get_uint8(v_a_4853_, sizeof(void*)*1);
lean_dec_ref_known(v_a_4853_, 1);
v___x_4857_ = l_Array_append___redArg(v_records_4850_, v_records_4855_);
lean_dec_ref(v_records_4855_);
if (v_unlocated_4856_ == 0)
{
v___y_4747_ = v___y_4846_;
v___y_4748_ = v___y_4847_;
v_anyFailed_4749_ = v_anyFailed_4848_;
v_anyUnlocated_4750_ = v_anyUnlocated_4849_;
v_records_4751_ = v___x_4857_;
v_codeQualityEntries_4752_ = v_codeQualityEntries_4851_;
goto v___jp_4746_;
}
else
{
v___y_4747_ = v___y_4846_;
v___y_4748_ = v___y_4847_;
v_anyFailed_4749_ = v_anyFailed_4848_;
v_anyUnlocated_4750_ = v_anyUnlocated_4712_;
v_records_4751_ = v___x_4857_;
v_codeQualityEntries_4752_ = v_codeQualityEntries_4851_;
goto v___jp_4746_;
}
}
default: 
{
lean_object* v_entries_4858_; lean_object* v___x_4859_; 
v_entries_4858_ = lean_ctor_get(v_a_4853_, 0);
lean_inc_ref(v_entries_4858_);
lean_dec_ref_known(v_a_4853_, 1);
v___x_4859_ = l_Array_append___redArg(v_codeQualityEntries_4851_, v_entries_4858_);
lean_dec_ref(v_entries_4858_);
v___y_4747_ = v___y_4846_;
v___y_4748_ = v___y_4847_;
v_anyFailed_4749_ = v_anyFailed_4848_;
v_anyUnlocated_4750_ = v_anyUnlocated_4849_;
v_records_4751_ = v_records_4850_;
v_codeQualityEntries_4752_ = v___x_4859_;
goto v___jp_4746_;
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
lean_dec_ref(v_codeQualityEntries_4851_);
lean_dec_ref(v_records_4850_);
lean_dec_ref(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_del_object(v___x_4744_);
lean_dec(v_snd_4742_);
lean_del_object(v___x_4739_);
lean_del_object(v___x_4735_);
lean_del_object(v___x_4731_);
lean_dec(v___x_4699_);
v_a_4860_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4852_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4852_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
v___jp_4868_:
{
lean_object* v___x_4871_; lean_object* v_toEnvExtension_4872_; lean_object* v_asyncMode_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v_merged_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4908_; 
v___x_4871_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_4872_ = lean_ctor_get(v___x_4871_, 0);
v_asyncMode_4873_ = lean_ctor_get(v_toEnvExtension_4872_, 2);
v___x_4874_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_4875_ = lean_box(0);
lean_inc_ref(v___y_4869_);
v___x_4876_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4874_, v___x_4871_, v___y_4869_, v_asyncMode_4873_, v___x_4875_);
v_merged_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4908_ == 0)
{
lean_object* v_unused_4909_; 
v_unused_4909_ = lean_ctor_get(v___x_4876_, 1);
lean_dec(v_unused_4909_);
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4908_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_merged_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4908_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 1, v_merged_4877_);
lean_ctor_set(v___x_4879_, 0, v___y_4870_);
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___y_4870_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_merged_4877_);
v___x_4882_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; 
v___x_4883_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4698_, v___x_4882_, v___y_4869_, v_a_4718_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4883_, 1);
switch(lean_obj_tag(v_a_4884_))
{
case 0:
{
uint8_t v___x_4885_; 
v___x_4885_ = lean_unbox(v_fst_4729_);
lean_dec(v_fst_4729_);
if (v___x_4885_ == 0)
{
uint8_t v_failed_4886_; uint8_t v___x_4887_; 
v_failed_4886_ = lean_ctor_get_uint8(v_a_4884_, 0);
lean_dec_ref_known(v_a_4884_, 0);
v___x_4887_ = lean_unbox(v_fst_4733_);
lean_dec(v_fst_4733_);
v___y_4846_ = v___y_4869_;
v___y_4847_ = v___x_4882_;
v_anyFailed_4848_ = v_failed_4886_;
v_anyUnlocated_4849_ = v___x_4887_;
v_records_4850_ = v_fst_4737_;
v_codeQualityEntries_4851_ = v_fst_4741_;
goto v___jp_4845_;
}
else
{
uint8_t v___x_4888_; 
lean_dec_ref_known(v_a_4884_, 0);
v___x_4888_ = lean_unbox(v_fst_4733_);
lean_dec(v_fst_4733_);
v___y_4846_ = v___y_4869_;
v___y_4847_ = v___x_4882_;
v_anyFailed_4848_ = v_anyUnlocated_4712_;
v_anyUnlocated_4849_ = v___x_4888_;
v_records_4850_ = v_fst_4737_;
v_codeQualityEntries_4851_ = v_fst_4741_;
goto v___jp_4845_;
}
}
case 1:
{
lean_object* v_records_4889_; uint8_t v_unlocated_4890_; lean_object* v___x_4891_; 
v_records_4889_ = lean_ctor_get(v_a_4884_, 0);
lean_inc_ref(v_records_4889_);
v_unlocated_4890_ = lean_ctor_get_uint8(v_a_4884_, sizeof(void*)*1);
lean_dec_ref_known(v_a_4884_, 1);
v___x_4891_ = l_Array_append___redArg(v_fst_4737_, v_records_4889_);
lean_dec_ref(v_records_4889_);
if (v_unlocated_4890_ == 0)
{
uint8_t v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = lean_unbox(v_fst_4729_);
lean_dec(v_fst_4729_);
v___x_4893_ = lean_unbox(v_fst_4733_);
lean_dec(v_fst_4733_);
v___y_4846_ = v___y_4869_;
v___y_4847_ = v___x_4882_;
v_anyFailed_4848_ = v___x_4892_;
v_anyUnlocated_4849_ = v___x_4893_;
v_records_4850_ = v___x_4891_;
v_codeQualityEntries_4851_ = v_fst_4741_;
goto v___jp_4845_;
}
else
{
uint8_t v___x_4894_; 
lean_dec(v_fst_4733_);
v___x_4894_ = lean_unbox(v_fst_4729_);
lean_dec(v_fst_4729_);
v___y_4846_ = v___y_4869_;
v___y_4847_ = v___x_4882_;
v_anyFailed_4848_ = v___x_4894_;
v_anyUnlocated_4849_ = v_anyUnlocated_4712_;
v_records_4850_ = v___x_4891_;
v_codeQualityEntries_4851_ = v_fst_4741_;
goto v___jp_4845_;
}
}
default: 
{
lean_object* v_entries_4895_; lean_object* v___x_4896_; uint8_t v___x_4897_; uint8_t v___x_4898_; 
v_entries_4895_ = lean_ctor_get(v_a_4884_, 0);
lean_inc_ref(v_entries_4895_);
lean_dec_ref_known(v_a_4884_, 1);
v___x_4896_ = l_Array_append___redArg(v_fst_4741_, v_entries_4895_);
lean_dec_ref(v_entries_4895_);
v___x_4897_ = lean_unbox(v_fst_4729_);
lean_dec(v_fst_4729_);
v___x_4898_ = lean_unbox(v_fst_4733_);
lean_dec(v_fst_4733_);
v___y_4846_ = v___y_4869_;
v___y_4847_ = v___x_4882_;
v_anyFailed_4848_ = v___x_4897_;
v_anyUnlocated_4849_ = v___x_4898_;
v_records_4850_ = v_fst_4737_;
v_codeQualityEntries_4851_ = v___x_4896_;
goto v___jp_4845_;
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_dec_ref(v___x_4882_);
lean_dec_ref(v___y_4869_);
lean_del_object(v___x_4744_);
lean_dec(v_snd_4742_);
lean_dec(v_fst_4741_);
lean_del_object(v___x_4739_);
lean_dec(v_fst_4737_);
lean_del_object(v___x_4735_);
lean_dec(v_fst_4733_);
lean_del_object(v___x_4731_);
lean_dec(v_fst_4729_);
lean_dec(v___x_4699_);
v_a_4899_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4883_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4883_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
}
v___jp_4910_:
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_compacted_region_free(v_snd_4724_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; uint32_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4912_, 1);
lean_inc(v_a_4718_);
v___x_4913_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4913_, 0, v_a_4718_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1, v_anyFailed_4711_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 1, v_anyUnlocated_4712_);
lean_ctor_set_uint8(v___x_4913_, sizeof(void*)*1 + 2, v_anyFailed_4711_);
v___x_4914_ = lean_unsigned_to_nat(2u);
v___x_4915_ = lean_mk_empty_array_with_capacity(v___x_4914_);
v___x_4916_ = lean_array_push(v___x_4915_, v___x_4913_);
v___x_4917_ = lean_array_push(v___x_4916_, v_envLinterModule_4714_);
v___x_4918_ = l_Lean_Options_empty;
v___x_4919_ = 1024;
v___x_4920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__4));
v___x_4921_ = lean_box(1);
v___x_4922_ = l_Lean_importModules(v___x_4917_, v___x_4918_, v___x_4919_, v___x_4920_, v_anyFailed_4711_, v_anyUnlocated_4712_, v___y_4911_, v___x_4921_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v_linterOverrides_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4922_, 1);
v_linterOverrides_4924_ = lean_ctor_get(v_args_4698_, 0);
v___x_4925_ = lean_array_get_size(v_linterOverrides_4924_);
v___x_4926_ = lean_nat_dec_lt(v___x_4710_, v___x_4925_);
if (v___x_4926_ == 0)
{
v___y_4869_ = v_a_4923_;
v___y_4870_ = v___x_4918_;
goto v___jp_4868_;
}
else
{
uint8_t v___x_4927_; 
v___x_4927_ = lean_nat_dec_le(v___x_4925_, v___x_4925_);
if (v___x_4927_ == 0)
{
if (v___x_4926_ == 0)
{
v___y_4869_ = v_a_4923_;
v___y_4870_ = v___x_4918_;
goto v___jp_4868_;
}
else
{
size_t v___x_4928_; size_t v___x_4929_; lean_object* v___x_4930_; 
v___x_4928_ = ((size_t)0ULL);
v___x_4929_ = lean_usize_of_nat(v___x_4925_);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_linterOverrides_4924_, v___x_4928_, v___x_4929_, v___x_4918_);
v___y_4869_ = v_a_4923_;
v___y_4870_ = v___x_4930_;
goto v___jp_4868_;
}
}
else
{
size_t v___x_4931_; size_t v___x_4932_; lean_object* v___x_4933_; 
v___x_4931_ = ((size_t)0ULL);
v___x_4932_ = lean_usize_of_nat(v___x_4925_);
v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_linterOverrides_4924_, v___x_4931_, v___x_4932_, v___x_4918_);
v___y_4869_ = v_a_4923_;
v___y_4870_ = v___x_4933_;
goto v___jp_4868_;
}
}
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_del_object(v___x_4744_);
lean_dec(v_snd_4742_);
lean_dec(v_fst_4741_);
lean_del_object(v___x_4739_);
lean_dec(v_fst_4737_);
lean_del_object(v___x_4735_);
lean_dec(v_fst_4733_);
lean_del_object(v___x_4731_);
lean_dec(v_fst_4729_);
lean_dec(v___x_4699_);
v_a_4934_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4922_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4922_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
lean_del_object(v___x_4744_);
lean_dec(v_snd_4742_);
lean_dec(v_fst_4741_);
lean_del_object(v___x_4739_);
lean_dec(v_fst_4737_);
lean_del_object(v___x_4735_);
lean_dec(v_fst_4733_);
lean_del_object(v___x_4731_);
lean_dec(v_fst_4729_);
lean_dec_ref_known(v_envLinterModule_4714_, 1);
lean_dec(v___x_4699_);
v_a_4942_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4912_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4912_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
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
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec_ref_known(v_envLinterModule_4714_, 1);
lean_dec_ref(v_b_4703_);
lean_dec(v___x_4699_);
v_a_4959_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4721_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4721_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec_ref_known(v_envLinterModule_4714_, 1);
lean_dec_ref(v_b_4703_);
lean_dec(v___x_4699_);
v_a_4967_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4719_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4719_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
v___jp_4705_:
{
size_t v___x_4707_; size_t v___x_4708_; 
v___x_4707_ = ((size_t)1ULL);
v___x_4708_ = lean_usize_add(v_i_4702_, v___x_4707_);
v_i_4702_ = v___x_4708_;
v_b_4703_ = v_a_4706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v___x_4975_, lean_object* v_args_4976_, lean_object* v___x_4977_, lean_object* v_as_4978_, lean_object* v_sz_4979_, lean_object* v_i_4980_, lean_object* v_b_4981_, lean_object* v___y_4982_){
_start:
{
size_t v_sz_boxed_4983_; size_t v_i_boxed_4984_; lean_object* v_res_4985_; 
v_sz_boxed_4983_ = lean_unbox_usize(v_sz_4979_);
lean_dec(v_sz_4979_);
v_i_boxed_4984_ = lean_unbox_usize(v_i_4980_);
lean_dec(v_i_4980_);
v_res_4985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_4975_, v_args_4976_, v___x_4977_, v_as_4978_, v_sz_boxed_4983_, v_i_boxed_4984_, v_b_4981_);
lean_dec_ref(v_as_4978_);
lean_dec_ref(v_args_4976_);
lean_dec(v___x_4975_);
return v_res_4985_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = l_Lean_NameSet_empty;
v___x_4987_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
lean_ctor_set(v___x_4988_, 1, v___x_4986_);
return v___x_4988_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4989_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_4990_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4990_);
lean_ctor_set(v___x_4991_, 1, v___x_4989_);
return v___x_4991_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = 0;
v___x_4994_ = lean_box_uint32(v___x_4993_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = 1;
v___x_4996_ = lean_box_uint32(v___x_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_4997_){
_start:
{
lean_object* v_mods_4999_; uint8_t v_mode_5000_; lean_object* v_srcSearchPath_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; uint8_t v_anyFailed_5004_; 
v_mods_4999_ = lean_ctor_get(v_args_4997_, 1);
lean_inc_ref(v_mods_4999_);
v_mode_5000_ = lean_ctor_get_uint8(v_args_4997_, sizeof(void*)*3 + 1);
v_srcSearchPath_5001_ = lean_ctor_get(v_args_4997_, 2);
v___x_5002_ = lean_array_get_size(v_mods_4999_);
v___x_5003_ = lean_unsigned_to_nat(0u);
v_anyFailed_5004_ = lean_nat_dec_eq(v___x_5002_, v___x_5003_);
if (v_anyFailed_5004_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; size_t v_sz_5013_; size_t v___x_5014_; lean_object* v___x_5015_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___x_5005_, 1);
lean_inc(v_srcSearchPath_5001_);
v___x_5007_ = l_List_appendTR___redArg(v_srcSearchPath_5001_, v_a_5006_);
v___x_5008_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5009_ = lean_box(v_anyFailed_5004_);
v___x_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v___x_5008_);
v___x_5011_ = lean_box(v_anyFailed_5004_);
v___x_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
lean_ctor_set(v___x_5012_, 1, v___x_5010_);
v_sz_5013_ = lean_array_size(v_mods_4999_);
v___x_5014_ = ((size_t)0ULL);
v___x_5015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_5002_, v_args_4997_, v___x_5007_, v_mods_4999_, v_sz_5013_, v___x_5014_, v___x_5012_);
lean_dec_ref(v_mods_4999_);
lean_dec_ref(v_args_4997_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5081_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5018_ = v___x_5015_;
v_isShared_5019_ = v_isSharedCheck_5081_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5081_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
switch(v_mode_5000_)
{
case 0:
{
lean_object* v_fst_5020_; uint8_t v___x_5021_; 
v_fst_5020_ = lean_ctor_get(v_a_5016_, 0);
lean_inc(v_fst_5020_);
lean_dec(v_a_5016_);
v___x_5021_ = lean_unbox(v_fst_5020_);
lean_dec(v_fst_5020_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5022_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 0, v___x_5022_);
v___x_5024_ = v___x_5018_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
else
{
lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5026_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 0, v___x_5026_);
v___x_5028_ = v___x_5018_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
case 1:
{
lean_object* v_snd_5030_; lean_object* v_snd_5031_; lean_object* v_fst_5032_; lean_object* v_fst_5033_; lean_object* v___x_5034_; 
v_snd_5030_ = lean_ctor_get(v_a_5016_, 1);
lean_inc(v_snd_5030_);
lean_del_object(v___x_5018_);
lean_dec(v_a_5016_);
v_snd_5031_ = lean_ctor_get(v_snd_5030_, 1);
lean_inc(v_snd_5031_);
v_fst_5032_ = lean_ctor_get(v_snd_5030_, 0);
lean_inc(v_fst_5032_);
lean_dec(v_snd_5030_);
v_fst_5033_ = lean_ctor_get(v_snd_5031_, 0);
lean_inc(v_fst_5033_);
lean_dec(v_snd_5031_);
v___x_5034_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5033_);
lean_dec(v_fst_5033_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5047_; 
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5047_ == 0)
{
lean_object* v_unused_5048_; 
v_unused_5048_ = lean_ctor_get(v___x_5034_, 0);
lean_dec(v_unused_5048_);
v___x_5036_ = v___x_5034_;
v_isShared_5037_ = v_isSharedCheck_5047_;
goto v_resetjp_5035_;
}
else
{
lean_dec(v___x_5034_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5047_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
uint8_t v___x_5038_; 
v___x_5038_ = lean_unbox(v_fst_5032_);
lean_dec(v_fst_5032_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; lean_object* v___x_5041_; 
v___x_5039_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 0, v___x_5039_);
v___x_5041_ = v___x_5036_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5039_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
else
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
v___x_5043_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 0, v___x_5043_);
v___x_5045_ = v___x_5036_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec(v_fst_5032_);
v_a_5049_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_5034_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_5034_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
default: 
{
lean_object* v_snd_5057_; lean_object* v_snd_5058_; lean_object* v_snd_5059_; lean_object* v_fst_5060_; lean_object* v___x_5061_; size_t v_sz_5062_; lean_object* v___x_5063_; 
v_snd_5057_ = lean_ctor_get(v_a_5016_, 1);
lean_inc(v_snd_5057_);
lean_del_object(v___x_5018_);
lean_dec(v_a_5016_);
v_snd_5058_ = lean_ctor_get(v_snd_5057_, 1);
lean_inc(v_snd_5058_);
lean_dec(v_snd_5057_);
v_snd_5059_ = lean_ctor_get(v_snd_5058_, 1);
lean_inc(v_snd_5059_);
lean_dec(v_snd_5058_);
v_fst_5060_ = lean_ctor_get(v_snd_5059_, 0);
lean_inc(v_fst_5060_);
lean_dec(v_snd_5059_);
v___x_5061_ = lean_box(0);
v_sz_5062_ = lean_array_size(v_fst_5060_);
v___x_5063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v_fst_5060_, v_sz_5062_, v___x_5014_, v___x_5061_);
lean_dec(v_fst_5060_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5071_; 
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5071_ == 0)
{
lean_object* v_unused_5072_; 
v_unused_5072_ = lean_ctor_get(v___x_5063_, 0);
lean_dec(v_unused_5072_);
v___x_5065_ = v___x_5063_;
v_isShared_5066_ = v_isSharedCheck_5071_;
goto v_resetjp_5064_;
}
else
{
lean_dec(v___x_5063_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5071_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5067_);
v___x_5069_ = v___x_5065_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
v_a_5073_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5063_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5063_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
v_a_5082_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5015_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5015_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec_ref(v_mods_4999_);
lean_dec_ref(v_args_4997_);
v_a_5090_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5005_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5005_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
lean_dec_ref(v_mods_4999_);
lean_dec_ref(v_args_4997_);
v___x_5098_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__2));
v___x_5099_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v___x_5098_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5107_; 
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v___x_5099_, 0);
lean_dec(v_unused_5108_);
v___x_5101_ = v___x_5099_;
v_isShared_5102_ = v_isSharedCheck_5107_;
goto v_resetjp_5100_;
}
else
{
lean_dec(v___x_5099_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5107_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; lean_object* v___x_5105_; 
v___x_5103_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v___x_5103_);
v___x_5105_ = v___x_5101_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5103_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
v_a_5109_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5099_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5099_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lake_BuiltinLint_run(v_args_5117_);
return v_res_5119_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_CodeQuality(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
res = runtime_initialize_Lean_Linter_CodeQuality(builtin);
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
lean_object* initialize_Lean_Linter_CodeQuality(uint8_t builtin);
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
res = initialize_Lean_Linter_CodeQuality(builtin);
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
