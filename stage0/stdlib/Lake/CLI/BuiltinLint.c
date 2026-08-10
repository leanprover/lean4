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
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_get_stderr();
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_linter_doc_deferred;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "warning: no declaration range for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_378_);
lean_dec_ref(v_s_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
return v_x_380_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_key_382_);
lean_ctor_set(v___x_385_, 1, v_value_383_);
v___x_386_ = lean_array_push(v_x_380_, v___x_385_);
v_x_380_ = v___x_386_;
v_x_381_ = v_tail_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_388_, v_x_389_);
lean_dec(v_x_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; 
v___x_396_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
v___x_397_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_394_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_392_, v___x_398_);
v_i_392_ = v___x_399_;
v_b_394_ = v___x_397_;
goto _start;
}
else
{
return v_b_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_401_, lean_object* v_i_402_, lean_object* v_stop_403_, lean_object* v_b_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_403_);
lean_dec(v_stop_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_401_, v_i_boxed_405_, v_stop_boxed_406_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_putStr_411_; lean_object* v___x_412_; 
v___x_410_ = lean_get_stderr();
v_putStr_411_ = lean_ctor_get(v___x_410_, 4);
lean_inc_ref(v_putStr_411_);
lean_dec_ref(v___x_410_);
v___x_412_ = lean_apply_2(v_putStr_411_, v_s_408_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_416_){
_start:
{
uint32_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = 10;
v___x_419_ = lean_string_push(v_s_416_, v___x_418_);
v___x_420_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
return v_x_424_;
}
else
{
lean_object* v_key_426_; lean_object* v_value_427_; lean_object* v_tail_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_key_426_ = lean_ctor_get(v_x_425_, 0);
v_value_427_ = lean_ctor_get(v_x_425_, 1);
v_tail_428_ = lean_ctor_get(v_x_425_, 2);
lean_inc(v_value_427_);
lean_inc(v_key_426_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_key_426_);
lean_ctor_set(v___x_429_, 1, v_value_427_);
v___x_430_ = lean_array_push(v_x_424_, v___x_429_);
v_x_424_ = v___x_430_;
v_x_425_ = v_tail_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_432_, v_x_433_);
lean_dec(v_x_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_435_, size_t v_i_436_, size_t v_stop_437_, lean_object* v_b_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = lean_usize_dec_eq(v_i_436_, v_stop_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; size_t v___x_442_; size_t v___x_443_; 
v___x_440_ = lean_array_uget_borrowed(v_as_435_, v_i_436_);
v___x_441_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_438_, v___x_440_);
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_436_, v___x_442_);
v_i_436_ = v___x_443_;
v_b_438_ = v___x_441_;
goto _start;
}
else
{
return v_b_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v_b_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; lean_object* v_res_451_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_445_, v_i_boxed_449_, v_stop_boxed_450_, v_b_448_);
lean_dec_ref(v_as_445_);
return v_res_451_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v_fst_454_; lean_object* v_fst_455_; uint8_t v___x_456_; 
v_fst_454_ = lean_ctor_get(v_b_453_, 0);
v_fst_455_ = lean_ctor_get(v_a_452_, 0);
v___x_456_ = lean_nat_dec_lt(v_fst_454_, v_fst_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_457_, lean_object* v_b_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_457_, v_b_458_);
lean_dec_ref(v_b_458_);
lean_dec_ref(v_a_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_461_, lean_object* v_pivot_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_k_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_nat_dec_lt(v_k_465_, v_hi_461_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_k_465_);
v___x_467_ = lean_array_fswap(v_as_463_, v_i_464_, v_hi_461_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_i_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v_fst_469_; lean_object* v___x_470_; lean_object* v_fst_471_; uint8_t v___x_472_; 
v_fst_469_ = lean_ctor_get(v_pivot_462_, 0);
v___x_470_ = lean_array_fget_borrowed(v_as_463_, v_k_465_);
v_fst_471_ = lean_ctor_get(v___x_470_, 0);
v___x_472_ = lean_nat_dec_lt(v_fst_469_, v_fst_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_k_465_, v___x_473_);
lean_dec(v_k_465_);
v_k_465_ = v___x_474_;
goto _start;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_array_fswap(v_as_463_, v_i_464_, v_k_465_);
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_i_464_, v___x_477_);
lean_dec(v_i_464_);
v___x_479_ = lean_nat_add(v_k_465_, v___x_477_);
lean_dec(v_k_465_);
v_as_463_ = v___x_476_;
v_i_464_ = v___x_478_;
v_k_465_ = v___x_479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_481_, lean_object* v_pivot_482_, lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_481_, v_pivot_482_, v_as_483_, v_i_484_, v_k_485_);
lean_dec_ref(v_pivot_482_);
lean_dec(v_hi_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_487_, lean_object* v_as_488_, lean_object* v_lo_489_, lean_object* v_hi_490_){
_start:
{
lean_object* v___y_492_; uint8_t v___x_502_; 
v___x_502_ = lean_nat_dec_lt(v_lo_489_, v_hi_490_);
if (v___x_502_ == 0)
{
lean_dec(v_lo_489_);
return v_as_488_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_mid_505_; lean_object* v___y_507_; lean_object* v___y_513_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_503_ = lean_nat_add(v_lo_489_, v_hi_490_);
v___x_504_ = lean_unsigned_to_nat(1u);
v_mid_505_ = lean_nat_shiftr(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
v___x_518_ = lean_array_fget_borrowed(v_as_488_, v_mid_505_);
v___x_519_ = lean_array_fget_borrowed(v_as_488_, v_lo_489_);
v___x_520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
v___y_513_ = v_as_488_;
goto v___jp_512_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_array_fswap(v_as_488_, v_lo_489_, v_mid_505_);
v___y_513_ = v___x_521_;
goto v___jp_512_;
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_array_fget_borrowed(v___y_507_, v_mid_505_);
v___x_509_ = lean_array_fget_borrowed(v___y_507_, v_hi_490_);
v___x_510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v_mid_505_);
v___y_492_ = v___y_507_;
goto v___jp_491_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = lean_array_fswap(v___y_507_, v_mid_505_, v_hi_490_);
lean_dec(v_mid_505_);
v___y_492_ = v___x_511_;
goto v___jp_491_;
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_array_fget_borrowed(v___y_513_, v_hi_490_);
v___x_515_ = lean_array_fget_borrowed(v___y_513_, v_lo_489_);
v___x_516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
v___y_507_ = v___y_513_;
goto v___jp_506_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_array_fswap(v___y_513_, v_lo_489_, v_hi_490_);
v___y_507_ = v___x_517_;
goto v___jp_506_;
}
}
}
v___jp_491_:
{
lean_object* v_pivot_493_; lean_object* v___x_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; uint8_t v___x_497_; 
v_pivot_493_ = lean_array_fget(v___y_492_, v_hi_490_);
lean_inc_n(v_lo_489_, 2);
v___x_494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_490_, v_pivot_493_, v___y_492_, v_lo_489_, v_lo_489_);
lean_dec(v_pivot_493_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_496_);
lean_dec_ref(v___x_494_);
v___x_497_ = lean_nat_dec_le(v_hi_490_, v_fst_495_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_487_, v_snd_496_, v_lo_489_, v_fst_495_);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_fst_495_, v___x_499_);
lean_dec(v_fst_495_);
v_as_488_ = v___x_498_;
v_lo_489_ = v___x_500_;
goto _start;
}
else
{
lean_dec(v_fst_495_);
lean_dec(v_lo_489_);
return v_snd_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_522_, lean_object* v_as_523_, lean_object* v_lo_524_, lean_object* v_hi_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_522_, v_as_523_, v_lo_524_, v_hi_525_);
lean_dec(v_hi_525_);
lean_dec(v_n_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_a_530_, lean_object* v_b_531_){
_start:
{
lean_object* v_it_533_; lean_object* v_startInclusive_534_; lean_object* v_endExclusive_535_; 
if (lean_obj_tag(v_a_530_) == 0)
{
lean_object* v_currPos_539_; lean_object* v_searcher_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_566_; 
v_currPos_539_ = lean_ctor_get(v_a_530_, 0);
v_searcher_540_ = lean_ctor_get(v_a_530_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_566_ == 0)
{
v___x_542_ = v_a_530_;
v_isShared_543_ = v_isSharedCheck_566_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_searcher_540_);
lean_inc(v_currPos_539_);
lean_dec(v_a_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_566_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_startInclusive_544_; lean_object* v_endExclusive_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_startInclusive_544_ = lean_ctor_get(v___x_528_, 1);
v_endExclusive_545_ = lean_ctor_get(v___x_528_, 2);
v___x_546_ = lean_nat_sub(v_endExclusive_545_, v_startInclusive_544_);
v___x_547_ = lean_nat_dec_eq(v_searcher_540_, v___x_546_);
lean_dec(v___x_546_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = 10;
v___x_549_ = lean_string_utf8_get_fast(v_a_527_, v_searcher_540_);
v___x_550_ = lean_uint32_dec_eq(v___x_549_, v___x_548_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_string_utf8_next_fast(v_a_527_, v_searcher_540_);
lean_dec(v_searcher_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_551_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_currPos_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_551_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v_a_530_ = v___x_553_;
goto _start;
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_slice_559_; lean_object* v_nextIt_561_; 
v___x_556_ = lean_string_utf8_next_fast(v_a_527_, v_searcher_540_);
v___x_557_ = lean_nat_sub(v___x_556_, v_searcher_540_);
v___x_558_ = lean_nat_add(v_searcher_540_, v___x_557_);
lean_dec(v___x_557_);
v_slice_559_ = l_String_Slice_subslice_x21(v___x_528_, v_currPos_539_, v_searcher_540_);
lean_inc(v___x_558_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_558_);
lean_ctor_set(v___x_542_, 0, v___x_558_);
v_nextIt_561_ = v___x_542_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_558_);
v_nextIt_561_ = v_reuseFailAlloc_564_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v_startInclusive_562_; lean_object* v_endExclusive_563_; 
v_startInclusive_562_ = lean_ctor_get(v_slice_559_, 0);
lean_inc(v_startInclusive_562_);
v_endExclusive_563_ = lean_ctor_get(v_slice_559_, 1);
lean_inc(v_endExclusive_563_);
lean_dec_ref(v_slice_559_);
v_it_533_ = v_nextIt_561_;
v_startInclusive_534_ = v_startInclusive_562_;
v_endExclusive_535_ = v_endExclusive_563_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v___x_565_; 
lean_del_object(v___x_542_);
lean_dec(v_searcher_540_);
v___x_565_ = lean_box(1);
lean_inc(v___x_529_);
v_it_533_ = v___x_565_;
v_startInclusive_534_ = v_currPos_539_;
v_endExclusive_535_ = v___x_529_;
goto v___jp_532_;
}
}
}
else
{
lean_dec(v___x_529_);
lean_dec_ref(v_a_527_);
return v_b_531_;
}
v___jp_532_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_inc_ref(v_a_527_);
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v_a_527_);
lean_ctor_set(v___x_536_, 1, v_startInclusive_534_);
lean_ctor_set(v___x_536_, 2, v_endExclusive_535_);
v___x_537_ = lean_array_push(v_b_531_, v___x_536_);
v_a_530_ = v_it_533_;
v_b_531_ = v___x_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_567_, lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_a_570_, lean_object* v_b_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_567_, v___x_568_, v___x_569_, v_a_570_, v_b_571_);
lean_dec_ref(v___x_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_573_, size_t v_i_574_, lean_object* v_bs_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_574_, v_sz_573_);
if (v___x_576_ == 0)
{
return v_bs_575_;
}
else
{
lean_object* v_v_577_; lean_object* v___x_578_; lean_object* v_bs_x27_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; 
v_v_577_ = lean_array_uget(v_bs_575_, v_i_574_);
v___x_578_ = lean_unsigned_to_nat(0u);
v_bs_x27_579_ = lean_array_uset(v_bs_575_, v_i_574_, v___x_578_);
v___x_580_ = l_String_Slice_toString(v_v_577_);
lean_dec(v_v_577_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_574_, v___x_581_);
v___x_583_ = lean_array_uset(v_bs_x27_579_, v_i_574_, v___x_580_);
v_i_574_ = v___x_582_;
v_bs_575_ = v___x_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_585_, lean_object* v_i_586_, lean_object* v_bs_587_){
_start:
{
size_t v_sz_boxed_588_; size_t v_i_boxed_589_; lean_object* v_res_590_; 
v_sz_boxed_588_ = lean_unbox_usize(v_sz_585_);
lean_dec(v_sz_585_);
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_588_, v_i_boxed_589_, v_bs_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
return v_x_591_;
}
else
{
lean_object* v_key_593_; lean_object* v_value_594_; lean_object* v_tail_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_618_; 
v_key_593_ = lean_ctor_get(v_x_592_, 0);
v_value_594_ = lean_ctor_get(v_x_592_, 1);
v_tail_595_ = lean_ctor_get(v_x_592_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_618_ == 0)
{
v___x_597_ = v_x_592_;
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_tail_595_);
lean_inc(v_value_594_);
lean_inc(v_key_593_);
lean_dec(v_x_592_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v_fold_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_599_ = lean_array_get_size(v_x_591_);
v___x_600_ = lean_uint64_of_nat(v_key_593_);
v___x_601_ = 32ULL;
v___x_602_ = lean_uint64_shift_right(v___x_600_, v___x_601_);
v_fold_603_ = lean_uint64_xor(v___x_600_, v___x_602_);
v___x_604_ = 16ULL;
v___x_605_ = lean_uint64_shift_right(v_fold_603_, v___x_604_);
v___x_606_ = lean_uint64_xor(v_fold_603_, v___x_605_);
v___x_607_ = lean_uint64_to_usize(v___x_606_);
v___x_608_ = lean_usize_of_nat(v___x_599_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v___x_608_, v___x_609_);
v___x_611_ = lean_usize_land(v___x_607_, v___x_610_);
v___x_612_ = lean_array_uget_borrowed(v_x_591_, v___x_611_);
lean_inc(v___x_612_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v___x_612_);
v___x_614_ = v___x_597_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_key_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_value_594_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_612_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_uset(v_x_591_, v___x_611_, v___x_614_);
v_x_591_ = v___x_615_;
v_x_592_ = v_tail_595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_619_, lean_object* v_source_620_, lean_object* v_target_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_source_620_);
v___x_623_ = lean_nat_dec_lt(v_i_619_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_source_620_);
lean_dec(v_i_619_);
return v_target_621_;
}
else
{
lean_object* v_es_624_; lean_object* v___x_625_; lean_object* v_source_626_; lean_object* v_target_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_es_624_ = lean_array_fget(v_source_620_, v_i_619_);
v___x_625_ = lean_box(0);
v_source_626_ = lean_array_fset(v_source_620_, v_i_619_, v___x_625_);
v_target_627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_621_, v_es_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_i_619_, v___x_628_);
lean_dec(v_i_619_);
v_i_619_ = v___x_629_;
v_source_620_ = v_source_626_;
v_target_621_ = v_target_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_nbuckets_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_array_get_size(v_data_631_);
v___x_633_ = lean_unsigned_to_nat(2u);
v_nbuckets_634_ = lean_nat_mul(v___x_632_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_box(0);
v___x_637_ = lean_mk_array(v_nbuckets_634_, v___x_636_);
v___x_638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_635_, v_data_631_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
uint8_t v___x_641_; 
v___x_641_ = 0;
return v___x_641_;
}
else
{
lean_object* v_key_642_; lean_object* v_tail_643_; uint8_t v___x_644_; 
v_key_642_ = lean_ctor_get(v_x_640_, 0);
v_tail_643_ = lean_ctor_get(v_x_640_, 2);
v___x_644_ = lean_nat_dec_eq(v_key_642_, v_a_639_);
if (v___x_644_ == 0)
{
v_x_640_ = v_tail_643_;
goto _start;
}
else
{
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_646_, lean_object* v_x_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_646_, v_x_647_);
lean_dec(v_x_647_);
lean_dec(v_a_646_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_650_, lean_object* v_b_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_dec(v_b_651_);
lean_dec(v_a_650_);
return v_x_652_;
}
else
{
lean_object* v_key_653_; lean_object* v_value_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_667_; 
v_key_653_ = lean_ctor_get(v_x_652_, 0);
v_value_654_ = lean_ctor_get(v_x_652_, 1);
v_tail_655_ = lean_ctor_get(v_x_652_, 2);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_657_ = v_x_652_;
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_value_654_);
lean_inc(v_key_653_);
lean_dec(v_x_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_nat_dec_eq(v_key_653_, v_a_650_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_650_, v_b_651_, v_tail_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_key_653_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_value_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_665_; 
lean_dec(v_value_654_);
lean_dec(v_key_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_b_651_);
lean_ctor_set(v___x_657_, 0, v_a_650_);
v___x_665_ = v___x_657_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_b_651_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_tail_655_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_668_, lean_object* v_a_669_, lean_object* v_b_670_){
_start:
{
lean_object* v_size_671_; lean_object* v_buckets_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_715_; 
v_size_671_ = lean_ctor_get(v_m_668_, 0);
v_buckets_672_ = lean_ctor_get(v_m_668_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_m_668_);
if (v_isSharedCheck_715_ == 0)
{
v___x_674_ = v_m_668_;
v_isShared_675_ = v_isSharedCheck_715_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_buckets_672_);
lean_inc(v_size_671_);
lean_dec(v_m_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_715_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v_fold_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v_bkt_689_; uint8_t v___x_690_; 
v___x_676_ = lean_array_get_size(v_buckets_672_);
v___x_677_ = lean_uint64_of_nat(v_a_669_);
v___x_678_ = 32ULL;
v___x_679_ = lean_uint64_shift_right(v___x_677_, v___x_678_);
v_fold_680_ = lean_uint64_xor(v___x_677_, v___x_679_);
v___x_681_ = 16ULL;
v___x_682_ = lean_uint64_shift_right(v_fold_680_, v___x_681_);
v___x_683_ = lean_uint64_xor(v_fold_680_, v___x_682_);
v___x_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = lean_usize_of_nat(v___x_676_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_sub(v___x_685_, v___x_686_);
v___x_688_ = lean_usize_land(v___x_684_, v___x_687_);
v_bkt_689_ = lean_array_uget_borrowed(v_buckets_672_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_669_, v_bkt_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v_size_x27_692_; lean_object* v___x_693_; lean_object* v_buckets_x27_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v_size_x27_692_ = lean_nat_add(v_size_671_, v___x_691_);
lean_dec(v_size_671_);
lean_inc(v_bkt_689_);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v_a_669_);
lean_ctor_set(v___x_693_, 1, v_b_670_);
lean_ctor_set(v___x_693_, 2, v_bkt_689_);
v_buckets_x27_694_ = lean_array_uset(v_buckets_672_, v___x_688_, v___x_693_);
v___x_695_ = lean_unsigned_to_nat(4u);
v___x_696_ = lean_nat_mul(v_size_x27_692_, v___x_695_);
v___x_697_ = lean_unsigned_to_nat(3u);
v___x_698_ = lean_nat_div(v___x_696_, v___x_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_array_get_size(v_buckets_x27_694_);
v___x_700_ = lean_nat_dec_le(v___x_698_, v___x_699_);
lean_dec(v___x_698_);
if (v___x_700_ == 0)
{
lean_object* v_val_701_; lean_object* v___x_703_; 
v_val_701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_694_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_val_701_);
lean_ctor_set(v___x_674_, 0, v_size_x27_692_);
v___x_703_ = v___x_674_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_size_x27_692_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_val_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_706_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_buckets_x27_694_);
lean_ctor_set(v___x_674_, 0, v_size_x27_692_);
v___x_706_ = v___x_674_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_x27_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_buckets_x27_694_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_708_; lean_object* v_buckets_x27_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_bkt_689_);
v___x_708_ = lean_box(0);
v_buckets_x27_709_ = lean_array_uset(v_buckets_672_, v___x_688_, v___x_708_);
v___x_710_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_669_, v_b_670_, v_bkt_689_);
v___x_711_ = lean_array_uset(v_buckets_x27_709_, v___x_688_, v___x_710_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_711_);
v___x_713_ = v___x_674_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_size_671_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_716_, lean_object* v_as_717_, size_t v_i_718_, size_t v_stop_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_eq(v_i_718_, v_stop_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_uget_borrowed(v_as_717_, v_i_718_);
v___x_722_ = lean_name_eq(v_a_716_, v___x_721_);
if (v___x_722_ == 0)
{
size_t v___x_723_; size_t v___x_724_; 
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_718_, v___x_723_);
v_i_718_ = v___x_724_;
goto _start;
}
else
{
return v___x_722_;
}
}
else
{
uint8_t v___x_726_; 
v___x_726_ = 0;
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_727_, lean_object* v_as_728_, lean_object* v_i_729_, lean_object* v_stop_730_){
_start:
{
size_t v_i_boxed_731_; size_t v_stop_boxed_732_; uint8_t v_res_733_; lean_object* v_r_734_; 
v_i_boxed_731_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_stop_boxed_732_ = lean_unbox_usize(v_stop_730_);
lean_dec(v_stop_730_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_727_, v_as_728_, v_i_boxed_731_, v_stop_boxed_732_);
lean_dec_ref(v_as_728_);
lean_dec(v_a_727_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v_as_735_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
size_t v___x_740_; size_t v___x_741_; uint8_t v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_738_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_736_, v_as_735_, v___x_740_, v___x_741_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_as_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_747_, lean_object* v_fallback_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
lean_inc(v_fallback_748_);
return v_fallback_748_;
}
else
{
lean_object* v_key_750_; lean_object* v_value_751_; lean_object* v_tail_752_; uint8_t v___x_753_; 
v_key_750_ = lean_ctor_get(v_x_749_, 0);
v_value_751_ = lean_ctor_get(v_x_749_, 1);
v_tail_752_ = lean_ctor_get(v_x_749_, 2);
v___x_753_ = lean_nat_dec_eq(v_key_750_, v_a_747_);
if (v___x_753_ == 0)
{
v_x_749_ = v_tail_752_;
goto _start;
}
else
{
lean_inc(v_value_751_);
return v_value_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_755_, lean_object* v_fallback_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_755_, v_fallback_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec(v_fallback_756_);
lean_dec(v_a_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v_buckets_762_; lean_object* v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v_fold_767_; uint64_t v___x_768_; uint64_t v___x_769_; uint64_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_buckets_762_ = lean_ctor_get(v_m_759_, 1);
v___x_763_ = lean_array_get_size(v_buckets_762_);
v___x_764_ = lean_uint64_of_nat(v_a_760_);
v___x_765_ = 32ULL;
v___x_766_ = lean_uint64_shift_right(v___x_764_, v___x_765_);
v_fold_767_ = lean_uint64_xor(v___x_764_, v___x_766_);
v___x_768_ = 16ULL;
v___x_769_ = lean_uint64_shift_right(v_fold_767_, v___x_768_);
v___x_770_ = lean_uint64_xor(v_fold_767_, v___x_769_);
v___x_771_ = lean_uint64_to_usize(v___x_770_);
v___x_772_ = lean_usize_of_nat(v___x_763_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_sub(v___x_772_, v___x_773_);
v___x_775_ = lean_usize_land(v___x_771_, v___x_774_);
v___x_776_ = lean_array_uget_borrowed(v_buckets_762_, v___x_775_);
v___x_777_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_760_, v_fallback_761_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_778_, lean_object* v_a_779_, lean_object* v_fallback_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_778_, v_a_779_, v_fallback_780_);
lean_dec(v_fallback_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_m_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_784_, size_t v_sz_785_, size_t v_i_786_, lean_object* v_b_787_){
_start:
{
lean_object* v_a_790_; uint8_t v___x_794_; 
v___x_794_ = lean_usize_dec_lt(v_i_786_, v_sz_785_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_787_);
return v___x_795_;
}
else
{
lean_object* v_a_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_a_796_ = lean_array_uget_borrowed(v_as_784_, v_i_786_);
v_fst_797_ = lean_ctor_get(v_a_796_, 0);
v_snd_798_ = lean_ctor_get(v_a_796_, 1);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_787_, v_fst_797_, v___x_799_);
v___x_801_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_800_, v_snd_798_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc(v_snd_798_);
v___x_802_ = lean_array_push(v___x_800_, v_snd_798_);
lean_inc(v_fst_797_);
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_787_, v_fst_797_, v___x_802_);
v_a_790_ = v___x_803_;
goto v___jp_789_;
}
else
{
lean_dec(v___x_800_);
v_a_790_ = v_b_787_;
goto v___jp_789_;
}
}
v___jp_789_:
{
size_t v___x_791_; size_t v___x_792_; 
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_786_, v___x_791_);
v_i_786_ = v___x_792_;
v_b_787_ = v_a_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_804_, lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_b_807_, lean_object* v___y_808_){
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_810_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_804_, v_sz_boxed_809_, v_i_boxed_810_, v_b_807_);
lean_dec_ref(v_as_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_812_){
_start:
{
lean_object* v___x_814_; lean_object* v_putStr_815_; lean_object* v___x_816_; 
v___x_814_ = lean_get_stdout();
v_putStr_815_ = lean_ctor_get(v___x_814_, 4);
lean_inc_ref(v_putStr_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = lean_apply_2(v_putStr_815_, v_s_812_, lean_box(0));
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_820_){
_start:
{
uint32_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = 10;
v___x_823_ = lean_string_push(v_s_820_, v___x_822_);
v___x_824_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_825_);
return v_res_827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_828_, lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_829_, v___x_828_);
v___x_832_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_830_, v___x_828_);
v___x_833_ = lean_string_dec_lt(v___x_831_, v___x_832_);
lean_dec_ref(v___x_832_);
lean_dec_ref(v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_834_, lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
uint8_t v___x_11634__boxed_837_; uint8_t v_res_838_; lean_object* v_r_839_; 
v___x_11634__boxed_837_ = lean_unbox(v___x_834_);
v_res_838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11634__boxed_837_, v_a_835_, v_b_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v_hi_840_, lean_object* v_pivot_841_, lean_object* v_as_842_, lean_object* v_i_843_, lean_object* v_k_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_nat_dec_lt(v_k_844_, v_hi_840_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_k_844_);
lean_dec(v_pivot_841_);
v___x_846_ = lean_array_fswap(v_as_842_, v_i_843_, v_hi_840_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_i_843_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_848_ = lean_array_fget_borrowed(v_as_842_, v_k_844_);
lean_inc(v___x_848_);
v___x_849_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_848_, v___x_845_);
lean_inc(v_pivot_841_);
v___x_850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_841_, v___x_845_);
v___x_851_ = lean_string_dec_lt(v___x_849_, v___x_850_);
lean_dec_ref(v___x_850_);
lean_dec_ref(v___x_849_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_nat_add(v_k_844_, v___x_852_);
lean_dec(v_k_844_);
v_k_844_ = v___x_853_;
goto _start;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_array_fswap(v_as_842_, v_i_843_, v_k_844_);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_i_843_, v___x_856_);
lean_dec(v_i_843_);
v___x_858_ = lean_nat_add(v_k_844_, v___x_856_);
lean_dec(v_k_844_);
v_as_842_ = v___x_855_;
v_i_843_ = v___x_857_;
v_k_844_ = v___x_858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v_hi_860_, lean_object* v_pivot_861_, lean_object* v_as_862_, lean_object* v_i_863_, lean_object* v_k_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_860_, v_pivot_861_, v_as_862_, v_i_863_, v_k_864_);
lean_dec(v_hi_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v_n_866_, lean_object* v_as_867_, lean_object* v_lo_868_, lean_object* v_hi_869_){
_start:
{
lean_object* v___y_871_; uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_lt(v_lo_868_, v_hi_869_);
if (v___x_881_ == 0)
{
lean_dec(v_lo_868_);
return v_as_867_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_mid_884_; lean_object* v___y_886_; lean_object* v___y_892_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_882_ = lean_nat_add(v_lo_868_, v_hi_869_);
v___x_883_ = lean_unsigned_to_nat(1u);
v_mid_884_ = lean_nat_shiftr(v___x_882_, v___x_883_);
lean_dec(v___x_882_);
v___x_897_ = lean_array_fget_borrowed(v_as_867_, v_mid_884_);
v___x_898_ = lean_array_fget_borrowed(v_as_867_, v_lo_868_);
lean_inc(v___x_898_);
lean_inc(v___x_897_);
v___x_899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_881_, v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
v___y_892_ = v_as_867_;
goto v___jp_891_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_array_fswap(v_as_867_, v_lo_868_, v_mid_884_);
v___y_892_ = v___x_900_;
goto v___jp_891_;
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_array_fget_borrowed(v___y_886_, v_mid_884_);
v___x_888_ = lean_array_fget_borrowed(v___y_886_, v_hi_869_);
lean_inc(v___x_888_);
lean_inc(v___x_887_);
v___x_889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_881_, v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_dec(v_mid_884_);
v___y_871_ = v___y_886_;
goto v___jp_870_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_array_fswap(v___y_886_, v_mid_884_, v_hi_869_);
lean_dec(v_mid_884_);
v___y_871_ = v___x_890_;
goto v___jp_870_;
}
}
v___jp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_array_fget_borrowed(v___y_892_, v_hi_869_);
v___x_894_ = lean_array_fget_borrowed(v___y_892_, v_lo_868_);
lean_inc(v___x_894_);
lean_inc(v___x_893_);
v___x_895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_881_, v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
v___y_886_ = v___y_892_;
goto v___jp_885_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = lean_array_fswap(v___y_892_, v_lo_868_, v_hi_869_);
v___y_886_ = v___x_896_;
goto v___jp_885_;
}
}
}
v___jp_870_:
{
lean_object* v_pivot_872_; lean_object* v___x_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; uint8_t v___x_876_; 
v_pivot_872_ = lean_array_fget(v___y_871_, v_hi_869_);
lean_inc_n(v_lo_868_, 2);
v___x_873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_869_, v_pivot_872_, v___y_871_, v_lo_868_, v_lo_868_);
v_fst_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_875_);
lean_dec_ref(v___x_873_);
v___x_876_ = lean_nat_dec_le(v_hi_869_, v_fst_874_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_866_, v_snd_875_, v_lo_868_, v_fst_874_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_fst_874_, v___x_878_);
lean_dec(v_fst_874_);
v_as_867_ = v___x_877_;
v_lo_868_ = v___x_879_;
goto _start;
}
else
{
lean_dec(v_fst_874_);
lean_dec(v_lo_868_);
return v_snd_875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v_n_901_, lean_object* v_as_902_, lean_object* v_lo_903_, lean_object* v_hi_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_901_, v_as_902_, v_lo_903_, v_hi_904_);
lean_dec(v_hi_904_);
lean_dec(v_n_901_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_912_ == 0)
{
lean_dec_ref(v___x_908_);
return v_bs_911_;
}
else
{
lean_object* v_v_913_; lean_object* v___x_914_; lean_object* v_bs_x27_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
v_v_913_ = lean_array_uget(v_bs_911_, v_i_910_);
v___x_914_ = lean_unsigned_to_nat(0u);
v_bs_x27_915_ = lean_array_uset(v_bs_911_, v_i_910_, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_908_);
v___x_917_ = lean_string_append(v___x_908_, v___x_916_);
v___x_918_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_913_, v___x_912_);
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
lean_dec_ref(v___x_918_);
v___x_920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
v___x_922_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_910_, v___x_924_);
v___x_926_ = lean_array_uset(v_bs_x27_915_, v_i_910_, v___x_923_);
v_i_910_ = v___x_925_;
v_bs_911_ = v___x_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_bs_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_933_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_928_, v_sz_boxed_932_, v_i_boxed_933_, v_bs_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_935_, size_t v_sz_936_, size_t v_i_937_, lean_object* v_b_938_){
_start:
{
lean_object* v_a_941_; uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_937_, v_sz_936_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_938_);
return v___x_946_;
}
else
{
lean_object* v_a_947_; lean_object* v_fst_948_; lean_object* v_snd_949_; lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_990_; 
v_a_947_ = lean_array_uget_borrowed(v_as_935_, v_i_937_);
v_fst_948_ = lean_ctor_get(v_a_947_, 0);
v_snd_949_ = lean_ctor_get(v_a_947_, 1);
v_fst_950_ = lean_ctor_get(v_b_938_, 0);
v_snd_951_ = lean_ctor_get(v_b_938_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_b_938_);
if (v_isSharedCheck_990_ == 0)
{
v___x_953_ = v_b_938_;
v_isShared_954_ = v_isSharedCheck_990_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_b_938_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_990_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_sub(v_fst_948_, v___x_955_);
v___x_957_ = lean_array_get_size(v_fst_950_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v___x_956_);
if (v_isShared_954_ == 0)
{
v___x_960_ = v___x_953_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_snd_951_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v_a_941_ = v___x_960_;
goto v___jp_940_;
}
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___y_966_; lean_object* v___x_979_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___x_984_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_array_fget_borrowed(v_fst_950_, v___x_956_);
v___x_964_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_963_);
v___x_979_ = lean_array_get_size(v_snd_949_);
v___x_984_ = lean_nat_dec_eq(v___x_979_, v___x_962_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___y_987_; uint8_t v___x_989_; 
v___x_985_ = lean_nat_sub(v___x_979_, v___x_955_);
v___x_989_ = lean_nat_dec_le(v___x_962_, v___x_985_);
if (v___x_989_ == 0)
{
lean_inc(v___x_985_);
v___y_987_ = v___x_985_;
goto v___jp_986_;
}
else
{
v___y_987_ = v___x_962_;
goto v___jp_986_;
}
v___jp_986_:
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_le(v___y_987_, v___x_985_);
if (v___x_988_ == 0)
{
lean_dec(v___x_985_);
lean_inc(v___y_987_);
v___y_981_ = v___y_987_;
v___y_982_ = v___y_987_;
goto v___jp_980_;
}
else
{
v___y_981_ = v___y_987_;
v___y_982_ = v___x_985_;
goto v___jp_980_;
}
}
}
else
{
lean_inc(v_snd_949_);
v___y_966_ = v_snd_949_;
goto v___jp_965_;
}
v___jp_965_:
{
size_t v_sz_967_; size_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v_sz_967_ = lean_array_size(v___y_966_);
v___x_968_ = ((size_t)0ULL);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_964_, v_sz_967_, v___x_968_, v___y_966_);
lean_inc(v___x_956_);
v___x_970_ = l_Array_extract___redArg(v_fst_950_, v___x_962_, v___x_956_);
v___x_971_ = l_Array_append___redArg(v___x_970_, v___x_969_);
v___x_972_ = l_Array_extract___redArg(v_fst_950_, v___x_956_, v___x_957_);
lean_dec(v_fst_950_);
v___x_973_ = l_Array_append___redArg(v___x_971_, v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_array_get_size(v___x_969_);
lean_dec_ref(v___x_969_);
v___x_975_ = lean_nat_add(v_snd_951_, v___x_974_);
lean_dec(v_snd_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_975_);
lean_ctor_set(v___x_953_, 0, v___x_973_);
v___x_977_ = v___x_953_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
v_a_941_ = v___x_977_;
goto v___jp_940_;
}
}
v___jp_980_:
{
lean_object* v___x_983_; 
lean_inc(v_snd_949_);
v___x_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_979_, v_snd_949_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
v___y_966_ = v___x_983_;
goto v___jp_965_;
}
}
}
}
v___jp_940_:
{
size_t v___x_942_; size_t v___x_943_; 
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_937_, v___x_942_);
v_i_937_ = v___x_943_;
v_b_938_ = v_a_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_991_, lean_object* v_sz_992_, lean_object* v_i_993_, lean_object* v_b_994_, lean_object* v___y_995_){
_start:
{
size_t v_sz_boxed_996_; size_t v_i_boxed_997_; lean_object* v_res_998_; 
v_sz_boxed_996_ = lean_unbox_usize(v_sz_992_);
lean_dec(v_sz_992_);
v_i_boxed_997_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_991_, v_sz_boxed_996_, v_i_boxed_997_, v_b_994_);
lean_dec_ref(v_as_991_);
return v_res_998_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = lean_unsigned_to_nat(16u);
v___x_1001_ = lean_mk_array(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1015_, size_t v_sz_1016_, size_t v_i_1017_, lean_object* v_b_1018_){
_start:
{
lean_object* v_a_1021_; uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_lt(v_i_1017_, v_sz_1016_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_b_1018_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v_snd_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1140_; 
v_a_1027_ = lean_array_uget_borrowed(v_as_1015_, v_i_1017_);
v_snd_1028_ = lean_ctor_get(v_a_1027_, 1);
lean_inc(v_snd_1028_);
v_fst_1029_ = lean_ctor_get(v_snd_1028_, 0);
v_snd_1030_ = lean_ctor_get(v_snd_1028_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_snd_1028_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1032_ = v_snd_1028_;
v_isShared_1033_ = v_isSharedCheck_1140_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_inc(v_fst_1029_);
lean_dec(v_snd_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1140_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_1036_ = lean_array_size(v_snd_1030_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1030_, v_sz_1036_, v___x_1037_, v___x_1035_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1054_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = lean_box(0);
v___x_1054_ = l_IO_FS_readFile(v_fst_1029_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_size_1059_; lean_object* v_buckets_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; size_t v_sz_1063_; lean_object* v___x_1064_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1108_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
lean_dec(v_snd_1030_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_n(v_a_1055_, 2);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = lean_string_utf8_byte_size(v_a_1055_);
v___x_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1034_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
v___x_1058_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_1057_);
v_size_1059_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_size_1059_);
v_buckets_1060_ = lean_ctor_get(v_a_1039_, 1);
lean_inc_ref(v_buckets_1060_);
lean_dec(v_a_1039_);
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1062_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1055_, v___x_1057_, v___x_1056_, v___x_1058_, v___x_1061_);
lean_dec_ref_known(v___x_1057_, 3);
v_sz_1063_ = lean_array_size(v___x_1062_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1063_, v___x_1037_, v___x_1062_);
v___x_1114_ = lean_mk_empty_array_with_capacity(v_size_1059_);
lean_dec(v_size_1059_);
v___x_1115_ = lean_array_get_size(v_buckets_1060_);
v___x_1116_ = lean_nat_dec_lt(v___x_1034_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_buckets_1060_);
v___y_1108_ = v___x_1114_;
goto v___jp_1107_;
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_nat_dec_le(v___x_1115_, v___x_1115_);
if (v___x_1117_ == 0)
{
if (v___x_1116_ == 0)
{
lean_dec_ref(v_buckets_1060_);
v___y_1108_ = v___x_1114_;
goto v___jp_1107_;
}
else
{
size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_usize_of_nat(v___x_1115_);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1060_, v___x_1037_, v___x_1118_, v___x_1114_);
lean_dec_ref(v_buckets_1060_);
v___y_1108_ = v___x_1119_;
goto v___jp_1107_;
}
}
else
{
size_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_usize_of_nat(v___x_1115_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1060_, v___x_1037_, v___x_1120_, v___x_1114_);
lean_dec_ref(v_buckets_1060_);
v___y_1108_ = v___x_1121_;
goto v___jp_1107_;
}
}
v___jp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1034_);
lean_ctor_set(v___x_1032_, 0, v___x_1064_);
v___x_1069_ = v___x_1032_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1034_);
v___x_1069_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
size_t v_sz_1070_; lean_object* v___x_1071_; 
v_sz_1070_ = lean_array_size(v___y_1067_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1067_, v_sz_1070_, v___x_1037_, v___x_1069_);
lean_dec_ref(v___y_1067_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_fst_1073_; lean_object* v_snd_1074_; uint8_t v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_fst_1073_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_fst_1073_);
v_snd_1074_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_snd_1074_);
lean_dec(v_a_1072_);
v___x_1075_ = lean_nat_dec_lt(v___x_1034_, v_snd_1074_);
if (v___x_1075_ == 0)
{
lean_dec(v_snd_1074_);
lean_dec(v_fst_1073_);
lean_dec(v_fst_1029_);
v_a_1021_ = v___x_1040_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1074_);
v___x_1077_ = l_Nat_reprFast(v_snd_1074_);
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
lean_dec_ref(v___x_1077_);
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_nat_dec_eq(v_snd_1074_, v___y_1066_);
lean_dec(v_snd_1074_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1042_ = v_fst_1073_;
v___y_1043_ = v___x_1080_;
v___y_1044_ = v___x_1082_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1042_ = v_fst_1073_;
v___y_1043_ = v___x_1080_;
v___y_1044_ = v___x_1083_;
goto v___jp_1041_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_fst_1029_);
v_a_1084_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1071_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1071_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1095_, v___y_1094_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec(v___y_1095_);
v___y_1066_ = v___y_1096_;
v___y_1067_ = v___x_1099_;
goto v___jp_1065_;
}
v___jp_1100_:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_le(v___y_1105_, v___y_1104_);
if (v___x_1106_ == 0)
{
lean_dec(v___y_1104_);
lean_inc(v___y_1105_);
v___y_1094_ = v___y_1101_;
v___y_1095_ = v___y_1102_;
v___y_1096_ = v___y_1103_;
v___y_1097_ = v___y_1105_;
v___y_1098_ = v___y_1105_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v___y_1101_;
v___y_1095_ = v___y_1102_;
v___y_1096_ = v___y_1103_;
v___y_1097_ = v___y_1105_;
v___y_1098_ = v___y_1104_;
goto v___jp_1093_;
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_array_get_size(v___y_1108_);
v___x_1111_ = lean_nat_dec_eq(v___x_1110_, v___x_1034_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_nat_sub(v___x_1110_, v___x_1109_);
v___x_1113_ = lean_nat_dec_le(v___x_1034_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_inc(v___x_1112_);
v___y_1101_ = v___y_1108_;
v___y_1102_ = v___x_1110_;
v___y_1103_ = v___x_1109_;
v___y_1104_ = v___x_1112_;
v___y_1105_ = v___x_1112_;
goto v___jp_1100_;
}
else
{
v___y_1101_ = v___y_1108_;
v___y_1102_ = v___x_1110_;
v___y_1103_ = v___x_1109_;
v___y_1104_ = v___x_1112_;
v___y_1105_ = v___x_1034_;
goto v___jp_1100_;
}
}
else
{
v___y_1066_ = v___x_1109_;
v___y_1067_ = v___y_1108_;
goto v___jp_1065_;
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref_known(v___x_1054_, 1);
lean_dec(v_a_1039_);
lean_del_object(v___x_1032_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1123_ = lean_string_append(v___x_1122_, v_fst_1029_);
lean_dec(v_fst_1029_);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1125_ = lean_string_append(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_array_get_size(v_snd_1030_);
lean_dec(v_snd_1030_);
v___x_1127_ = l_Nat_reprFast(v___x_1126_);
v___x_1128_ = lean_string_append(v___x_1125_, v___x_1127_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
v___x_1131_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
v_a_1021_ = v___x_1040_;
goto v___jp_1020_;
}
else
{
return v___x_1131_;
}
}
v___jp_1041_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1045_ = lean_string_append(v___y_1043_, v___y_1044_);
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1047_, v_fst_1029_);
v___x_1049_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1048_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref_known(v___x_1049_, 1);
v___x_1050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_1051_ = lean_array_to_list(v___y_1042_);
v___x_1052_ = l_String_intercalate(v___x_1050_, v___x_1051_);
v___x_1053_ = l_IO_FS_writeFile(v_fst_1029_, v___x_1052_);
lean_dec_ref(v___x_1052_);
lean_dec(v_fst_1029_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_dec_ref_known(v___x_1053_, 1);
v_a_1021_ = v___x_1040_;
goto v___jp_1020_;
}
else
{
return v___x_1053_;
}
}
else
{
lean_dec(v___y_1042_);
lean_dec(v_fst_1029_);
return v___x_1049_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_del_object(v___x_1032_);
lean_dec(v_snd_1030_);
lean_dec(v_fst_1029_);
v_a_1132_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1038_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1038_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
v___jp_1020_:
{
size_t v___x_1022_; size_t v___x_1023_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1017_, v___x_1022_);
v_i_1017_ = v___x_1023_;
v_b_1018_ = v_a_1021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1141_, lean_object* v_sz_1142_, lean_object* v_i_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1142_);
lean_dec(v_sz_1142_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1141_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1144_);
lean_dec_ref(v_as_1141_);
return v_res_1148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
return v___x_1151_;
}
else
{
lean_object* v_key_1152_; lean_object* v_tail_1153_; uint8_t v___x_1154_; 
v_key_1152_ = lean_ctor_get(v_x_1150_, 0);
v_tail_1153_ = lean_ctor_get(v_x_1150_, 2);
v___x_1154_ = lean_string_dec_eq(v_key_1152_, v_a_1149_);
if (v___x_1154_ == 0)
{
v_x_1150_ = v_tail_1153_;
goto _start;
}
else
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec_ref(v_a_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1160_, lean_object* v_b_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_dec(v_b_1161_);
lean_dec_ref(v_a_1160_);
return v_x_1162_;
}
else
{
lean_object* v_key_1163_; lean_object* v_value_1164_; lean_object* v_tail_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1177_; 
v_key_1163_ = lean_ctor_get(v_x_1162_, 0);
v_value_1164_ = lean_ctor_get(v_x_1162_, 1);
v_tail_1165_ = lean_ctor_get(v_x_1162_, 2);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1167_ = v_x_1162_;
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_tail_1165_);
lean_inc(v_value_1164_);
lean_inc(v_key_1163_);
lean_dec(v_x_1162_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_string_dec_eq(v_key_1163_, v_a_1160_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1160_, v_b_1161_, v_tail_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 2, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_key_1163_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_value_1164_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
else
{
lean_object* v___x_1175_; 
lean_dec(v_value_1164_);
lean_dec(v_key_1163_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_b_1161_);
lean_ctor_set(v___x_1167_, 0, v_a_1160_);
v___x_1175_ = v___x_1167_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1160_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_b_1161_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_tail_1165_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
return v_x_1178_;
}
else
{
lean_object* v_key_1180_; lean_object* v_value_1181_; lean_object* v_tail_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1205_; 
v_key_1180_ = lean_ctor_get(v_x_1179_, 0);
v_value_1181_ = lean_ctor_get(v_x_1179_, 1);
v_tail_1182_ = lean_ctor_get(v_x_1179_, 2);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1184_ = v_x_1179_;
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_tail_1182_);
lean_inc(v_value_1181_);
lean_inc(v_key_1180_);
lean_dec(v_x_1179_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; uint64_t v___x_1189_; uint64_t v_fold_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1186_ = lean_array_get_size(v_x_1178_);
v___x_1187_ = lean_string_hash(v_key_1180_);
v___x_1188_ = 32ULL;
v___x_1189_ = lean_uint64_shift_right(v___x_1187_, v___x_1188_);
v_fold_1190_ = lean_uint64_xor(v___x_1187_, v___x_1189_);
v___x_1191_ = 16ULL;
v___x_1192_ = lean_uint64_shift_right(v_fold_1190_, v___x_1191_);
v___x_1193_ = lean_uint64_xor(v_fold_1190_, v___x_1192_);
v___x_1194_ = lean_uint64_to_usize(v___x_1193_);
v___x_1195_ = lean_usize_of_nat(v___x_1186_);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_sub(v___x_1195_, v___x_1196_);
v___x_1198_ = lean_usize_land(v___x_1194_, v___x_1197_);
v___x_1199_ = lean_array_uget_borrowed(v_x_1178_, v___x_1198_);
lean_inc(v___x_1199_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 2, v___x_1199_);
v___x_1201_ = v___x_1184_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_key_1180_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_value_1181_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_array_uset(v_x_1178_, v___x_1198_, v___x_1201_);
v_x_1178_ = v___x_1202_;
v_x_1179_ = v_tail_1182_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1206_, lean_object* v_source_1207_, lean_object* v_target_1208_){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_array_get_size(v_source_1207_);
v___x_1210_ = lean_nat_dec_lt(v_i_1206_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec_ref(v_source_1207_);
lean_dec(v_i_1206_);
return v_target_1208_;
}
else
{
lean_object* v_es_1211_; lean_object* v___x_1212_; lean_object* v_source_1213_; lean_object* v_target_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_es_1211_ = lean_array_fget(v_source_1207_, v_i_1206_);
v___x_1212_ = lean_box(0);
v_source_1213_ = lean_array_fset(v_source_1207_, v_i_1206_, v___x_1212_);
v_target_1214_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1208_, v_es_1211_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_i_1206_, v___x_1215_);
lean_dec(v_i_1206_);
v_i_1206_ = v___x_1216_;
v_source_1207_ = v_source_1213_;
v_target_1208_ = v_target_1214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_nbuckets_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1219_ = lean_array_get_size(v_data_1218_);
v___x_1220_ = lean_unsigned_to_nat(2u);
v_nbuckets_1221_ = lean_nat_mul(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_mk_array(v_nbuckets_1221_, v___x_1223_);
v___x_1225_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1222_, v_data_1218_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_){
_start:
{
lean_object* v_size_1229_; lean_object* v_buckets_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1273_; 
v_size_1229_ = lean_ctor_get(v_m_1226_, 0);
v_buckets_1230_ = lean_ctor_get(v_m_1226_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_m_1226_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1232_ = v_m_1226_;
v_isShared_1233_ = v_isSharedCheck_1273_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_buckets_1230_);
lean_inc(v_size_1229_);
lean_dec(v_m_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1273_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; uint64_t v___x_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v_fold_1238_; uint64_t v___x_1239_; uint64_t v___x_1240_; uint64_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v_bkt_1247_; uint8_t v___x_1248_; 
v___x_1234_ = lean_array_get_size(v_buckets_1230_);
v___x_1235_ = lean_string_hash(v_a_1227_);
v___x_1236_ = 32ULL;
v___x_1237_ = lean_uint64_shift_right(v___x_1235_, v___x_1236_);
v_fold_1238_ = lean_uint64_xor(v___x_1235_, v___x_1237_);
v___x_1239_ = 16ULL;
v___x_1240_ = lean_uint64_shift_right(v_fold_1238_, v___x_1239_);
v___x_1241_ = lean_uint64_xor(v_fold_1238_, v___x_1240_);
v___x_1242_ = lean_uint64_to_usize(v___x_1241_);
v___x_1243_ = lean_usize_of_nat(v___x_1234_);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_sub(v___x_1243_, v___x_1244_);
v___x_1246_ = lean_usize_land(v___x_1242_, v___x_1245_);
v_bkt_1247_ = lean_array_uget_borrowed(v_buckets_1230_, v___x_1246_);
v___x_1248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1227_, v_bkt_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v_size_x27_1250_; lean_object* v___x_1251_; lean_object* v_buckets_x27_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v_size_x27_1250_ = lean_nat_add(v_size_1229_, v___x_1249_);
lean_dec(v_size_1229_);
lean_inc(v_bkt_1247_);
v___x_1251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1227_);
lean_ctor_set(v___x_1251_, 1, v_b_1228_);
lean_ctor_set(v___x_1251_, 2, v_bkt_1247_);
v_buckets_x27_1252_ = lean_array_uset(v_buckets_1230_, v___x_1246_, v___x_1251_);
v___x_1253_ = lean_unsigned_to_nat(4u);
v___x_1254_ = lean_nat_mul(v_size_x27_1250_, v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(3u);
v___x_1256_ = lean_nat_div(v___x_1254_, v___x_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_array_get_size(v_buckets_x27_1252_);
v___x_1258_ = lean_nat_dec_le(v___x_1256_, v___x_1257_);
lean_dec(v___x_1256_);
if (v___x_1258_ == 0)
{
lean_object* v_val_1259_; lean_object* v___x_1261_; 
v_val_1259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1252_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_val_1259_);
lean_ctor_set(v___x_1232_, 0, v_size_x27_1250_);
v___x_1261_ = v___x_1232_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_size_x27_1250_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_val_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
else
{
lean_object* v___x_1264_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_buckets_x27_1252_);
lean_ctor_set(v___x_1232_, 0, v_size_x27_1250_);
v___x_1264_ = v___x_1232_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_size_x27_1250_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_buckets_x27_1252_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v_buckets_x27_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_inc(v_bkt_1247_);
v___x_1266_ = lean_box(0);
v_buckets_x27_1267_ = lean_array_uset(v_buckets_1230_, v___x_1246_, v___x_1266_);
v___x_1268_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1227_, v_b_1228_, v_bkt_1247_);
v___x_1269_ = lean_array_uset(v_buckets_x27_1267_, v___x_1246_, v___x_1268_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1269_);
v___x_1271_ = v___x_1232_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_size_1229_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1274_, lean_object* v_fallback_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_inc(v_fallback_1275_);
return v_fallback_1275_;
}
else
{
lean_object* v_key_1277_; lean_object* v_value_1278_; lean_object* v_tail_1279_; uint8_t v___x_1280_; 
v_key_1277_ = lean_ctor_get(v_x_1276_, 0);
v_value_1278_ = lean_ctor_get(v_x_1276_, 1);
v_tail_1279_ = lean_ctor_get(v_x_1276_, 2);
v___x_1280_ = lean_string_dec_eq(v_key_1277_, v_a_1274_);
if (v___x_1280_ == 0)
{
v_x_1276_ = v_tail_1279_;
goto _start;
}
else
{
lean_inc(v_value_1278_);
return v_value_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1282_, lean_object* v_fallback_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1282_, v_fallback_1283_, v_x_1284_);
lean_dec(v_x_1284_);
lean_dec(v_fallback_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1286_, lean_object* v_a_1287_, lean_object* v_fallback_1288_){
_start:
{
lean_object* v_buckets_1289_; lean_object* v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v_fold_1294_; uint64_t v___x_1295_; uint64_t v___x_1296_; uint64_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_buckets_1289_ = lean_ctor_get(v_m_1286_, 1);
v___x_1290_ = lean_array_get_size(v_buckets_1289_);
v___x_1291_ = lean_string_hash(v_a_1287_);
v___x_1292_ = 32ULL;
v___x_1293_ = lean_uint64_shift_right(v___x_1291_, v___x_1292_);
v_fold_1294_ = lean_uint64_xor(v___x_1291_, v___x_1293_);
v___x_1295_ = 16ULL;
v___x_1296_ = lean_uint64_shift_right(v_fold_1294_, v___x_1295_);
v___x_1297_ = lean_uint64_xor(v_fold_1294_, v___x_1296_);
v___x_1298_ = lean_uint64_to_usize(v___x_1297_);
v___x_1299_ = lean_usize_of_nat(v___x_1290_);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_sub(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_usize_land(v___x_1298_, v___x_1301_);
v___x_1303_ = lean_array_uget_borrowed(v_buckets_1289_, v___x_1302_);
v___x_1304_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1287_, v_fallback_1288_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1305_, lean_object* v_a_1306_, lean_object* v_fallback_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1305_, v_a_1306_, v_fallback_1307_);
lean_dec(v_fallback_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_m_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1311_, size_t v_sz_1312_, size_t v_i_1313_, lean_object* v_b_1314_){
_start:
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_usize_dec_lt(v_i_1313_, v_sz_1312_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_b_1314_);
return v___x_1317_;
}
else
{
lean_object* v_a_1318_; lean_object* v_file_1319_; lean_object* v_pos_1320_; lean_object* v_option_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1347_; 
v_a_1318_ = lean_array_uget_borrowed(v_as_1311_, v_i_1313_);
v_file_1319_ = lean_ctor_get(v_a_1318_, 0);
v_pos_1320_ = lean_ctor_get(v_a_1318_, 1);
lean_inc_ref(v_pos_1320_);
v_option_1321_ = lean_ctor_get(v_a_1318_, 2);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1319_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_file_1319_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1314_, v_file_1319_, v___x_1323_);
lean_dec_ref_known(v___x_1323_, 2);
v_fst_1325_ = lean_ctor_get(v___x_1324_, 0);
v_snd_1326_ = lean_ctor_get(v___x_1324_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1328_ = v___x_1324_;
v_isShared_1329_ = v_isSharedCheck_1347_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snd_1326_);
lean_inc(v_fst_1325_);
lean_dec(v___x_1324_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1347_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_line_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1345_; 
v_line_1330_ = lean_ctor_get(v_pos_1320_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_pos_1320_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_pos_1320_, 1);
lean_dec(v_unused_1346_);
v___x_1332_ = v_pos_1320_;
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_line_1330_);
lean_dec(v_pos_1320_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
lean_inc(v_option_1321_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v_option_1321_);
lean_ctor_set(v___x_1328_, 0, v_line_1330_);
v___x_1335_ = v___x_1328_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_line_1330_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_option_1321_);
v___x_1335_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_array_push(v_snd_1326_, v___x_1335_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1336_);
lean_ctor_set(v___x_1332_, 0, v_fst_1325_);
v___x_1338_ = v___x_1332_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1325_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; 
lean_inc_ref(v_file_1319_);
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1314_, v_file_1319_, v___x_1338_);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1313_, v___x_1340_);
v_i_1313_ = v___x_1341_;
v_b_1314_ = v___x_1339_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1348_, lean_object* v_sz_1349_, lean_object* v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1349_);
lean_dec(v_sz_1349_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1348_, v_sz_boxed_1353_, v_i_boxed_1354_, v_b_1351_);
lean_dec_ref(v_as_1348_);
return v_res_1355_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_unsigned_to_nat(16u);
v___x_1358_ = lean_mk_array(v___x_1357_, v___x_1356_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_byFile_1361_; 
v___x_1359_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_byFile_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1361_, 0, v___x_1360_);
lean_ctor_set(v_byFile_1361_, 1, v___x_1359_);
return v_byFile_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_byFile_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
v_byFile_1365_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1366_ = lean_array_size(v_records_1362_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1362_, v_sz_1366_, v___x_1367_, v_byFile_1365_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___y_1371_; lean_object* v_size_1383_; lean_object* v_buckets_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_size_1383_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_size_1383_);
v_buckets_1384_ = lean_ctor_get(v_a_1369_, 1);
lean_inc_ref(v_buckets_1384_);
lean_dec(v_a_1369_);
v___x_1385_ = lean_mk_empty_array_with_capacity(v_size_1383_);
lean_dec(v_size_1383_);
v___x_1386_ = lean_array_get_size(v_buckets_1384_);
v___x_1387_ = lean_nat_dec_lt(v___x_1364_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v_buckets_1384_);
v___y_1371_ = v___x_1385_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_le(v___x_1386_, v___x_1386_);
if (v___x_1388_ == 0)
{
if (v___x_1387_ == 0)
{
lean_dec_ref(v_buckets_1384_);
v___y_1371_ = v___x_1385_;
goto v___jp_1370_;
}
else
{
size_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_usize_of_nat(v___x_1386_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1384_, v___x_1367_, v___x_1389_, v___x_1385_);
lean_dec_ref(v_buckets_1384_);
v___y_1371_ = v___x_1390_;
goto v___jp_1370_;
}
}
else
{
size_t v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_usize_of_nat(v___x_1386_);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1384_, v___x_1367_, v___x_1391_, v___x_1385_);
lean_dec_ref(v_buckets_1384_);
v___y_1371_ = v___x_1392_;
goto v___jp_1370_;
}
}
v___jp_1370_:
{
lean_object* v___x_1372_; size_t v_sz_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_box(0);
v_sz_1373_ = lean_array_size(v___y_1371_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1371_, v_sz_1373_, v___x_1367_, v___x_1372_);
lean_dec_ref(v___y_1371_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v___x_1374_, 0);
lean_dec(v_unused_1382_);
v___x_1376_ = v___x_1374_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v___x_1374_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1372_);
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1372_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1368_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1368_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1401_);
lean_dec_ref(v_records_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1404_, lean_object* v_m_1405_, lean_object* v_a_1406_, lean_object* v_fallback_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1405_, v_a_1406_, v_fallback_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1409_, lean_object* v_m_1410_, lean_object* v_a_1411_, lean_object* v_fallback_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1409_, v_m_1410_, v_a_1411_, v_fallback_1412_);
lean_dec(v_fallback_1412_);
lean_dec_ref(v_a_1411_);
lean_dec_ref(v_m_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_, lean_object* v_a_1416_, lean_object* v_b_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1415_, v_a_1416_, v_b_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1419_, lean_object* v_m_1420_, lean_object* v_a_1421_, lean_object* v_fallback_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1420_, v_a_1421_, v_fallback_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1424_, lean_object* v_m_1425_, lean_object* v_a_1426_, lean_object* v_fallback_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1424_, v_m_1425_, v_a_1426_, v_fallback_1427_);
lean_dec(v_fallback_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_m_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1430_, v_a_1431_, v_b_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1434_, lean_object* v___x_1435_, lean_object* v___x_1436_, lean_object* v_inst_1437_, lean_object* v_R_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1434_, v___x_1435_, v___x_1436_, v_a_1439_, v_b_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v_inst_1445_, lean_object* v_R_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1442_, v___x_1443_, v___x_1444_, v_inst_1445_, v_R_1446_, v_a_1447_, v_b_1448_);
lean_dec_ref(v___x_1443_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v_n_1450_, lean_object* v_as_1451_, lean_object* v_lo_1452_, lean_object* v_hi_1453_, lean_object* v_w_1454_, lean_object* v_hlo_1455_, lean_object* v_hhi_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v_n_1450_, v_as_1451_, v_lo_1452_, v_hi_1453_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v_n_1458_, lean_object* v_as_1459_, lean_object* v_lo_1460_, lean_object* v_hi_1461_, lean_object* v_w_1462_, lean_object* v_hlo_1463_, lean_object* v_hhi_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v_n_1458_, v_as_1459_, v_lo_1460_, v_hi_1461_, v_w_1462_, v_hlo_1463_, v_hhi_1464_);
lean_dec(v_hi_1461_);
lean_dec(v_n_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1466_, lean_object* v_as_1467_, lean_object* v_lo_1468_, lean_object* v_hi_1469_, lean_object* v_w_1470_, lean_object* v_hlo_1471_, lean_object* v_hhi_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1466_, v_as_1467_, v_lo_1468_, v_hi_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1474_, lean_object* v_as_1475_, lean_object* v_lo_1476_, lean_object* v_hi_1477_, lean_object* v_w_1478_, lean_object* v_hlo_1479_, lean_object* v_hhi_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1474_, v_as_1475_, v_lo_1476_, v_hi_1477_, v_w_1478_, v_hlo_1479_, v_hhi_1480_);
lean_dec(v_hi_1477_);
lean_dec(v_n_1474_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1482_, lean_object* v_a_1483_, lean_object* v_fallback_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1483_, v_fallback_1484_, v_x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_fallback_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1487_, v_a_1488_, v_fallback_1489_, v_x_1490_);
lean_dec(v_x_1490_);
lean_dec(v_fallback_1489_);
lean_dec_ref(v_a_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1492_, lean_object* v_a_1493_, lean_object* v_x_1494_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1493_, v_x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1496_, lean_object* v_a_1497_, lean_object* v_x_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1496_, v_a_1497_, v_x_1498_);
lean_dec(v_x_1498_);
lean_dec_ref(v_a_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1501_, lean_object* v_data_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1504_, lean_object* v_a_1505_, lean_object* v_b_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1505_, v_b_1506_, v_x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1509_, lean_object* v_a_1510_, lean_object* v_fallback_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1510_, v_fallback_1511_, v_x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1514_, lean_object* v_a_1515_, lean_object* v_fallback_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1514_, v_a_1515_, v_fallback_1516_, v_x_1517_);
lean_dec(v_x_1517_);
lean_dec(v_fallback_1516_);
lean_dec(v_a_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1519_, lean_object* v_a_1520_, lean_object* v_x_1521_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1520_, v_x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1523_, lean_object* v_a_1524_, lean_object* v_x_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1523_, v_a_1524_, v_x_1525_);
lean_dec(v_x_1525_);
lean_dec(v_a_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1528_, lean_object* v_data_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1531_, lean_object* v_a_1532_, lean_object* v_b_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1532_, v_b_1533_, v_x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v_n_1536_, lean_object* v_lo_1537_, lean_object* v_hi_1538_, lean_object* v_hhi_1539_, lean_object* v_pivot_1540_, lean_object* v_as_1541_, lean_object* v_i_1542_, lean_object* v_k_1543_, lean_object* v_ilo_1544_, lean_object* v_ik_1545_, lean_object* v_w_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v_hi_1538_, v_pivot_1540_, v_as_1541_, v_i_1542_, v_k_1543_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v_n_1548_, lean_object* v_lo_1549_, lean_object* v_hi_1550_, lean_object* v_hhi_1551_, lean_object* v_pivot_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_k_1555_, lean_object* v_ilo_1556_, lean_object* v_ik_1557_, lean_object* v_w_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v_n_1548_, v_lo_1549_, v_hi_1550_, v_hhi_1551_, v_pivot_1552_, v_as_1553_, v_i_1554_, v_k_1555_, v_ilo_1556_, v_ik_1557_, v_w_1558_);
lean_dec(v_hi_1550_);
lean_dec(v_lo_1549_);
lean_dec(v_n_1548_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1560_, lean_object* v_lo_1561_, lean_object* v_hi_1562_, lean_object* v_hhi_1563_, lean_object* v_pivot_1564_, lean_object* v_as_1565_, lean_object* v_i_1566_, lean_object* v_k_1567_, lean_object* v_ilo_1568_, lean_object* v_ik_1569_, lean_object* v_w_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1562_, v_pivot_1564_, v_as_1565_, v_i_1566_, v_k_1567_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1572_, lean_object* v_lo_1573_, lean_object* v_hi_1574_, lean_object* v_hhi_1575_, lean_object* v_pivot_1576_, lean_object* v_as_1577_, lean_object* v_i_1578_, lean_object* v_k_1579_, lean_object* v_ilo_1580_, lean_object* v_ik_1581_, lean_object* v_w_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1572_, v_lo_1573_, v_hi_1574_, v_hhi_1575_, v_pivot_1576_, v_as_1577_, v_i_1578_, v_k_1579_, v_ilo_1580_, v_ik_1581_, v_w_1582_);
lean_dec_ref(v_pivot_1576_);
lean_dec(v_hi_1574_);
lean_dec(v_lo_1573_);
lean_dec(v_n_1572_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1584_, lean_object* v_i_1585_, lean_object* v_source_1586_, lean_object* v_target_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1585_, v_source_1586_, v_target_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1589_, lean_object* v_i_1590_, lean_object* v_source_1591_, lean_object* v_target_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1590_, v_source_1591_, v_target_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1595_, v_x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1599_, v_x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v_env_1606_; lean_object* v___x_1607_; lean_object* v_env_1608_; lean_object* v___x_1609_; lean_object* v_toEnvExtension_1610_; lean_object* v_asyncMode_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1605_ = lean_st_ref_get(v___y_1603_);
v_env_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1605_);
v___x_1607_ = lean_st_ref_get(v___y_1603_);
v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = l_Lean_declRangeExt;
v_toEnvExtension_1610_ = lean_ctor_get(v___x_1609_, 0);
v_asyncMode_1611_ = lean_ctor_get(v_toEnvExtension_1610_, 2);
v___x_1612_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1613_ = 0;
lean_inc(v_declName_1602_);
v___x_1614_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1612_, v___x_1609_, v_env_1606_, v_declName_1602_, v_asyncMode_1611_, v___x_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = 1;
v___x_1616_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1612_, v___x_1609_, v_env_1608_, v_declName_1602_, v_asyncMode_1611_, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
lean_dec_ref(v_env_1608_);
lean_dec(v_declName_1602_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1619_, v___y_1620_);
lean_dec(v___y_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v_env_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1626_ = lean_st_ref_get(v___y_1624_);
v_env_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1627_);
lean_dec(v___x_1626_);
v___x_1628_ = l_Lean_isRecCore(v_env_1627_, v_declName_1623_);
v___x_1629_ = lean_box(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1631_, v___y_1632_);
lean_dec(v___y_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_ranges_1640_; lean_object* v___x_1646_; lean_object* v_env_1647_; lean_object* v___x_1648_; lean_object* v_a_1649_; uint8_t v___y_1655_; uint8_t v___x_1659_; 
v___x_1646_ = lean_st_ref_get(v___y_1637_);
v_env_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_ref_n(v_env_1647_, 2);
lean_dec(v___x_1646_);
lean_inc_n(v_declName_1635_, 2);
v___x_1648_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1635_, v___y_1637_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1659_ = l_Lean_isAuxRecursor(v_env_1647_, v_declName_1635_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; 
lean_inc(v_declName_1635_);
v___x_1660_ = l_Lean_isNoConfusion(v_env_1647_, v_declName_1635_);
v___y_1655_ = v___x_1660_;
goto v___jp_1654_;
}
else
{
lean_dec_ref(v_env_1647_);
v___y_1655_ = v___x_1659_;
goto v___jp_1654_;
}
v___jp_1639_:
{
if (lean_obj_tag(v_ranges_1640_) == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = l_Lean_builtinDeclRanges;
v___x_1642_ = lean_st_ref_get(v___x_1641_);
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1642_, v_declName_1635_);
lean_dec(v_declName_1635_);
lean_dec(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; 
lean_dec(v_declName_1635_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_ranges_1640_);
return v___x_1645_;
}
}
v___jp_1650_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; 
v___x_1651_ = l_Lean_Name_getPrefix(v_declName_1635_);
v___x_1652_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1651_, v___y_1637_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v_ranges_1640_ = v_a_1653_;
goto v___jp_1639_;
}
v___jp_1654_:
{
if (v___y_1655_ == 0)
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v_a_1658_; 
lean_inc(v_declName_1635_);
v___x_1657_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1635_, v___y_1637_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
v_ranges_1640_ = v_a_1658_;
goto v___jp_1639_;
}
else
{
goto v___jp_1650_;
}
}
else
{
lean_dec(v_a_1649_);
goto v___jp_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1666_, lean_object* v_site_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
if (lean_obj_tag(v_site_1667_) == 0)
{
lean_object* v_name_1671_; lean_object* v___x_1672_; 
v_name_1671_ = lean_ctor_get(v_site_1667_, 0);
lean_inc(v_name_1671_);
lean_dec_ref_known(v_site_1667_, 1);
v___x_1672_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1671_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1694_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1694_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1694_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
if (lean_obj_tag(v_a_1673_) == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_box(0);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1693_; 
v_val_1681_ = lean_ctor_get(v_a_1673_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1673_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1683_ = v_a_1673_;
v_isShared_1684_ = v_isSharedCheck_1693_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_val_1681_);
lean_dec(v_a_1673_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1693_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_range_1685_; lean_object* v_pos_1686_; lean_object* v___x_1688_; 
v_range_1685_ = lean_ctor_get(v_val_1681_, 0);
lean_inc_ref(v_range_1685_);
lean_dec(v_val_1681_);
v_pos_1686_ = lean_ctor_get(v_range_1685_, 0);
lean_inc_ref(v_pos_1686_);
lean_dec_ref(v_range_1685_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v_pos_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1688_);
v___x_1690_ = v___x_1675_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1672_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1672_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_n_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1734_; 
v_n_1703_ = lean_ctor_get(v_site_1667_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_site_1667_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1705_ = v_site_1667_;
v_isShared_1706_ = v_isSharedCheck_1734_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_n_1703_);
lean_dec(v_site_1667_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1734_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v_env_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_st_ref_get(v_a_1669_);
v_env_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc_ref(v_env_1708_);
lean_dec(v___x_1707_);
v___x_1709_ = l_Lean_getVersoModuleDoc_x3f(v_env_1708_, v_failMod_1666_);
lean_dec_ref(v_env_1708_);
if (lean_obj_tag(v___x_1709_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1729_; 
v_val_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_val_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = lean_array_get_size(v_val_1710_);
v___x_1715_ = lean_nat_dec_lt(v_n_1703_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_del_object(v___x_1712_);
lean_dec(v_val_1710_);
lean_dec(v_n_1703_);
v___x_1716_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1716_);
v___x_1718_ = v___x_1705_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v_declarationRange_1721_; lean_object* v_pos_1722_; lean_object* v___x_1724_; 
v___x_1720_ = lean_array_fget(v_val_1710_, v_n_1703_);
lean_dec(v_n_1703_);
lean_dec(v_val_1710_);
v_declarationRange_1721_ = lean_ctor_get(v___x_1720_, 2);
lean_inc_ref(v_declarationRange_1721_);
lean_dec(v___x_1720_);
v_pos_1722_ = lean_ctor_get(v_declarationRange_1721_, 0);
lean_inc_ref(v_pos_1722_);
lean_dec_ref(v_declarationRange_1721_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v_pos_1722_);
v___x_1724_ = v___x_1712_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_pos_1722_);
v___x_1724_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1726_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1724_);
v___x_1726_ = v___x_1705_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_dec(v___x_1709_);
lean_dec(v_n_1703_);
v___x_1730_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1730_);
v___x_1732_ = v___x_1705_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1735_, lean_object* v_site_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1735_, v_site_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_failMod_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1741_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1751_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1764_){
_start:
{
if (lean_obj_tag(v_x_1764_) == 0)
{
lean_object* v_name_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_name_1765_ = lean_ctor_get(v_x_1764_, 0);
lean_inc(v_name_1765_);
lean_dec_ref_known(v_x_1764_, 1);
v___x_1766_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1767_ = 1;
v___x_1768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1765_, v___x_1767_);
v___x_1769_ = lean_string_append(v___x_1766_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_n_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_n_1772_ = lean_ctor_get(v_x_1764_, 0);
lean_inc(v_n_1772_);
lean_dec_ref_known(v_x_1764_, 1);
v___x_1773_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_n_1772_, v___x_1774_);
lean_dec(v_n_1772_);
v___x_1776_ = l_Nat_reprFast(v___x_1775_);
v___x_1777_ = lean_string_append(v___x_1773_, v___x_1776_);
lean_dec_ref(v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v_env_1782_; lean_object* v___x_1783_; lean_object* v_toEnvExtension_1784_; lean_object* v_asyncMode_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_merged_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1797_; 
v___x_1781_ = lean_st_ref_get(v___y_1779_);
v_env_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc_ref(v_env_1782_);
lean_dec(v___x_1781_);
v___x_1783_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1784_ = lean_ctor_get(v___x_1783_, 0);
v_asyncMode_1785_ = lean_ctor_get(v_toEnvExtension_1784_, 2);
v___x_1786_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1787_ = lean_box(0);
v___x_1788_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1786_, v___x_1783_, v_env_1782_, v_asyncMode_1785_, v___x_1787_);
v_merged_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1788_, 1);
lean_dec(v_unused_1798_);
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_merged_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v_merged_1789_);
lean_ctor_set(v___x_1791_, 0, v_o_1778_);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_o_1778_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_merged_1789_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1799_, v___y_1800_);
lean_dec(v___y_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1803_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1813_, lean_object* v_opt_1814_){
_start:
{
lean_object* v_name_1815_; lean_object* v_defValue_1816_; lean_object* v_map_1817_; lean_object* v___x_1818_; 
v_name_1815_ = lean_ctor_get(v_opt_1814_, 0);
v_defValue_1816_ = lean_ctor_get(v_opt_1814_, 1);
v_map_1817_ = lean_ctor_get(v_opts_1813_, 0);
v___x_1818_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1817_, v_name_1815_);
if (lean_obj_tag(v___x_1818_) == 0)
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_unbox(v_defValue_1816_);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; 
v_val_1820_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v___x_1818_, 1);
if (lean_obj_tag(v_val_1820_) == 1)
{
uint8_t v_v_1821_; 
v_v_1821_ = lean_ctor_get_uint8(v_val_1820_, 0);
lean_dec_ref_known(v_val_1820_, 0);
return v_v_1821_;
}
else
{
uint8_t v___x_1822_; 
lean_dec(v_val_1820_);
v___x_1822_ = lean_unbox(v_defValue_1816_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1823_, lean_object* v_opt_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1823_, v_opt_1824_);
lean_dec_ref(v_opt_1824_);
lean_dec_ref(v_opts_1823_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1827_, lean_object* v_opt_1828_){
_start:
{
lean_object* v_name_1829_; lean_object* v_defValue_1830_; lean_object* v_map_1831_; lean_object* v___x_1832_; 
v_name_1829_ = lean_ctor_get(v_opt_1828_, 0);
v_defValue_1830_ = lean_ctor_get(v_opt_1828_, 1);
v_map_1831_ = lean_ctor_get(v_opts_1827_, 0);
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1831_, v_name_1829_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_inc(v_defValue_1830_);
return v_defValue_1830_;
}
else
{
lean_object* v_val_1833_; 
v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v___x_1832_, 1);
if (lean_obj_tag(v_val_1833_) == 3)
{
lean_object* v_v_1834_; 
v_v_1834_ = lean_ctor_get(v_val_1833_, 0);
lean_inc(v_v_1834_);
lean_dec_ref_known(v_val_1833_, 1);
return v_v_1834_;
}
else
{
lean_dec(v_val_1833_);
lean_inc(v_defValue_1830_);
return v_defValue_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1835_, lean_object* v_opt_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1835_, v_opt_1836_);
lean_dec_ref(v_opt_1836_);
lean_dec_ref(v_opts_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_options_1842_; lean_object* v___x_1843_; lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1854_; 
v_options_1842_ = lean_ctor_get(v_c_1838_, 6);
lean_inc_ref(v_options_1842_);
lean_dec_ref(v_c_1838_);
v___x_1843_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1842_, v___y_1840_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1848_ = l_Lean_linter_doc_deferred;
v___x_1849_ = l_Lean_Linter_getLinterValue(v___x_1848_, v_a_1844_);
lean_dec(v_a_1844_);
v___x_1850_ = lean_box(v___x_1849_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1850_);
v___x_1852_ = v___x_1846_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1860_, lean_object* v_docCheckedModules_1861_, lean_object* v_m_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1860_, v_m_1862_);
if (v___x_1863_ == 0)
{
return v___x_1863_;
}
else
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_NameSet_contains(v_docCheckedModules_1861_, v_m_1862_);
if (v___x_1864_ == 0)
{
return v___x_1863_;
}
else
{
uint8_t v___x_1865_; 
v___x_1865_ = 0;
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1866_, lean_object* v_docCheckedModules_1867_, lean_object* v_m_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1866_, v_docCheckedModules_1867_, v_m_1868_);
lean_dec(v_m_1868_);
lean_dec(v_docCheckedModules_1867_);
lean_dec(v_pkgRoot_1866_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_1878_, lean_object* v_sp_1879_, lean_object* v_as_1880_, size_t v_sz_1881_, size_t v_i_1882_, lean_object* v_b_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_a_1888_; uint8_t v_unlocated_1892_; 
v_unlocated_1892_ = lean_usize_dec_lt(v_i_1882_, v_sz_1881_);
if (v_unlocated_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec(v_sp_1879_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_b_1883_);
return v___x_1893_;
}
else
{
lean_object* v_a_1894_; lean_object* v_snd_1895_; lean_object* v_fst_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_2025_; 
v_a_1894_ = lean_array_uget_borrowed(v_as_1880_, v_i_1882_);
v_snd_1895_ = lean_ctor_get(v_a_1894_, 1);
lean_inc(v_snd_1895_);
v_fst_1896_ = lean_ctor_get(v_snd_1895_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_snd_1895_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v_snd_1895_, 1);
lean_dec(v_unused_2026_);
v___x_1898_ = v_snd_1895_;
v_isShared_1899_ = v_isSharedCheck_2025_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_fst_1896_);
lean_dec(v_snd_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_2025_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_fst_1900_; lean_object* v_site_1901_; lean_object* v___x_1902_; 
v_fst_1900_ = lean_ctor_get(v_a_1894_, 0);
v_site_1901_ = lean_ctor_get(v_fst_1896_, 0);
lean_inc_ref_n(v_site_1901_, 2);
lean_dec(v_fst_1896_);
v___x_1902_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_1900_, v_site_1901_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
if (lean_obj_tag(v_a_1903_) == 0)
{
lean_object* v_fst_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1943_; 
v_fst_1904_ = lean_ctor_get(v_b_1883_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_b_1883_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_b_1883_, 1);
lean_dec(v_unused_1944_);
v___x_1906_ = v_b_1883_;
v_isShared_1907_ = v_isSharedCheck_1943_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_fst_1904_);
lean_dec(v_b_1883_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1943_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v_name_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1908_ = l_Lean_linter_doc_deferred;
v_name_1909_ = lean_ctor_get(v___x_1908_, 0);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_1911_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1901_);
v___x_1912_ = lean_string_append(v___x_1910_, v___x_1911_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
lean_inc(v_fst_1900_);
v___x_1915_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1900_, v___x_1878_);
v___x_1916_ = lean_string_append(v___x_1914_, v___x_1915_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_1918_ = lean_string_append(v___x_1916_, v___x_1917_);
lean_inc(v_name_1909_);
v___x_1919_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1909_, v___x_1878_);
v___x_1920_ = lean_string_append(v___x_1918_, v___x_1919_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1922_ = lean_string_append(v___x_1920_, v___x_1921_);
v___x_1923_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1922_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec_ref_known(v___x_1923_, 1);
lean_del_object(v___x_1898_);
v___x_1924_ = lean_box(v_unlocated_1892_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1924_);
v___x_1926_ = v___x_1906_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_fst_1904_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
v_a_1888_ = v___x_1926_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1906_);
lean_dec(v_fst_1904_);
lean_dec(v_sp_1879_);
v_a_1928_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1930_ = v___x_1923_;
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1923_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_ref_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v_ref_1932_ = lean_ctor_get(v___y_1884_, 5);
v___x_1933_ = lean_io_error_to_string(v_a_1928_);
v___x_1934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___x_1935_ = l_Lean_MessageData_ofFormat(v___x_1934_);
lean_inc(v_ref_1932_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___x_1935_);
lean_ctor_set(v___x_1898_, 0, v_ref_1932_);
v___x_1937_ = v___x_1898_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_ref_1932_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1939_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1937_);
v___x_1939_ = v___x_1930_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1945_; lean_object* v_snd_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_site_1901_);
v_fst_1945_ = lean_ctor_get(v_b_1883_, 0);
v_snd_1946_ = lean_ctor_get(v_b_1883_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_b_1883_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1948_ = v_b_1883_;
v_isShared_1949_ = v_isSharedCheck_2016_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snd_1946_);
lean_inc(v_fst_1945_);
lean_dec(v_b_1883_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_2016_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_val_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2015_; 
v_val_1950_ = lean_ctor_get(v_a_1903_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_a_1903_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1952_ = v_a_1903_;
v_isShared_1953_ = v_isSharedCheck_2015_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_val_1950_);
lean_dec(v_a_1903_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2015_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1900_);
lean_inc(v_sp_1879_);
v___x_1955_ = l_Lean_SearchPath_findWithExt(v_sp_1879_, v___x_1954_, v_fst_1900_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
if (lean_obj_tag(v_a_1956_) == 0)
{
lean_object* v___x_1957_; lean_object* v_name_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_val_1950_);
lean_dec(v_snd_1946_);
v___x_1957_ = l_Lean_linter_doc_deferred;
v_name_1958_ = lean_ctor_get(v___x_1957_, 0);
v___x_1959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_1900_);
v___x_1960_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1900_, v___x_1878_);
v___x_1961_ = lean_string_append(v___x_1959_, v___x_1960_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_1963_ = lean_string_append(v___x_1961_, v___x_1962_);
lean_inc(v_name_1958_);
v___x_1964_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1958_, v___x_1878_);
v___x_1965_ = lean_string_append(v___x_1963_, v___x_1964_);
lean_dec_ref(v___x_1964_);
v___x_1966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1967_ = lean_string_append(v___x_1965_, v___x_1966_);
v___x_1968_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1968_, 1);
lean_del_object(v___x_1952_);
lean_del_object(v___x_1898_);
v___x_1969_ = lean_box(v_unlocated_1892_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1969_);
v___x_1971_ = v___x_1948_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_fst_1945_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v_a_1888_ = v___x_1971_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1989_; 
lean_del_object(v___x_1948_);
lean_dec(v_fst_1945_);
lean_dec(v_sp_1879_);
v_a_1973_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1975_ = v___x_1968_;
v_isShared_1976_ = v_isSharedCheck_1989_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1989_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_ref_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v_ref_1977_ = lean_ctor_get(v___y_1884_, 5);
v___x_1978_ = lean_io_error_to_string(v_a_1973_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 3);
lean_ctor_set(v___x_1952_, 0, v___x_1978_);
v___x_1980_ = v___x_1952_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
lean_inc(v_ref_1977_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___x_1981_);
lean_ctor_set(v___x_1898_, 0, v_ref_1977_);
v___x_1983_ = v___x_1898_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_ref_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1983_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1991_; lean_object* v_name_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_del_object(v___x_1952_);
lean_del_object(v___x_1898_);
v_val_1990_ = lean_ctor_get(v_a_1956_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v_a_1956_, 1);
v___x_1991_ = l_Lean_linter_doc_deferred;
v_name_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_name_1992_);
v___x_1993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1993_, 0, v_val_1990_);
lean_ctor_set(v___x_1993_, 1, v_val_1950_);
lean_ctor_set(v___x_1993_, 2, v_name_1992_);
v___x_1994_ = lean_array_push(v_fst_1945_, v___x_1993_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1994_);
v___x_1996_ = v___x_1948_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_snd_1946_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v_a_1888_ = v___x_1996_;
goto v___jp_1887_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_val_1950_);
lean_del_object(v___x_1948_);
lean_dec(v_snd_1946_);
lean_dec(v_fst_1945_);
lean_dec(v_sp_1879_);
v_a_1998_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2000_ = v___x_1955_;
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1955_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2014_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_ref_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v_ref_2002_ = lean_ctor_get(v___y_1884_, 5);
v___x_2003_ = lean_io_error_to_string(v_a_1998_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 3);
lean_ctor_set(v___x_1952_, 0, v___x_2003_);
v___x_2005_ = v___x_1952_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = l_Lean_MessageData_ofFormat(v___x_2005_);
lean_inc(v_ref_2002_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___x_2006_);
lean_ctor_set(v___x_1898_, 0, v_ref_2002_);
v___x_2008_ = v___x_1898_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_ref_2002_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2008_);
v___x_2010_ = v___x_2000_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
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
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_site_1901_);
lean_del_object(v___x_1898_);
lean_dec_ref(v_b_1883_);
lean_dec(v_sp_1879_);
v_a_2017_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1902_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1902_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
v___jp_1887_:
{
size_t v___x_1889_; size_t v___x_1890_; 
v___x_1889_ = ((size_t)1ULL);
v___x_1890_ = lean_usize_add(v_i_1882_, v___x_1889_);
v_i_1882_ = v___x_1890_;
v_b_1883_ = v_a_1888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2027_, lean_object* v_sp_2028_, lean_object* v_as_2029_, lean_object* v_sz_2030_, lean_object* v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v___x_8996__boxed_2036_; size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v___x_8996__boxed_2036_ = lean_unbox(v___x_2027_);
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2030_);
lean_dec(v_sz_2030_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2031_);
lean_dec(v_i_2031_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_8996__boxed_2036_, v_sp_2028_, v_as_2029_, v_sz_boxed_2037_, v_i_boxed_2038_, v_b_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_as_2029_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_2046_, uint8_t v___y_2047_, lean_object* v_as_2048_, size_t v_sz_2049_, size_t v_i_2050_, lean_object* v_b_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_a_2055_; uint8_t v___x_2059_; 
v___x_2059_ = lean_usize_dec_lt(v_i_2050_, v_sz_2049_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec(v_sp_2046_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_b_2051_);
return v___x_2060_;
}
else
{
lean_object* v_a_2061_; lean_object* v_snd_2062_; lean_object* v_fst_2063_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2160_; 
v_a_2061_ = lean_array_uget_borrowed(v_as_2048_, v_i_2050_);
v_snd_2062_ = lean_ctor_get(v_a_2061_, 1);
lean_inc(v_snd_2062_);
v_fst_2063_ = lean_ctor_get(v_snd_2062_, 0);
lean_inc(v_fst_2063_);
v_fst_2064_ = lean_ctor_get(v_a_2061_, 0);
v_snd_2065_ = lean_ctor_get(v_snd_2062_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_snd_2062_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_snd_2062_, 0);
lean_dec(v_unused_2161_);
v___x_2067_ = v_snd_2062_;
v_isShared_2068_ = v_isSharedCheck_2160_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snd_2065_);
lean_dec(v_snd_2062_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2160_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_site_2069_; lean_object* v_sourceString_2070_; lean_object* v___x_2071_; lean_object* v___y_2073_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v_site_2069_ = lean_ctor_get(v_fst_2063_, 0);
lean_inc_ref(v_site_2069_);
v_sourceString_2070_ = lean_ctor_get(v_fst_2063_, 2);
lean_inc_ref(v_sourceString_2070_);
lean_dec(v_fst_2063_);
v___x_2071_ = lean_box(0);
v___x_2152_ = lean_string_utf8_byte_size(v_sourceString_2070_);
v___x_2153_ = lean_unsigned_to_nat(0u);
v___x_2154_ = lean_nat_dec_eq(v___x_2152_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2156_ = lean_string_append(v___x_2155_, v_sourceString_2070_);
lean_dec_ref(v_sourceString_2070_);
v___x_2157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
v___y_2073_ = v___x_2158_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2159_; 
lean_dec_ref(v_sourceString_2070_);
v___x_2159_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2073_ = v___x_2159_;
goto v___jp_2072_;
}
v___jp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2064_);
lean_inc(v_sp_2046_);
v___x_2075_ = l_Lean_SearchPath_findWithExt(v_sp_2046_, v___x_2074_, v_fst_2064_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
if (lean_obj_tag(v_a_2076_) == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2077_ = l_Lean_MessageData_toString(v_snd_2065_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2064_);
v___x_2079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2064_, v___y_2047_);
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
v___x_2083_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2069_);
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = lean_string_append(v___x_2084_, v___y_2073_);
lean_dec_ref(v___y_2073_);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
v___x_2088_ = lean_string_append(v___x_2087_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2089_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2088_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_dec_ref_known(v___x_2089_, 1);
lean_del_object(v___x_2067_);
v_a_2055_ = v___x_2071_;
goto v___jp_2054_;
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_sp_2046_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_ref_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_ref_2094_ = lean_ctor_get(v___y_2052_, 5);
v___x_2095_ = lean_io_error_to_string(v_a_2090_);
v___x_2096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = l_Lean_MessageData_ofFormat(v___x_2096_);
lean_inc(v_ref_2094_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2097_);
lean_ctor_set(v___x_2067_, 0, v_ref_2094_);
v___x_2099_ = v___x_2067_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_ref_2094_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2099_);
v___x_2101_ = v___x_2092_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v_val_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2136_; 
v_val_2105_ = lean_ctor_get(v_a_2076_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_a_2076_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2107_ = v_a_2076_;
v_isShared_2108_ = v_isSharedCheck_2136_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_val_2105_);
lean_dec(v_a_2076_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2136_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2109_ = l_Lean_MessageData_toString(v_snd_2065_);
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2111_ = lean_string_append(v_val_2105_, v___x_2110_);
v___x_2112_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2069_);
v___x_2113_ = lean_string_append(v___x_2111_, v___x_2112_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = lean_string_append(v___x_2113_, v___y_2073_);
lean_dec_ref(v___y_2073_);
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
v___x_2117_ = lean_string_append(v___x_2116_, v___x_2109_);
lean_dec_ref(v___x_2109_);
v___x_2118_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
lean_del_object(v___x_2107_);
lean_del_object(v___x_2067_);
v_a_2055_ = v___x_2071_;
goto v___jp_2054_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_sp_2046_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2135_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2135_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_ref_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v_ref_2123_ = lean_ctor_get(v___y_2052_, 5);
v___x_2124_ = lean_io_error_to_string(v_a_2119_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 3);
lean_ctor_set(v___x_2107_, 0, v___x_2124_);
v___x_2126_ = v___x_2107_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Lean_MessageData_ofFormat(v___x_2126_);
lean_inc(v_ref_2123_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2127_);
lean_ctor_set(v___x_2067_, 0, v_ref_2123_);
v___x_2129_ = v___x_2067_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_ref_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2129_);
v___x_2131_ = v___x_2121_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
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
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_site_2069_);
lean_dec(v_snd_2065_);
lean_dec(v_sp_2046_);
v_a_2137_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2139_ = v___x_2075_;
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2075_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_ref_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v_ref_2141_ = lean_ctor_get(v___y_2052_, 5);
v___x_2142_ = lean_io_error_to_string(v_a_2137_);
v___x_2143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = l_Lean_MessageData_ofFormat(v___x_2143_);
lean_inc(v_ref_2141_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2144_);
lean_ctor_set(v___x_2067_, 0, v_ref_2141_);
v___x_2146_ = v___x_2067_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_ref_2141_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2146_);
v___x_2148_ = v___x_2139_;
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
v___jp_2054_:
{
size_t v___x_2056_; size_t v___x_2057_; 
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2050_, v___x_2056_);
v_i_2050_ = v___x_2057_;
v_b_2051_ = v_a_2055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2162_, lean_object* v___y_2163_, lean_object* v_as_2164_, lean_object* v_sz_2165_, lean_object* v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v___y_9288__boxed_2170_; size_t v_sz_boxed_2171_; size_t v_i_boxed_2172_; lean_object* v_res_2173_; 
v___y_9288__boxed_2170_ = lean_unbox(v___y_2163_);
v_sz_boxed_2171_ = lean_unbox_usize(v_sz_2165_);
lean_dec(v_sz_2165_);
v_i_boxed_2172_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2162_, v___y_9288__boxed_2170_, v_as_2164_, v_sz_boxed_2171_, v_i_boxed_2172_, v_b_2167_, v___y_2168_);
lean_dec_ref(v___y_2168_);
lean_dec_ref(v_as_2164_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2174_, lean_object* v_as_2175_, size_t v_sz_2176_, size_t v_i_2177_, lean_object* v_b_2178_){
_start:
{
lean_object* v_a_2181_; uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2177_, v_sz_2176_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_b_2178_);
return v___x_2186_;
}
else
{
lean_object* v_a_2187_; uint8_t v___x_2188_; 
v_a_2187_ = lean_array_uget_borrowed(v_as_2175_, v_i_2177_);
v___x_2188_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2174_, v_a_2187_);
if (v___x_2188_ == 0)
{
v_a_2181_ = v_b_2178_;
goto v___jp_2180_;
}
else
{
lean_object* v___x_2189_; 
lean_inc(v_a_2187_);
v___x_2189_ = l_Lean_NameSet_insert(v_b_2178_, v_a_2187_);
v_a_2181_ = v___x_2189_;
goto v___jp_2180_;
}
}
v___jp_2180_:
{
size_t v___x_2182_; size_t v___x_2183_; 
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2177_, v___x_2182_);
v_i_2177_ = v___x_2183_;
v_b_2178_ = v_a_2181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2190_, lean_object* v_as_2191_, lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2190_, v_as_2191_, v_sz_boxed_2196_, v_i_boxed_2197_, v_b_2194_);
lean_dec_ref(v_as_2191_);
lean_dec(v_pkgRoot_2190_);
return v_res_2198_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(32u);
v___x_2206_ = lean_mk_empty_array_with_capacity(v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2208_ = ((size_t)5ULL);
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = lean_unsigned_to_nat(32u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2212_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2213_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2209_);
lean_ctor_set(v___x_2213_, 3, v___x_2209_);
lean_ctor_set_usize(v___x_2213_, 4, v___x_2208_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = l_Lean_NameSet_empty;
v___x_2220_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
lean_ctor_set(v___x_2221_, 2, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = l_Lean_firstFrontendMacroScope;
v___x_2224_ = lean_nat_add(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2235_; uint64_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2236_ = 0ULL;
v___x_2237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set_uint64(v___x_2237_, sizeof(void*)*1, v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v_unlocated_2240_; lean_object* v___x_2241_; 
v___x_2238_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2239_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2240_ = 1;
v___x_2241_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2239_);
lean_ctor_set(v___x_2241_, 2, v___x_2238_);
lean_ctor_set_uint8(v___x_2241_, sizeof(void*)*3, v_unlocated_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = l_Lean_Options_empty;
v___x_2245_ = l_Lean_Core_getMaxHeartbeats(v___x_2244_);
return v___x_2245_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2246_ = l_Lean_diagnostics;
v___x_2247_ = l_Lean_Options_empty;
v___x_2248_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2247_, v___x_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2249_, lean_object* v_linterOpts_2250_, lean_object* v_sp_2251_, lean_object* v_env_2252_, lean_object* v_pkgRoot_2253_, lean_object* v_docCheckedModules_2254_){
_start:
{
lean_object* v___y_2257_; lean_object* v_a_2258_; lean_object* v___y_2283_; uint8_t v___y_2284_; lean_object* v_a_2287_; uint8_t v___y_2291_; lean_object* v_a_2292_; lean_object* v___y_2309_; uint8_t v_lintOnly_2312_; uint8_t v_mode_2313_; lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___y_2317_; lean_object* v___y_2318_; uint8_t v___y_2319_; uint8_t v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v_fileName_2324_; lean_object* v_fileMap_2325_; lean_object* v_currRecDepth_2326_; lean_object* v_ref_2327_; lean_object* v_currNamespace_2328_; lean_object* v_openDecls_2329_; lean_object* v_initHeartbeats_2330_; lean_object* v_maxHeartbeats_2331_; lean_object* v_quotContext_2332_; lean_object* v_currMacroScope_2333_; lean_object* v_cancelTk_x3f_2334_; uint8_t v_suppressElabErrors_2335_; lean_object* v_inheritedTraceOptions_2336_; lean_object* v___y_2337_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2389_; uint8_t v___y_2390_; lean_object* v___y_2391_; uint8_t v___y_2392_; uint8_t v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; uint8_t v___y_2397_; uint8_t v___y_2418_; 
v_lintOnly_2312_ = lean_ctor_get_uint8(v_args_2249_, sizeof(void*)*3);
v_mode_2313_ = lean_ctor_get_uint8(v_args_2249_, sizeof(void*)*3 + 1);
v___f_2314_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
lean_inc(v_docCheckedModules_2254_);
lean_inc(v_pkgRoot_2253_);
v___f_2315_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2315_, 0, v_pkgRoot_2253_);
lean_closure_set(v___f_2315_, 1, v_docCheckedModules_2254_);
if (v_lintOnly_2312_ == 0)
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = l_Lean_linter_doc_deferred;
v___x_2455_ = l_Lean_Linter_getLinterValue(v___x_2454_, v_linterOpts_2250_);
v___y_2418_ = v___x_2455_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2456_; lean_object* v_name_2457_; uint8_t v___x_2458_; 
v___x_2456_ = l_Lean_linter_doc_deferred;
v_name_2457_ = lean_ctor_get(v___x_2456_, 0);
v___x_2458_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2457_, v_linterOpts_2250_);
v___y_2418_ = v___x_2458_;
goto v___jp_2417_;
}
v___jp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; size_t v_sz_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2259_ = lean_st_ref_get(v___y_2257_);
lean_dec(v___y_2257_);
lean_dec(v___x_2259_);
v___x_2260_ = l_Lean_Environment_header(v_env_2252_);
lean_dec_ref(v_env_2252_);
v___x_2261_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2260_);
v_sz_2262_ = lean_array_size(v___x_2261_);
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2253_, v___x_2261_, v_sz_2262_, v___x_2263_, v_docCheckedModules_2254_);
lean_dec_ref(v___x_2261_);
lean_dec(v_pkgRoot_2253_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2258_);
lean_ctor_set(v___x_2269_, 1, v_a_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_a_2258_);
v_a_2274_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2264_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2264_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
v___jp_2282_:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2285_, 0, v___y_2284_);
v___y_2257_ = v___y_2283_;
v_a_2258_ = v___x_2285_;
goto v___jp_2256_;
}
v___jp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_mk_io_user_error(v_a_2287_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
v___jp_2290_:
{
if (lean_obj_tag(v_a_2292_) == 0)
{
lean_object* v_msg_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_msg_2293_ = lean_ctor_get(v_a_2292_, 1);
lean_inc_ref(v_msg_2293_);
lean_dec_ref_known(v_a_2292_, 2);
v___x_2294_ = l_Lean_MessageData_toString(v_msg_2293_);
v___x_2295_ = lean_mk_io_user_error(v___x_2294_);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
else
{
lean_object* v_id_2297_; lean_object* v___x_2298_; 
v_id_2297_ = lean_ctor_get(v_a_2292_, 0);
lean_inc(v_id_2297_);
lean_dec_ref_known(v_a_2292_, 2);
v___x_2298_ = l_Lean_InternalExceptionId_getName(v_id_2297_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec(v_id_2297_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2301_ = l_Lean_Name_toString(v_a_2299_, v___y_2291_);
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2301_);
v_a_2287_ = v___x_2302_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2298_, 1);
v___x_2303_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2304_ = l_Nat_reprFast(v_id_2297_);
v___x_2305_ = lean_string_append(v___x_2303_, v___x_2304_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
v_a_2287_ = v___x_2307_;
goto v___jp_2286_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___y_2309_);
lean_ctor_set(v___x_2310_, 1, v_docCheckedModules_2254_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
v___jp_2316_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = l_Lean_maxRecDepth;
v___x_2339_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2318_, v___x_2338_);
lean_inc_ref(v___y_2318_);
v___x_2340_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2340_, 0, v_fileName_2324_);
lean_ctor_set(v___x_2340_, 1, v_fileMap_2325_);
lean_ctor_set(v___x_2340_, 2, v___y_2318_);
lean_ctor_set(v___x_2340_, 3, v_currRecDepth_2326_);
lean_ctor_set(v___x_2340_, 4, v___x_2339_);
lean_ctor_set(v___x_2340_, 5, v_ref_2327_);
lean_ctor_set(v___x_2340_, 6, v_currNamespace_2328_);
lean_ctor_set(v___x_2340_, 7, v_openDecls_2329_);
lean_ctor_set(v___x_2340_, 8, v_initHeartbeats_2330_);
lean_ctor_set(v___x_2340_, 9, v_maxHeartbeats_2331_);
lean_ctor_set(v___x_2340_, 10, v_quotContext_2332_);
lean_ctor_set(v___x_2340_, 11, v_currMacroScope_2333_);
lean_ctor_set(v___x_2340_, 12, v_cancelTk_x3f_2334_);
lean_ctor_set(v___x_2340_, 13, v_inheritedTraceOptions_2336_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*14, v___y_2320_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*14 + 1, v_suppressElabErrors_2335_);
lean_inc_ref(v___y_2317_);
v___x_2341_ = l_Lean_Doc_DeferredCheck_run(v___f_2315_, v___y_2317_, v___x_2340_, v___y_2337_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; uint8_t v___x_2343_; uint8_t v___x_2344_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = 1;
v___x_2344_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2313_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; size_t v_sz_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v___y_2337_);
v___x_2345_ = lean_box(0);
v_sz_2346_ = lean_array_size(v_a_2342_);
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2251_, v___y_2319_, v_a_2342_, v_sz_2346_, v___x_2347_, v___x_2345_, v___x_2340_);
lean_dec_ref_known(v___x_2340_, 14);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
lean_dec_ref_known(v___x_2348_, 1);
v___x_2349_ = lean_array_get_size(v_a_2342_);
lean_dec(v_a_2342_);
v___x_2350_ = lean_nat_dec_eq(v___x_2349_, v___y_2322_);
lean_dec(v___y_2322_);
if (v___x_2350_ == 0)
{
v___y_2283_ = v___y_2323_;
v___y_2284_ = v___y_2319_;
goto v___jp_2282_;
}
else
{
v___y_2283_ = v___y_2323_;
v___y_2284_ = v___x_2344_;
goto v___jp_2282_;
}
}
else
{
lean_object* v_a_2351_; 
lean_dec(v_a_2342_);
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec(v_docCheckedModules_2254_);
lean_dec(v_pkgRoot_2253_);
lean_dec_ref(v_env_2252_);
v_a_2351_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2348_, 1);
v___y_2291_ = v___y_2319_;
v_a_2292_ = v_a_2351_;
goto v___jp_2290_;
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; size_t v_sz_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2352_ = lean_mk_empty_array_with_capacity(v___y_2322_);
lean_dec(v___y_2322_);
v___x_2353_ = lean_box(v___y_2321_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v_sz_2355_ = lean_array_size(v_a_2342_);
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2344_, v_sp_2251_, v_a_2342_, v_sz_2355_, v___x_2356_, v___x_2354_, v___x_2340_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref_known(v___x_2340_, 14);
lean_dec(v_a_2342_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_fst_2359_; lean_object* v_snd_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v_fst_2359_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_fst_2359_);
v_snd_2360_ = lean_ctor_get(v_a_2358_, 1);
lean_inc(v_snd_2360_);
lean_dec(v_a_2358_);
v___x_2361_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2361_, 0, v_fst_2359_);
v___x_2362_ = lean_unbox(v_snd_2360_);
lean_dec(v_snd_2360_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v___x_2362_);
v___y_2257_ = v___y_2323_;
v_a_2258_ = v___x_2361_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2363_; 
lean_dec(v___y_2323_);
lean_dec(v_docCheckedModules_2254_);
lean_dec(v_pkgRoot_2253_);
lean_dec_ref(v_env_2252_);
v_a_2363_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2357_, 1);
v___y_2291_ = v___y_2319_;
v_a_2292_ = v_a_2363_;
goto v___jp_2290_;
}
}
}
else
{
lean_object* v_a_2364_; 
lean_dec_ref_known(v___x_2340_, 14);
lean_dec(v___y_2337_);
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec(v_docCheckedModules_2254_);
lean_dec(v_pkgRoot_2253_);
lean_dec_ref(v_env_2252_);
lean_dec(v_sp_2251_);
v_a_2364_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2341_, 1);
v___y_2291_ = v___y_2319_;
v_a_2292_ = v_a_2364_;
goto v___jp_2290_;
}
}
v___jp_2365_:
{
lean_object* v_fileName_2375_; lean_object* v_fileMap_2376_; lean_object* v_currRecDepth_2377_; lean_object* v_ref_2378_; lean_object* v_currNamespace_2379_; lean_object* v_openDecls_2380_; lean_object* v_initHeartbeats_2381_; lean_object* v_maxHeartbeats_2382_; lean_object* v_quotContext_2383_; lean_object* v_currMacroScope_2384_; lean_object* v_cancelTk_x3f_2385_; uint8_t v_suppressElabErrors_2386_; lean_object* v_inheritedTraceOptions_2387_; 
v_fileName_2375_ = lean_ctor_get(v___y_2373_, 0);
lean_inc_ref(v_fileName_2375_);
v_fileMap_2376_ = lean_ctor_get(v___y_2373_, 1);
lean_inc_ref(v_fileMap_2376_);
v_currRecDepth_2377_ = lean_ctor_get(v___y_2373_, 3);
lean_inc(v_currRecDepth_2377_);
v_ref_2378_ = lean_ctor_get(v___y_2373_, 5);
lean_inc(v_ref_2378_);
v_currNamespace_2379_ = lean_ctor_get(v___y_2373_, 6);
lean_inc(v_currNamespace_2379_);
v_openDecls_2380_ = lean_ctor_get(v___y_2373_, 7);
lean_inc(v_openDecls_2380_);
v_initHeartbeats_2381_ = lean_ctor_get(v___y_2373_, 8);
lean_inc(v_initHeartbeats_2381_);
v_maxHeartbeats_2382_ = lean_ctor_get(v___y_2373_, 9);
lean_inc(v_maxHeartbeats_2382_);
v_quotContext_2383_ = lean_ctor_get(v___y_2373_, 10);
lean_inc(v_quotContext_2383_);
v_currMacroScope_2384_ = lean_ctor_get(v___y_2373_, 11);
lean_inc(v_currMacroScope_2384_);
v_cancelTk_x3f_2385_ = lean_ctor_get(v___y_2373_, 12);
lean_inc(v_cancelTk_x3f_2385_);
v_suppressElabErrors_2386_ = lean_ctor_get_uint8(v___y_2373_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2387_ = lean_ctor_get(v___y_2373_, 13);
lean_inc_ref(v_inheritedTraceOptions_2387_);
lean_dec_ref(v___y_2373_);
v___y_2317_ = v___y_2366_;
v___y_2318_ = v___y_2367_;
v___y_2319_ = v___y_2368_;
v___y_2320_ = v___y_2369_;
v___y_2321_ = v___y_2370_;
v___y_2322_ = v___y_2371_;
v___y_2323_ = v___y_2372_;
v_fileName_2324_ = v_fileName_2375_;
v_fileMap_2325_ = v_fileMap_2376_;
v_currRecDepth_2326_ = v_currRecDepth_2377_;
v_ref_2327_ = v_ref_2378_;
v_currNamespace_2328_ = v_currNamespace_2379_;
v_openDecls_2329_ = v_openDecls_2380_;
v_initHeartbeats_2330_ = v_initHeartbeats_2381_;
v_maxHeartbeats_2331_ = v_maxHeartbeats_2382_;
v_quotContext_2332_ = v_quotContext_2383_;
v_currMacroScope_2333_ = v_currMacroScope_2384_;
v_cancelTk_x3f_2334_ = v_cancelTk_x3f_2385_;
v_suppressElabErrors_2335_ = v_suppressElabErrors_2386_;
v_inheritedTraceOptions_2336_ = v_inheritedTraceOptions_2387_;
v___y_2337_ = v___y_2374_;
goto v___jp_2316_;
}
v___jp_2388_:
{
if (v___y_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v_nextMacroScope_2400_; lean_object* v_ngen_2401_; lean_object* v_auxDeclNGen_2402_; lean_object* v_traceState_2403_; lean_object* v_messages_2404_; lean_object* v_infoState_2405_; lean_object* v_snapshotTasks_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2415_; 
v___x_2398_ = lean_st_ref_take(v___y_2396_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
v_nextMacroScope_2400_ = lean_ctor_get(v___x_2398_, 1);
v_ngen_2401_ = lean_ctor_get(v___x_2398_, 2);
v_auxDeclNGen_2402_ = lean_ctor_get(v___x_2398_, 3);
v_traceState_2403_ = lean_ctor_get(v___x_2398_, 4);
v_messages_2404_ = lean_ctor_get(v___x_2398_, 6);
v_infoState_2405_ = lean_ctor_get(v___x_2398_, 7);
v_snapshotTasks_2406_ = lean_ctor_get(v___x_2398_, 8);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v___x_2398_, 5);
lean_dec(v_unused_2416_);
v___x_2408_ = v___x_2398_;
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_snapshotTasks_2406_);
lean_inc(v_infoState_2405_);
lean_inc(v_messages_2404_);
lean_inc(v_traceState_2403_);
lean_inc(v_auxDeclNGen_2402_);
lean_inc(v_ngen_2401_);
lean_inc(v_nextMacroScope_2400_);
lean_inc(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Lean_Kernel_enableDiag(v_env_2399_, v___y_2392_);
lean_inc_ref(v___y_2391_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 5, v___y_2391_);
lean_ctor_set(v___x_2408_, 0, v___x_2410_);
v___x_2412_ = v___x_2408_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_nextMacroScope_2400_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_ngen_2401_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_auxDeclNGen_2402_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_traceState_2403_);
lean_ctor_set(v_reuseFailAlloc_2414_, 5, v___y_2391_);
lean_ctor_set(v_reuseFailAlloc_2414_, 6, v_messages_2404_);
lean_ctor_set(v_reuseFailAlloc_2414_, 7, v_infoState_2405_);
lean_ctor_set(v_reuseFailAlloc_2414_, 8, v_snapshotTasks_2406_);
v___x_2412_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_st_ref_set(v___y_2396_, v___x_2412_);
lean_inc(v___y_2396_);
v___y_2366_ = v___f_2314_;
v___y_2367_ = v___y_2389_;
v___y_2368_ = v___y_2390_;
v___y_2369_ = v___y_2392_;
v___y_2370_ = v___y_2393_;
v___y_2371_ = v___y_2394_;
v___y_2372_ = v___y_2396_;
v___y_2373_ = v___y_2395_;
v___y_2374_ = v___y_2396_;
goto v___jp_2365_;
}
}
}
else
{
lean_inc(v___y_2396_);
v___y_2366_ = v___f_2314_;
v___y_2367_ = v___y_2389_;
v___y_2368_ = v___y_2390_;
v___y_2369_ = v___y_2392_;
v___y_2370_ = v___y_2393_;
v___y_2371_ = v___y_2394_;
v___y_2372_ = v___y_2396_;
v___y_2373_ = v___y_2395_;
v___y_2374_ = v___y_2396_;
goto v___jp_2365_;
}
}
v___jp_2417_:
{
if (v___y_2418_ == 0)
{
uint8_t v___x_2419_; uint8_t v___x_2420_; 
lean_dec_ref(v___f_2315_);
lean_dec(v_pkgRoot_2253_);
lean_dec_ref(v_env_2252_);
lean_dec(v_sp_2251_);
v___x_2419_ = 1;
v___x_2420_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2313_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2421_, 0, v___y_2418_);
v___y_2309_ = v___x_2421_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2423_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___y_2418_);
v___y_2309_ = v___x_2423_;
goto v___jp_2308_;
}
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v_env_2451_; uint8_t v___x_2452_; uint8_t v___x_2453_; 
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2426_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2427_ = lean_io_get_num_heartbeats();
v___x_2428_ = l_Lean_firstFrontendMacroScope;
v___x_2429_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2430_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_box(0);
v___x_2433_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2434_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2435_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2436_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2252_);
v___x_2437_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2437_, 0, v_env_2252_);
lean_ctor_set(v___x_2437_, 1, v___x_2429_);
lean_ctor_set(v___x_2437_, 2, v___x_2430_);
lean_ctor_set(v___x_2437_, 3, v___x_2433_);
lean_ctor_set(v___x_2437_, 4, v___x_2434_);
lean_ctor_set(v___x_2437_, 5, v___x_2425_);
lean_ctor_set(v___x_2437_, 6, v___x_2426_);
lean_ctor_set(v___x_2437_, 7, v___x_2435_);
lean_ctor_set(v___x_2437_, 8, v___x_2436_);
v___x_2438_ = lean_st_mk_ref(v___x_2437_);
v___x_2439_ = l_Lean_inheritedTraceOptions;
v___x_2440_ = lean_st_ref_get(v___x_2439_);
v___x_2441_ = lean_st_ref_get(v___x_2438_);
v___x_2442_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2443_ = l_Lean_instInhabitedFileMap_default;
v___x_2444_ = l_Lean_Options_empty;
v___x_2445_ = lean_unsigned_to_nat(1000u);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2448_ = 0;
v___x_2449_ = lean_box(0);
lean_inc(v___x_2440_);
lean_inc(v___x_2427_);
v___x_2450_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2450_, 0, v___x_2442_);
lean_ctor_set(v___x_2450_, 1, v___x_2443_);
lean_ctor_set(v___x_2450_, 2, v___x_2444_);
lean_ctor_set(v___x_2450_, 3, v___x_2424_);
lean_ctor_set(v___x_2450_, 4, v___x_2445_);
lean_ctor_set(v___x_2450_, 5, v___x_2446_);
lean_ctor_set(v___x_2450_, 6, v___x_2431_);
lean_ctor_set(v___x_2450_, 7, v___x_2432_);
lean_ctor_set(v___x_2450_, 8, v___x_2427_);
lean_ctor_set(v___x_2450_, 9, v___x_2447_);
lean_ctor_set(v___x_2450_, 10, v___x_2431_);
lean_ctor_set(v___x_2450_, 11, v___x_2428_);
lean_ctor_set(v___x_2450_, 12, v___x_2449_);
lean_ctor_set(v___x_2450_, 13, v___x_2440_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*14, v___x_2448_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*14 + 1, v___x_2448_);
v_env_2451_ = lean_ctor_get(v___x_2441_, 0);
lean_inc_ref(v_env_2451_);
lean_dec(v___x_2441_);
v___x_2452_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2453_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2451_);
lean_dec_ref(v_env_2451_);
if (v___x_2453_ == 0)
{
if (v___x_2452_ == 0)
{
lean_dec_ref_known(v___x_2450_, 14);
lean_inc(v___x_2438_);
v___y_2317_ = v___f_2314_;
v___y_2318_ = v___x_2444_;
v___y_2319_ = v___y_2418_;
v___y_2320_ = v___x_2452_;
v___y_2321_ = v___x_2448_;
v___y_2322_ = v___x_2424_;
v___y_2323_ = v___x_2438_;
v_fileName_2324_ = v___x_2442_;
v_fileMap_2325_ = v___x_2443_;
v_currRecDepth_2326_ = v___x_2424_;
v_ref_2327_ = v___x_2446_;
v_currNamespace_2328_ = v___x_2431_;
v_openDecls_2329_ = v___x_2432_;
v_initHeartbeats_2330_ = v___x_2427_;
v_maxHeartbeats_2331_ = v___x_2447_;
v_quotContext_2332_ = v___x_2431_;
v_currMacroScope_2333_ = v___x_2428_;
v_cancelTk_x3f_2334_ = v___x_2449_;
v_suppressElabErrors_2335_ = v___x_2448_;
v_inheritedTraceOptions_2336_ = v___x_2440_;
v___y_2337_ = v___x_2438_;
goto v___jp_2316_;
}
else
{
lean_dec(v___x_2440_);
lean_dec(v___x_2427_);
v___y_2389_ = v___x_2444_;
v___y_2390_ = v___y_2418_;
v___y_2391_ = v___x_2425_;
v___y_2392_ = v___x_2452_;
v___y_2393_ = v___x_2448_;
v___y_2394_ = v___x_2424_;
v___y_2395_ = v___x_2450_;
v___y_2396_ = v___x_2438_;
v___y_2397_ = v___x_2453_;
goto v___jp_2388_;
}
}
else
{
lean_dec(v___x_2440_);
lean_dec(v___x_2427_);
v___y_2389_ = v___x_2444_;
v___y_2390_ = v___y_2418_;
v___y_2391_ = v___x_2425_;
v___y_2392_ = v___x_2452_;
v___y_2393_ = v___x_2448_;
v___y_2394_ = v___x_2424_;
v___y_2395_ = v___x_2450_;
v___y_2396_ = v___x_2438_;
v___y_2397_ = v___x_2452_;
goto v___jp_2388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2459_, lean_object* v_linterOpts_2460_, lean_object* v_sp_2461_, lean_object* v_env_2462_, lean_object* v_pkgRoot_2463_, lean_object* v_docCheckedModules_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2459_, v_linterOpts_2460_, v_sp_2461_, v_env_2462_, v_pkgRoot_2463_, v_docCheckedModules_2464_);
lean_dec_ref(v_linterOpts_2460_);
lean_dec_ref(v_args_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2467_, uint8_t v___y_2468_, lean_object* v_as_2469_, size_t v_sz_2470_, size_t v_i_2471_, lean_object* v_b_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2467_, v___y_2468_, v_as_2469_, v_sz_2470_, v_i_2471_, v_b_2472_, v___y_2473_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2477_, lean_object* v___y_2478_, lean_object* v_as_2479_, lean_object* v_sz_2480_, lean_object* v_i_2481_, lean_object* v_b_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___y_10013__boxed_2486_; size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v___y_10013__boxed_2486_ = lean_unbox(v___y_2478_);
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2477_, v___y_10013__boxed_2486_, v_as_2479_, v_sz_boxed_2487_, v_i_boxed_2488_, v_b_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_as_2479_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_linterOpts_2490_, lean_object* v_as_2491_, size_t v_i_2492_, size_t v_stop_2493_, lean_object* v_b_2494_){
_start:
{
lean_object* v___y_2496_; uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_eq(v_i_2492_, v_stop_2493_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v_linter_2502_; uint8_t v___x_2503_; 
v___x_2501_ = lean_array_uget_borrowed(v_as_2491_, v_i_2492_);
v_linter_2502_ = lean_ctor_get(v___x_2501_, 0);
v___x_2503_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2502_, v_linterOpts_2490_);
if (v___x_2503_ == 0)
{
v___y_2496_ = v_b_2494_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2504_; 
lean_inc(v___x_2501_);
v___x_2504_ = lean_array_push(v_b_2494_, v___x_2501_);
v___y_2496_ = v___x_2504_;
goto v___jp_2495_;
}
}
else
{
return v_b_2494_;
}
v___jp_2495_:
{
size_t v___x_2497_; size_t v___x_2498_; 
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_add(v_i_2492_, v___x_2497_);
v_i_2492_ = v___x_2498_;
v_b_2494_ = v___y_2496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_linterOpts_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_stop_2508_, lean_object* v_b_2509_){
_start:
{
size_t v_i_boxed_2510_; size_t v_stop_boxed_2511_; lean_object* v_res_2512_; 
v_i_boxed_2510_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_stop_boxed_2511_ = lean_unbox_usize(v_stop_2508_);
lean_dec(v_stop_2508_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2505_, v_as_2506_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2509_);
lean_dec_ref(v_as_2506_);
lean_dec_ref(v_linterOpts_2505_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2515_, lean_object* v_as_2516_, size_t v_i_2517_, size_t v_stop_2518_, lean_object* v_b_2519_){
_start:
{
lean_object* v___y_2521_; uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_eq(v_i_2517_, v_stop_2518_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2552_; 
v___x_2526_ = lean_array_uget(v_as_2516_, v_i_2517_);
v_fst_2527_ = lean_ctor_get(v___x_2526_, 0);
v_snd_2528_ = lean_ctor_get(v___x_2526_, 1);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2530_ = v___x_2526_;
v_isShared_2531_ = v_isSharedCheck_2552_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_snd_2528_);
lean_inc(v_fst_2527_);
lean_dec(v___x_2526_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2552_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___y_2533_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_array_get_size(v_snd_2528_);
v___x_2543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2544_ = lean_nat_dec_lt(v___x_2541_, v___x_2542_);
if (v___x_2544_ == 0)
{
lean_dec(v_snd_2528_);
v___y_2533_ = v___x_2543_;
goto v___jp_2532_;
}
else
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_nat_dec_le(v___x_2542_, v___x_2542_);
if (v___x_2545_ == 0)
{
if (v___x_2544_ == 0)
{
lean_dec(v_snd_2528_);
v___y_2533_ = v___x_2543_;
goto v___jp_2532_;
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_of_nat(v___x_2542_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2515_, v_snd_2528_, v___x_2546_, v___x_2547_, v___x_2543_);
lean_dec(v_snd_2528_);
v___y_2533_ = v___x_2548_;
goto v___jp_2532_;
}
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2542_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_linterOpts_2515_, v_snd_2528_, v___x_2549_, v___x_2550_, v___x_2543_);
lean_dec(v_snd_2528_);
v___y_2533_ = v___x_2551_;
goto v___jp_2532_;
}
}
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_array_get_size(v___y_2533_);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = lean_nat_dec_eq(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2538_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___y_2533_);
v___x_2538_ = v___x_2530_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_fst_2527_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___y_2533_);
v___x_2538_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_array_push(v_b_2519_, v___x_2538_);
v___y_2521_ = v___x_2539_;
goto v___jp_2520_;
}
}
else
{
lean_dec_ref(v___y_2533_);
lean_del_object(v___x_2530_);
lean_dec(v_fst_2527_);
v___y_2521_ = v_b_2519_;
goto v___jp_2520_;
}
}
}
}
else
{
return v_b_2519_;
}
v___jp_2520_:
{
size_t v___x_2522_; size_t v___x_2523_; 
v___x_2522_ = ((size_t)1ULL);
v___x_2523_ = lean_usize_add(v_i_2517_, v___x_2522_);
v_i_2517_ = v___x_2523_;
v_b_2519_ = v___y_2521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2553_, lean_object* v_as_2554_, lean_object* v_i_2555_, lean_object* v_stop_2556_, lean_object* v_b_2557_){
_start:
{
size_t v_i_boxed_2558_; size_t v_stop_boxed_2559_; lean_object* v_res_2560_; 
v_i_boxed_2558_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_stop_boxed_2559_ = lean_unbox_usize(v_stop_2556_);
lean_dec(v_stop_2556_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2553_, v_as_2554_, v_i_boxed_2558_, v_stop_boxed_2559_, v_b_2557_);
lean_dec_ref(v_as_2554_);
lean_dec_ref(v_linterOpts_2553_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2561_, lean_object* v_as_2562_, lean_object* v_start_2563_, lean_object* v_stop_2564_){
_start:
{
lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2565_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2566_ = lean_nat_dec_lt(v_start_2563_, v_stop_2564_);
if (v___x_2566_ == 0)
{
return v___x_2565_;
}
else
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_array_get_size(v_as_2562_);
v___x_2568_ = lean_nat_dec_le(v_stop_2564_, v___x_2567_);
if (v___x_2568_ == 0)
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_nat_dec_lt(v_start_2563_, v___x_2567_);
if (v___x_2569_ == 0)
{
return v___x_2565_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_usize_of_nat(v_start_2563_);
v___x_2571_ = lean_usize_of_nat(v___x_2567_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2561_, v_as_2562_, v___x_2570_, v___x_2571_, v___x_2565_);
return v___x_2572_;
}
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_usize_of_nat(v_start_2563_);
v___x_2574_ = lean_usize_of_nat(v_stop_2564_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2561_, v_as_2562_, v___x_2573_, v___x_2574_, v___x_2565_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2576_, lean_object* v_as_2577_, lean_object* v_start_2578_, lean_object* v_stop_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2576_, v_as_2577_, v_start_2578_, v_stop_2579_);
lean_dec(v_stop_2579_);
lean_dec(v_start_2578_);
lean_dec_ref(v_as_2577_);
lean_dec_ref(v_linterOpts_2576_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2581_, lean_object* v_init_2582_, lean_object* v_x_2583_){
_start:
{
if (lean_obj_tag(v_x_2583_) == 0)
{
lean_object* v_k_2585_; lean_object* v_v_2586_; lean_object* v_l_2587_; lean_object* v_r_2588_; lean_object* v___x_2589_; lean_object* v_a_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2605_; 
v_k_2585_ = lean_ctor_get(v_x_2583_, 1);
lean_inc(v_k_2585_);
v_v_2586_ = lean_ctor_get(v_x_2583_, 2);
lean_inc(v_v_2586_);
v_l_2587_ = lean_ctor_get(v_x_2583_, 3);
lean_inc(v_l_2587_);
v_r_2588_ = lean_ctor_get(v_x_2583_, 4);
lean_inc(v_r_2588_);
lean_dec_ref_known(v_x_2583_, 5);
lean_inc(v_fst_2581_);
v___x_2589_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2581_, v_init_2582_, v_l_2587_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v_a_2591_ = lean_ctor_get(v_a_2590_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_a_2590_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2593_ = v_a_2590_;
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v_a_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v_anyUnlocated_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v_anyUnlocated_2595_ = 1;
v___x_2596_ = l_Lean_Name_toString(v_k_2585_, v_anyUnlocated_2595_);
lean_inc(v_fst_2581_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 0);
lean_ctor_set(v___x_2593_, 0, v_fst_2581_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_fst_2581_);
v___x_2598_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
double v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = lean_float_of_nat(v_v_2586_);
v___x_2600_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2600_, 0, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2596_);
lean_ctor_set(v___x_2601_, 1, v___x_2598_);
lean_ctor_set(v___x_2601_, 2, v___x_2600_);
v___x_2602_ = lean_array_push(v_a_2591_, v___x_2601_);
v_init_2582_ = v___x_2602_;
v_x_2583_ = v_r_2588_;
goto _start;
}
}
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_fst_2581_);
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_init_2582_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2608_, lean_object* v_init_2609_, lean_object* v_x_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2608_, v_init_2609_, v_x_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(lean_object* v_t_2613_, lean_object* v_k_2614_, lean_object* v_fallback_2615_){
_start:
{
if (lean_obj_tag(v_t_2613_) == 0)
{
lean_object* v_k_2616_; lean_object* v_v_2617_; lean_object* v_l_2618_; lean_object* v_r_2619_; uint8_t v___x_2620_; 
v_k_2616_ = lean_ctor_get(v_t_2613_, 1);
v_v_2617_ = lean_ctor_get(v_t_2613_, 2);
v_l_2618_ = lean_ctor_get(v_t_2613_, 3);
v_r_2619_ = lean_ctor_get(v_t_2613_, 4);
v___x_2620_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2614_, v_k_2616_);
switch(v___x_2620_)
{
case 0:
{
v_t_2613_ = v_l_2618_;
goto _start;
}
case 1:
{
lean_inc(v_v_2617_);
return v_v_2617_;
}
default: 
{
v_t_2613_ = v_r_2619_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2615_);
return v_fallback_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg___boxed(lean_object* v_t_2623_, lean_object* v_k_2624_, lean_object* v_fallback_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_t_2623_, v_k_2624_, v_fallback_2625_);
lean_dec(v_fallback_2625_);
lean_dec(v_k_2624_);
lean_dec(v_t_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2627_, size_t v_i_2628_, size_t v_stop_2629_, lean_object* v_b_2630_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_eq(v_i_2628_, v_stop_2629_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v_linter_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; size_t v___x_2639_; size_t v___x_2640_; 
v___x_2632_ = lean_array_uget_borrowed(v_as_2627_, v_i_2628_);
v_linter_2633_ = lean_ctor_get(v___x_2632_, 0);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_b_2630_, v_linter_2633_, v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(1u);
v___x_2637_ = lean_nat_add(v___x_2635_, v___x_2636_);
lean_dec(v___x_2635_);
lean_inc(v_linter_2633_);
v___x_2638_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2633_, v___x_2637_, v_b_2630_);
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2628_, v___x_2639_);
v_i_2628_ = v___x_2640_;
v_b_2630_ = v___x_2638_;
goto _start;
}
else
{
return v_b_2630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2642_, lean_object* v_i_2643_, lean_object* v_stop_2644_, lean_object* v_b_2645_){
_start:
{
size_t v_i_boxed_2646_; size_t v_stop_boxed_2647_; lean_object* v_res_2648_; 
v_i_boxed_2646_ = lean_unbox_usize(v_i_2643_);
lean_dec(v_i_2643_);
v_stop_boxed_2647_ = lean_unbox_usize(v_stop_2644_);
lean_dec(v_stop_2644_);
v_res_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2642_, v_i_boxed_2646_, v_stop_boxed_2647_, v_b_2645_);
lean_dec_ref(v_as_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2649_, size_t v_sz_2650_, size_t v_i_2651_, lean_object* v_b_2652_){
_start:
{
lean_object* v_a_2655_; uint8_t v___x_2659_; 
v___x_2659_ = lean_usize_dec_lt(v_i_2651_, v_sz_2650_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_b_2652_);
return v___x_2660_;
}
else
{
lean_object* v_a_2661_; lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___y_2665_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v_a_2661_ = lean_array_uget_borrowed(v_as_2649_, v_i_2651_);
v_fst_2662_ = lean_ctor_get(v_a_2661_, 0);
v_snd_2663_ = lean_ctor_get(v_a_2661_, 1);
v___x_2687_ = lean_box(1);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_array_get_size(v_snd_2663_);
v___x_2690_ = lean_nat_dec_lt(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
v___y_2665_ = v___x_2687_;
goto v___jp_2664_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_nat_dec_le(v___x_2689_, v___x_2689_);
if (v___x_2691_ == 0)
{
if (v___x_2690_ == 0)
{
v___y_2665_ = v___x_2687_;
goto v___jp_2664_;
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = lean_usize_of_nat(v___x_2689_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2663_, v___x_2692_, v___x_2693_, v___x_2687_);
v___y_2665_ = v___x_2694_;
goto v___jp_2664_;
}
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2689_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2663_, v___x_2695_, v___x_2696_, v___x_2687_);
v___y_2665_ = v___x_2697_;
goto v___jp_2664_;
}
}
v___jp_2664_:
{
lean_object* v___x_2666_; 
lean_inc(v_fst_2662_);
v___x_2666_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2662_, v_b_2652_, v___y_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v_a_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v_a_2668_ = lean_ctor_get(v_a_2667_, 0);
lean_inc(v_a_2668_);
lean_dec(v_a_2667_);
v_a_2655_ = v_a_2668_;
goto v___jp_2654_;
}
else
{
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2678_; 
v_a_2669_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2671_ = v___x_2666_;
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2666_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2678_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
if (lean_obj_tag(v_a_2669_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; 
v_a_2673_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v_a_2669_, 1);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
else
{
lean_object* v_a_2677_; 
lean_del_object(v___x_2671_);
v_a_2677_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v_a_2669_, 1);
v_a_2655_ = v_a_2677_;
goto v___jp_2654_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2666_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2666_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
v___jp_2654_:
{
size_t v___x_2656_; size_t v___x_2657_; 
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2651_, v___x_2656_);
v_i_2651_ = v___x_2657_;
v_b_2652_ = v_a_2655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2698_, lean_object* v_sz_2699_, lean_object* v_i_2700_, lean_object* v_b_2701_, lean_object* v___y_2702_){
_start:
{
size_t v_sz_boxed_2703_; size_t v_i_boxed_2704_; lean_object* v_res_2705_; 
v_sz_boxed_2703_ = lean_unbox_usize(v_sz_2699_);
lean_dec(v_sz_2699_);
v_i_boxed_2704_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_res_2705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2698_, v_sz_boxed_2703_, v_i_boxed_2704_, v_b_2701_);
lean_dec_ref(v_as_2698_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2709_, lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_){
_start:
{
lean_object* v_a_2716_; uint8_t v_anyUnlocated_2720_; 
v_anyUnlocated_2720_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v_anyUnlocated_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec(v_fst_2709_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_b_2713_);
return v___x_2721_;
}
else
{
lean_object* v_fst_2722_; lean_object* v_snd_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2760_; 
v_fst_2722_ = lean_ctor_get(v_b_2713_, 0);
v_snd_2723_ = lean_ctor_get(v_b_2713_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_b_2713_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2725_ = v_b_2713_;
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2723_);
lean_inc(v_fst_2722_);
lean_dec(v_b_2713_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_a_2727_; lean_object* v_position_x3f_2728_; 
v_a_2727_ = lean_array_uget_borrowed(v_as_2710_, v_i_2712_);
v_position_x3f_2728_ = lean_ctor_get(v_a_2727_, 2);
if (lean_obj_tag(v_position_x3f_2728_) == 0)
{
lean_object* v_linter_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec(v_snd_2723_);
v_linter_2729_ = lean_ctor_get(v_a_2727_, 0);
v___x_2730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2729_);
v___x_2731_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2729_, v_anyUnlocated_2720_);
v___x_2732_ = lean_string_append(v___x_2730_, v___x_2731_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2734_ = lean_string_append(v___x_2732_, v___x_2733_);
lean_inc(v_fst_2709_);
v___x_2735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2709_, v_anyUnlocated_2720_);
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
lean_dec_ref(v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2738_ = lean_string_append(v___x_2736_, v___x_2737_);
v___x_2739_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2738_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2739_, 1);
v___x_2740_ = lean_box(v_anyUnlocated_2720_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2740_);
v___x_2742_ = v___x_2725_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_fst_2722_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v_a_2716_ = v___x_2742_;
goto v___jp_2715_;
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_del_object(v___x_2725_);
lean_dec(v_fst_2722_);
lean_dec(v_fst_2709_);
v_a_2744_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2739_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2739_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_linter_2752_; lean_object* v_file_2753_; lean_object* v_val_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v_linter_2752_ = lean_ctor_get(v_a_2727_, 0);
v_file_2753_ = lean_ctor_get(v_a_2727_, 3);
v_val_2754_ = lean_ctor_get(v_position_x3f_2728_, 0);
lean_inc(v_linter_2752_);
lean_inc(v_val_2754_);
lean_inc_ref(v_file_2753_);
v___x_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2755_, 0, v_file_2753_);
lean_ctor_set(v___x_2755_, 1, v_val_2754_);
lean_ctor_set(v___x_2755_, 2, v_linter_2752_);
v___x_2756_ = lean_array_push(v_fst_2722_, v___x_2755_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2756_);
v___x_2758_ = v___x_2725_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_snd_2723_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
v_a_2716_ = v___x_2758_;
goto v___jp_2715_;
}
}
}
}
v___jp_2715_:
{
size_t v___x_2717_; size_t v___x_2718_; 
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_add(v_i_2712_, v___x_2717_);
v_i_2712_ = v___x_2718_;
v_b_2713_ = v_a_2716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2761_, lean_object* v_as_2762_, lean_object* v_sz_2763_, lean_object* v_i_2764_, lean_object* v_b_2765_, lean_object* v___y_2766_){
_start:
{
size_t v_sz_boxed_2767_; size_t v_i_boxed_2768_; lean_object* v_res_2769_; 
v_sz_boxed_2767_ = lean_unbox_usize(v_sz_2763_);
lean_dec(v_sz_2763_);
v_i_boxed_2768_ = lean_unbox_usize(v_i_2764_);
lean_dec(v_i_2764_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2761_, v_as_2762_, v_sz_boxed_2767_, v_i_boxed_2768_, v_b_2765_);
lean_dec_ref(v_as_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2770_, size_t v_sz_2771_, size_t v_i_2772_, lean_object* v_b_2773_){
_start:
{
uint8_t v___x_2775_; 
v___x_2775_ = lean_usize_dec_lt(v_i_2772_, v_sz_2771_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_b_2773_);
return v___x_2776_;
}
else
{
lean_object* v_a_2777_; lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2804_; 
v_a_2777_ = lean_array_uget_borrowed(v_as_2770_, v_i_2772_);
v_fst_2778_ = lean_ctor_get(v_a_2777_, 0);
v_snd_2779_ = lean_ctor_get(v_a_2777_, 1);
v_fst_2780_ = lean_ctor_get(v_b_2773_, 0);
v_snd_2781_ = lean_ctor_get(v_b_2773_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_b_2773_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2783_ = v_b_2773_;
v_isShared_2784_ = v_isSharedCheck_2804_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snd_2781_);
lean_inc(v_fst_2780_);
lean_dec(v_b_2773_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2804_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_fst_2780_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_snd_2781_);
v___x_2786_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
size_t v_sz_2787_; size_t v___x_2788_; lean_object* v___x_2789_; 
v_sz_2787_ = lean_array_size(v_snd_2779_);
v___x_2788_ = ((size_t)0ULL);
lean_inc(v_fst_2778_);
v___x_2789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2778_, v_snd_2779_, v_sz_2787_, v___x_2788_, v___x_2786_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2802_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v_fst_2791_ = lean_ctor_get(v_a_2790_, 0);
v_snd_2792_ = lean_ctor_get(v_a_2790_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_a_2790_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2794_ = v_a_2790_;
v_isShared_2795_ = v_isSharedCheck_2802_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snd_2792_);
lean_inc(v_fst_2791_);
lean_dec(v_a_2790_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2802_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_fst_2791_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_snd_2792_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
size_t v___x_2798_; size_t v___x_2799_; 
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_add(v_i_2772_, v___x_2798_);
v_i_2772_ = v___x_2799_;
v_b_2773_ = v___x_2797_;
goto _start;
}
}
}
else
{
return v___x_2789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2805_, lean_object* v_sz_2806_, lean_object* v_i_2807_, lean_object* v_b_2808_, lean_object* v___y_2809_){
_start:
{
size_t v_sz_boxed_2810_; size_t v_i_boxed_2811_; lean_object* v_res_2812_; 
v_sz_boxed_2810_ = lean_unbox_usize(v_sz_2806_);
lean_dec(v_sz_2806_);
v_i_boxed_2811_ = lean_unbox_usize(v_i_2807_);
lean_dec(v_i_2807_);
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2805_, v_sz_boxed_2810_, v_i_boxed_2811_, v_b_2808_);
lean_dec_ref(v_as_2805_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2813_, size_t v_sz_2814_, size_t v_i_2815_, lean_object* v_b_2816_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_lt(v_i_2815_, v_sz_2814_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_b_2816_);
return v___x_2819_;
}
else
{
lean_object* v_a_2820_; lean_object* v_message_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2820_ = lean_array_uget_borrowed(v_as_2813_, v_i_2815_);
v_message_2821_ = lean_ctor_get(v_a_2820_, 1);
v___x_2822_ = 0;
lean_inc_ref(v_message_2821_);
v___x_2823_ = l_Lean_SerialMessage_toString(v_message_2821_, v___x_2822_);
v___x_2824_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2823_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; 
lean_dec_ref_known(v___x_2824_, 1);
v___x_2825_ = lean_box(0);
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2815_, v___x_2826_);
v_i_2815_ = v___x_2827_;
v_b_2816_ = v___x_2825_;
goto _start;
}
else
{
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2829_, lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2829_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2832_);
lean_dec_ref(v_as_2829_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2839_, size_t v_sz_2840_, size_t v_i_2841_, lean_object* v_b_2842_){
_start:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_usize_dec_lt(v_i_2841_, v_sz_2840_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_b_2842_);
return v___x_2845_;
}
else
{
lean_object* v_a_2846_; lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2846_ = lean_array_uget_borrowed(v_as_2839_, v_i_2841_);
v_fst_2847_ = lean_ctor_get(v_a_2846_, 0);
v_snd_2848_ = lean_ctor_get(v_a_2846_, 1);
v___x_2849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_2847_);
v___x_2850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2847_, v___x_2844_);
v___x_2851_ = lean_string_append(v___x_2849_, v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
v___x_2854_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref_known(v___x_2854_, 1);
v___x_2855_ = lean_box(0);
v_sz_2856_ = lean_array_size(v_snd_2848_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_2848_, v_sz_2856_, v___x_2857_, v___x_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
size_t v___x_2859_; size_t v___x_2860_; 
lean_dec_ref_known(v___x_2858_, 1);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_i_2841_, v___x_2859_);
v_i_2841_ = v___x_2860_;
v_b_2842_ = v___x_2855_;
goto _start;
}
else
{
return v___x_2858_;
}
}
else
{
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_){
_start:
{
size_t v_sz_boxed_2867_; size_t v_i_boxed_2868_; lean_object* v_res_2869_; 
v_sz_boxed_2867_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2868_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_2862_, v_sz_boxed_2867_, v_i_boxed_2868_, v_b_2865_);
lean_dec_ref(v_as_2862_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_2876_, lean_object* v_linterOpts_2877_, lean_object* v_env_2878_, lean_object* v_mod_2879_){
_start:
{
uint8_t v_lintOnly_2881_; uint8_t v_mode_2882_; lean_object* v___y_2884_; uint8_t v___y_2885_; lean_object* v___y_2953_; lean_object* v___x_2959_; lean_object* v_textGroups_2960_; 
v_lintOnly_2881_ = lean_ctor_get_uint8(v_args_2876_, sizeof(void*)*3);
v_mode_2882_ = lean_ctor_get_uint8(v_args_2876_, sizeof(void*)*3 + 1);
v___x_2959_ = l_Lean_Name_getRoot(v_mod_2879_);
v_textGroups_2960_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_2878_, v___x_2959_);
lean_dec(v___x_2959_);
if (v_lintOnly_2881_ == 0)
{
v___y_2953_ = v_textGroups_2960_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_array_get_size(v_textGroups_2960_);
v___x_2963_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2877_, v_textGroups_2960_, v___x_2961_, v___x_2962_);
lean_dec_ref(v_textGroups_2960_);
v___y_2953_ = v___x_2963_;
goto v___jp_2952_;
}
v___jp_2883_:
{
switch(v_mode_2882_)
{
case 0:
{
lean_object* v___x_2886_; size_t v_sz_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_box(0);
v_sz_2887_ = lean_array_size(v___y_2884_);
v___x_2888_ = ((size_t)0ULL);
v___x_2889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_2884_, v_sz_2887_, v___x_2888_, v___x_2886_);
lean_dec_ref(v___y_2884_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2897_; 
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2898_);
v___x_2891_ = v___x_2889_;
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v___x_2889_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2897_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2893_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2893_, 0, v___y_2885_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2895_ = v___x_2891_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2889_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2889_);
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
case 1:
{
lean_object* v___x_2907_; size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2907_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_2908_ = lean_array_size(v___y_2884_);
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_2884_, v_sz_2908_, v___x_2909_, v___x_2907_);
lean_dec_ref(v___y_2884_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2922_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2922_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2922_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2920_; 
v_fst_2915_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_fst_2915_);
v_snd_2916_ = lean_ctor_get(v_a_2911_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_a_2911_);
v___x_2917_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2917_, 0, v_fst_2915_);
v___x_2918_ = lean_unbox(v_snd_2916_);
lean_dec(v_snd_2916_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*1, v___x_2918_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2917_);
v___x_2920_ = v___x_2913_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2917_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_a_2923_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2910_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2910_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_2931_; size_t v_sz_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
v_codeQualityEntries_2931_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1));
v_sz_2932_ = lean_array_size(v___y_2884_);
v___x_2933_ = ((size_t)0ULL);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_2884_, v_sz_2932_, v___x_2933_, v_codeQualityEntries_2931_);
lean_dec_ref(v___y_2884_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2943_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2943_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2943_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2939_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2934_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2934_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
v___jp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2954_ = lean_array_get_size(v___y_2953_);
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = lean_nat_dec_eq(v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
uint8_t v___x_2957_; 
v___x_2957_ = 1;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___x_2957_;
goto v___jp_2883_;
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___x_2958_;
goto v___jp_2883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_2964_, lean_object* v_linterOpts_2965_, lean_object* v_env_2966_, lean_object* v_mod_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_2964_, v_linterOpts_2965_, v_env_2966_, v_mod_2967_);
lean_dec(v_mod_2967_);
lean_dec_ref(v_env_2966_);
lean_dec_ref(v_linterOpts_2965_);
lean_dec_ref(v_args_2964_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_00_u03b4_2970_, lean_object* v_t_2971_, lean_object* v_k_2972_, lean_object* v_fallback_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___redArg(v_t_2971_, v_k_2972_, v_fallback_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_00_u03b4_2975_, lean_object* v_t_2976_, lean_object* v_k_2977_, lean_object* v_fallback_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_00_u03b4_2975_, v_t_2976_, v_k_2977_, v_fallback_2978_);
lean_dec(v_fallback_2978_);
lean_dec(v_k_2977_);
lean_dec(v_t_2976_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_2980_, lean_object* v_____r_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2985_, 0, v___y_2980_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_2987_, lean_object* v_____r_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v___y_17040__boxed_2992_; lean_object* v_res_2993_; 
v___y_17040__boxed_2992_ = lean_unbox(v___y_2987_);
v_res_2993_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_17040__boxed_2992_, v_____r_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
return v_res_2993_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2994_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_ctor_set(v___x_2999_, 3, v___x_2998_);
lean_ctor_set(v___x_2999_, 4, v___x_2997_);
lean_ctor_set(v___x_2999_, 5, v___x_2997_);
lean_ctor_set(v___x_2999_, 6, v___x_2997_);
lean_ctor_set(v___x_2999_, 7, v___x_2997_);
lean_ctor_set(v___x_2999_, 8, v___x_2997_);
lean_ctor_set(v___x_2999_, 9, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_unsigned_to_nat(32u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3003_ = ((size_t)5ULL);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_unsigned_to_nat(32u);
v___x_3006_ = lean_mk_empty_array_with_capacity(v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3008_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3006_);
lean_ctor_set(v___x_3008_, 2, v___x_3004_);
lean_ctor_set(v___x_3008_, 3, v___x_3004_);
lean_ctor_set_usize(v___x_3008_, 4, v___x_3003_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = lean_box(1);
v___x_3010_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3011_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v___x_3010_);
lean_ctor_set(v___x_3012_, 2, v___x_3009_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_env_3018_; lean_object* v_options_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3017_ = lean_st_ref_get(v___y_3015_);
v_env_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_env_3018_);
lean_dec(v___x_3017_);
v_options_3019_ = lean_ctor_get(v___y_3014_, 2);
v___x_3020_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3021_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3019_);
v___x_3022_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3022_, 0, v_env_3018_);
lean_ctor_set(v___x_3022_, 1, v___x_3020_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
lean_ctor_set(v___x_3022_, 3, v_options_3019_);
v___x_3023_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_msgData_3013_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_ref_3034_; lean_object* v___x_3035_; lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3044_; 
v_ref_3034_ = lean_ctor_get(v___y_3031_, 5);
v___x_3035_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3030_, v___y_3031_, v___y_3032_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3044_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3044_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
lean_inc(v_ref_3034_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v_ref_3034_);
lean_ctor_set(v___x_3040_, 1, v_a_3036_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 1);
lean_ctor_set(v___x_3038_, 0, v___x_3040_);
v___x_3042_ = v___x_3038_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3050_, lean_object* v_msg_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_fileName_3055_; lean_object* v_fileMap_3056_; lean_object* v_options_3057_; lean_object* v_currRecDepth_3058_; lean_object* v_maxRecDepth_3059_; lean_object* v_ref_3060_; lean_object* v_currNamespace_3061_; lean_object* v_openDecls_3062_; lean_object* v_initHeartbeats_3063_; lean_object* v_maxHeartbeats_3064_; lean_object* v_quotContext_3065_; lean_object* v_currMacroScope_3066_; uint8_t v_diag_3067_; lean_object* v_cancelTk_x3f_3068_; uint8_t v_suppressElabErrors_3069_; lean_object* v_inheritedTraceOptions_3070_; lean_object* v_ref_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_fileName_3055_ = lean_ctor_get(v___y_3052_, 0);
v_fileMap_3056_ = lean_ctor_get(v___y_3052_, 1);
v_options_3057_ = lean_ctor_get(v___y_3052_, 2);
v_currRecDepth_3058_ = lean_ctor_get(v___y_3052_, 3);
v_maxRecDepth_3059_ = lean_ctor_get(v___y_3052_, 4);
v_ref_3060_ = lean_ctor_get(v___y_3052_, 5);
v_currNamespace_3061_ = lean_ctor_get(v___y_3052_, 6);
v_openDecls_3062_ = lean_ctor_get(v___y_3052_, 7);
v_initHeartbeats_3063_ = lean_ctor_get(v___y_3052_, 8);
v_maxHeartbeats_3064_ = lean_ctor_get(v___y_3052_, 9);
v_quotContext_3065_ = lean_ctor_get(v___y_3052_, 10);
v_currMacroScope_3066_ = lean_ctor_get(v___y_3052_, 11);
v_diag_3067_ = lean_ctor_get_uint8(v___y_3052_, sizeof(void*)*14);
v_cancelTk_x3f_3068_ = lean_ctor_get(v___y_3052_, 12);
v_suppressElabErrors_3069_ = lean_ctor_get_uint8(v___y_3052_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3070_ = lean_ctor_get(v___y_3052_, 13);
v_ref_3071_ = l_Lean_replaceRef(v_ref_3050_, v_ref_3060_);
lean_inc_ref(v_inheritedTraceOptions_3070_);
lean_inc(v_cancelTk_x3f_3068_);
lean_inc(v_currMacroScope_3066_);
lean_inc(v_quotContext_3065_);
lean_inc(v_maxHeartbeats_3064_);
lean_inc(v_initHeartbeats_3063_);
lean_inc(v_openDecls_3062_);
lean_inc(v_currNamespace_3061_);
lean_inc(v_maxRecDepth_3059_);
lean_inc(v_currRecDepth_3058_);
lean_inc_ref(v_options_3057_);
lean_inc_ref(v_fileMap_3056_);
lean_inc_ref(v_fileName_3055_);
v___x_3072_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3072_, 0, v_fileName_3055_);
lean_ctor_set(v___x_3072_, 1, v_fileMap_3056_);
lean_ctor_set(v___x_3072_, 2, v_options_3057_);
lean_ctor_set(v___x_3072_, 3, v_currRecDepth_3058_);
lean_ctor_set(v___x_3072_, 4, v_maxRecDepth_3059_);
lean_ctor_set(v___x_3072_, 5, v_ref_3071_);
lean_ctor_set(v___x_3072_, 6, v_currNamespace_3061_);
lean_ctor_set(v___x_3072_, 7, v_openDecls_3062_);
lean_ctor_set(v___x_3072_, 8, v_initHeartbeats_3063_);
lean_ctor_set(v___x_3072_, 9, v_maxHeartbeats_3064_);
lean_ctor_set(v___x_3072_, 10, v_quotContext_3065_);
lean_ctor_set(v___x_3072_, 11, v_currMacroScope_3066_);
lean_ctor_set(v___x_3072_, 12, v_cancelTk_x3f_3068_);
lean_ctor_set(v___x_3072_, 13, v_inheritedTraceOptions_3070_);
lean_ctor_set_uint8(v___x_3072_, sizeof(void*)*14, v_diag_3067_);
lean_ctor_set_uint8(v___x_3072_, sizeof(void*)*14 + 1, v_suppressElabErrors_3069_);
v___x_3073_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3051_, v___x_3072_, v___y_3053_);
lean_dec_ref_known(v___x_3072_, 14);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3074_, lean_object* v_msg_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3074_, v_msg_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v_ref_3074_);
return v_res_3079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3088_ = l_Lean_stringToMessageData(v___x_3087_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3091_ = l_Lean_stringToMessageData(v___x_3090_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3097_ = l_Lean_stringToMessageData(v___x_3096_);
return v___x_3097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3100_ = l_Lean_stringToMessageData(v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3101_, lean_object* v_declHint_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v_env_3106_; uint8_t v___x_3107_; 
v___x_3105_ = lean_st_ref_get(v___y_3103_);
v_env_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_env_3106_);
lean_dec(v___x_3105_);
v___x_3107_ = l_Lean_Name_isAnonymous(v_declHint_3102_);
if (v___x_3107_ == 0)
{
uint8_t v_isExporting_3108_; 
v_isExporting_3108_ = lean_ctor_get_uint8(v_env_3106_, sizeof(void*)*8);
if (v_isExporting_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_dec_ref(v_env_3106_);
lean_dec(v_declHint_3102_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_msg_3101_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
lean_inc_ref(v_env_3106_);
v___x_3110_ = l_Lean_Environment_setExporting(v_env_3106_, v___x_3107_);
lean_inc(v_declHint_3102_);
lean_inc_ref(v___x_3110_);
v___x_3111_ = l_Lean_Environment_contains(v___x_3110_, v_declHint_3102_, v_isExporting_3108_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; 
lean_dec_ref(v___x_3110_);
lean_dec_ref(v_env_3106_);
lean_dec(v_declHint_3102_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_msg_3101_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_c_3118_; lean_object* v___x_3119_; 
v___x_3113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3115_ = l_Lean_Options_empty;
v___x_3116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3110_);
lean_ctor_set(v___x_3116_, 1, v___x_3113_);
lean_ctor_set(v___x_3116_, 2, v___x_3114_);
lean_ctor_set(v___x_3116_, 3, v___x_3115_);
lean_inc(v_declHint_3102_);
v___x_3117_ = l_Lean_MessageData_ofConstName(v_declHint_3102_, v___x_3107_);
v_c_3118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3118_, 0, v___x_3116_);
lean_ctor_set(v_c_3118_, 1, v___x_3117_);
v___x_3119_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3106_, v_declHint_3102_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v_env_3106_);
lean_dec(v_declHint_3102_);
v___x_3120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v_c_3118_);
v___x_3122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_MessageData_note(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_msg_3101_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
else
{
lean_object* v_val_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3162_; 
v_val_3127_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3129_ = v___x_3119_;
v_isShared_3130_ = v_isSharedCheck_3162_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_val_3127_);
lean_dec(v___x_3119_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3162_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v_mod_3134_; uint8_t v___x_3135_; 
v___x_3131_ = lean_box(0);
v___x_3132_ = l_Lean_Environment_header(v_env_3106_);
lean_dec_ref(v_env_3106_);
v___x_3133_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3132_);
v_mod_3134_ = lean_array_get(v___x_3131_, v___x_3133_, v_val_3127_);
lean_dec(v_val_3127_);
lean_dec_ref(v___x_3133_);
v___x_3135_ = l_Lean_isPrivateName(v_declHint_3102_);
lean_dec(v_declHint_3102_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v_c_3118_);
v___x_3138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3137_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Lean_MessageData_ofName(v_mod_3134_);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = l_Lean_MessageData_note(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_msg_3101_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3145_);
v___x_3147_ = v___x_3129_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v_c_3118_);
v___x_3151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_MessageData_ofName(v_mod_3134_);
v___x_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_MessageData_note(v___x_3156_);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_msg_3101_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3158_);
v___x_3160_ = v___x_3129_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
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
}
}
else
{
lean_object* v___x_3163_; 
lean_dec_ref(v_env_3106_);
lean_dec(v_declHint_3102_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_msg_3101_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3164_, lean_object* v_declHint_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3164_, v_declHint_3165_, v___y_3166_);
lean_dec(v___y_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3169_, lean_object* v_declHint_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3184_; 
v___x_3174_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3169_, v_declHint_3170_, v___y_3172_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3179_ = l_Lean_unknownIdentifierMessageTag;
v___x_3180_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v_a_3175_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3180_);
v___x_3182_ = v___x_3177_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3185_, lean_object* v_declHint_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3185_, v_declHint_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3191_, lean_object* v_msg_3192_, lean_object* v_declHint_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3199_; 
v___x_3197_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3192_, v_declHint_3193_, v___y_3194_, v___y_3195_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3191_, v_a_3198_, v___y_3194_, v___y_3195_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3200_, lean_object* v_msg_3201_, lean_object* v_declHint_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3200_, v_msg_3201_, v_declHint_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v_ref_3200_);
return v_res_3206_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3211_ = l_Lean_stringToMessageData(v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3212_, lean_object* v_constName_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3217_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3218_ = 0;
lean_inc(v_constName_3213_);
v___x_3219_ = l_Lean_MessageData_ofConstName(v_constName_3213_, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3217_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3212_, v___x_3222_, v_constName_3213_, v___y_3214_, v___y_3215_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3224_, lean_object* v_constName_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3224_, v_constName_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v_ref_3224_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_ref_3234_; lean_object* v___x_3235_; 
v_ref_3234_ = lean_ctor_get(v___y_3231_, 5);
v___x_3235_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3234_, v_constName_3230_, v___y_3231_, v___y_3232_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v_env_3246_; uint8_t v___x_3247_; lean_object* v___x_3248_; 
v___x_3245_ = lean_st_ref_get(v___y_3243_);
v_env_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc_ref(v_env_3246_);
lean_dec(v___x_3245_);
v___x_3247_ = 0;
lean_inc(v_constName_3241_);
v___x_3248_ = l_Lean_Environment_find_x3f(v_env_3246_, v_constName_3241_, v___x_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3241_, v___y_3242_, v___y_3243_);
return v___x_3249_;
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_constName_3241_);
v_val_3250_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3248_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_val_3250_);
lean_dec(v___x_3248_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set_tag(v___x_3252_, 0);
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_val_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
lean_inc(v_declName_3263_);
v___x_3267_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3294_; 
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3294_ == 0)
{
lean_object* v_unused_3295_; 
v_unused_3295_ = lean_ctor_get(v___x_3267_, 0);
lean_dec(v_unused_3295_);
v___x_3269_ = v___x_3267_;
v_isShared_3270_ = v_isSharedCheck_3294_;
goto v_resetjp_3268_;
}
else
{
lean_dec(v___x_3267_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3294_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v_env_3272_; lean_object* v___x_3273_; 
v___x_3271_ = lean_st_ref_get(v___y_3265_);
v_env_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc_ref(v_env_3272_);
lean_dec(v___x_3271_);
v___x_3273_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3272_, v_declName_3263_);
lean_dec(v_declName_3263_);
lean_dec_ref(v_env_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_box(0);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3274_);
v___x_3276_ = v___x_3269_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
else
{
lean_object* v_val_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3293_; 
v_val_3278_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3280_ = v___x_3273_;
v_isShared_3281_ = v_isSharedCheck_3293_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_val_3278_);
lean_dec(v___x_3273_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3293_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v_env_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3282_ = lean_st_ref_get(v___y_3265_);
v_env_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc_ref(v_env_3283_);
lean_dec(v___x_3282_);
v___x_3284_ = lean_box(0);
v___x_3285_ = l_Lean_Environment_allImportedModuleNames(v_env_3283_);
lean_dec_ref(v_env_3283_);
v___x_3286_ = lean_array_get(v___x_3284_, v___x_3285_, v_val_3278_);
lean_dec(v_val_3278_);
lean_dec_ref(v___x_3285_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3286_);
v___x_3288_ = v___x_3280_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3290_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3288_);
v___x_3290_ = v___x_3269_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_declName_3263_);
v_a_3296_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3267_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3267_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3310_, lean_object* v_sp_3311_, lean_object* v___x_3312_, lean_object* v_as_3313_, size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_a_3321_; uint8_t v___x_3325_; 
v___x_3325_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_b_3316_);
return v___x_3326_;
}
else
{
lean_object* v_a_3327_; lean_object* v_fst_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3463_; 
v_a_3327_ = lean_array_uget(v_as_3313_, v_i_3315_);
v_fst_3328_ = lean_ctor_get(v_a_3327_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3327_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v_a_3327_, 1);
lean_dec(v_unused_3464_);
v___x_3330_ = v_a_3327_;
v_isShared_3331_ = v_isSharedCheck_3463_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_fst_3328_);
lean_dec(v_a_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3463_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; 
lean_inc(v_fst_3328_);
v___x_3332_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3328_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
if (lean_obj_tag(v_a_3333_) == 0)
{
lean_object* v_fst_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3368_; 
v_fst_3334_ = lean_ctor_get(v_b_3316_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_b_3316_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v_b_3316_, 1);
lean_dec(v_unused_3369_);
v___x_3336_ = v_b_3316_;
v_isShared_3337_ = v_isSharedCheck_3368_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_fst_3334_);
lean_dec(v_b_3316_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3368_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_optName_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_optName_3338_ = lean_ctor_get(v_fst_3310_, 1);
v___x_3339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3328_, v___x_3325_);
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
lean_inc(v_optName_3338_);
v___x_3344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3338_, v___x_3325_);
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3347_ = lean_string_append(v___x_3345_, v___x_3346_);
v___x_3348_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_dec_ref_known(v___x_3348_, 1);
lean_del_object(v___x_3330_);
v___x_3349_ = lean_box(v___x_3325_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3349_);
v___x_3351_ = v___x_3336_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_fst_3334_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
v_a_3321_ = v___x_3351_;
goto v___jp_3320_;
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3367_; 
lean_del_object(v___x_3336_);
lean_dec(v_fst_3334_);
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v_a_3353_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3355_ = v___x_3348_;
v_isShared_3356_ = v_isSharedCheck_3367_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3348_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3367_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_ref_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v_ref_3357_ = lean_ctor_get(v___y_3317_, 5);
v___x_3358_ = lean_io_error_to_string(v_a_3353_);
v___x_3359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
v___x_3360_ = l_Lean_MessageData_ofFormat(v___x_3359_);
lean_inc(v_ref_3357_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3360_);
lean_ctor_set(v___x_3330_, 0, v_ref_3357_);
v___x_3362_ = v___x_3330_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_ref_3357_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3362_);
v___x_3364_ = v___x_3355_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3454_; 
v_fst_3370_ = lean_ctor_get(v_b_3316_, 0);
v_snd_3371_ = lean_ctor_get(v_b_3316_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_b_3316_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3373_ = v_b_3316_;
v_isShared_3374_ = v_isSharedCheck_3454_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3370_);
lean_dec(v_b_3316_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3454_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_val_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3453_; 
v_val_3375_ = lean_ctor_get(v_a_3333_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_a_3333_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3377_ = v_a_3333_;
v_isShared_3378_ = v_isSharedCheck_3453_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_val_3375_);
lean_dec(v_a_3333_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3453_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3328_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___y_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
if (lean_obj_tag(v_a_3380_) == 0)
{
lean_inc(v___x_3312_);
v___y_3382_ = v___x_3312_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3444_; 
v_val_3444_ = lean_ctor_get(v_a_3380_, 0);
lean_inc(v_val_3444_);
lean_dec_ref_known(v_a_3380_, 1);
v___y_3382_ = v_val_3444_;
goto v___jp_3381_;
}
v___jp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3382_);
lean_inc(v_sp_3311_);
v___x_3384_ = l_Lean_SearchPath_findWithExt(v_sp_3311_, v___x_3383_, v___y_3382_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
if (lean_obj_tag(v_a_3385_) == 0)
{
lean_object* v_optName_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec(v_val_3375_);
lean_dec(v_snd_3371_);
v_optName_3386_ = lean_ctor_get(v_fst_3310_, 1);
v___x_3387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3388_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3382_, v___x_3325_);
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
lean_inc(v_optName_3386_);
v___x_3392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3386_, v___x_3325_);
v___x_3393_ = lean_string_append(v___x_3391_, v___x_3392_);
lean_dec_ref(v___x_3392_);
v___x_3394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3395_ = lean_string_append(v___x_3393_, v___x_3394_);
v___x_3396_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_dec_ref_known(v___x_3396_, 1);
lean_del_object(v___x_3377_);
lean_del_object(v___x_3330_);
v___x_3397_ = lean_box(v___x_3325_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v___x_3397_);
v___x_3399_ = v___x_3373_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_fst_3370_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
v_a_3321_ = v___x_3399_;
goto v___jp_3320_;
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3373_);
lean_dec(v_fst_3370_);
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v_a_3401_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3403_ = v___x_3396_;
v_isShared_3404_ = v_isSharedCheck_3417_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3396_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3417_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_ref_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_ref_3405_ = lean_ctor_get(v___y_3317_, 5);
v___x_3406_ = lean_io_error_to_string(v_a_3401_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set_tag(v___x_3377_, 3);
lean_ctor_set(v___x_3377_, 0, v___x_3406_);
v___x_3408_ = v___x_3377_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = l_Lean_MessageData_ofFormat(v___x_3408_);
lean_inc(v_ref_3405_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3409_);
lean_ctor_set(v___x_3330_, 0, v_ref_3405_);
v___x_3411_ = v___x_3330_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_ref_3405_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3411_);
v___x_3413_ = v___x_3403_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
else
{
lean_object* v_range_3418_; lean_object* v_val_3419_; lean_object* v_pos_3420_; lean_object* v_optName_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
lean_dec(v___y_3382_);
lean_del_object(v___x_3377_);
lean_del_object(v___x_3330_);
v_range_3418_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_range_3418_);
lean_dec(v_val_3375_);
v_val_3419_ = lean_ctor_get(v_a_3385_, 0);
lean_inc(v_val_3419_);
lean_dec_ref_known(v_a_3385_, 1);
v_pos_3420_ = lean_ctor_get(v_range_3418_, 0);
lean_inc_ref(v_pos_3420_);
lean_dec_ref(v_range_3418_);
v_optName_3421_ = lean_ctor_get(v_fst_3310_, 1);
lean_inc(v_optName_3421_);
v___x_3422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3422_, 0, v_val_3419_);
lean_ctor_set(v___x_3422_, 1, v_pos_3420_);
lean_ctor_set(v___x_3422_, 2, v_optName_3421_);
v___x_3423_ = lean_array_push(v_fst_3370_, v___x_3422_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3423_);
v___x_3425_ = v___x_3373_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_snd_3371_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
v_a_3321_ = v___x_3425_;
goto v___jp_3320_;
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___y_3382_);
lean_dec(v_val_3375_);
lean_del_object(v___x_3373_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v_a_3427_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3429_ = v___x_3384_;
v_isShared_3430_ = v_isSharedCheck_3443_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3384_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3443_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_ref_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v_ref_3431_ = lean_ctor_get(v___y_3317_, 5);
v___x_3432_ = lean_io_error_to_string(v_a_3427_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set_tag(v___x_3377_, 3);
lean_ctor_set(v___x_3377_, 0, v___x_3432_);
v___x_3434_ = v___x_3377_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_MessageData_ofFormat(v___x_3434_);
lean_inc(v_ref_3431_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3435_);
lean_ctor_set(v___x_3330_, 0, v_ref_3431_);
v___x_3437_ = v___x_3330_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_ref_3431_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3437_);
v___x_3439_ = v___x_3429_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_del_object(v___x_3377_);
lean_dec(v_val_3375_);
lean_del_object(v___x_3373_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
lean_del_object(v___x_3330_);
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v_a_3445_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3379_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3379_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3330_);
lean_dec(v_fst_3328_);
lean_dec_ref(v_b_3316_);
lean_dec(v___x_3312_);
lean_dec(v_sp_3311_);
lean_dec_ref(v_fst_3310_);
v_a_3455_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3332_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3332_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
v___jp_3320_:
{
size_t v___x_3322_; size_t v___x_3323_; 
v___x_3322_ = ((size_t)1ULL);
v___x_3323_ = lean_usize_add(v_i_3315_, v___x_3322_);
v_i_3315_ = v___x_3323_;
v_b_3316_ = v_a_3321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3465_, lean_object* v_sp_3466_, lean_object* v___x_3467_, lean_object* v_as_3468_, lean_object* v_sz_3469_, lean_object* v_i_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
size_t v_sz_boxed_3475_; size_t v_i_boxed_3476_; lean_object* v_res_3477_; 
v_sz_boxed_3475_ = lean_unbox_usize(v_sz_3469_);
lean_dec(v_sz_3469_);
v_i_boxed_3476_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_res_3477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3465_, v_sp_3466_, v___x_3467_, v_as_3468_, v_sz_boxed_3475_, v_i_boxed_3476_, v_b_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_as_3468_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3478_, lean_object* v_x_3479_){
_start:
{
if (lean_obj_tag(v_x_3479_) == 0)
{
return v_x_3478_;
}
else
{
lean_object* v_key_3480_; lean_object* v_value_3481_; lean_object* v_tail_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v_key_3480_ = lean_ctor_get(v_x_3479_, 0);
v_value_3481_ = lean_ctor_get(v_x_3479_, 1);
v_tail_3482_ = lean_ctor_get(v_x_3479_, 2);
lean_inc(v_value_3481_);
lean_inc(v_key_3480_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_key_3480_);
lean_ctor_set(v___x_3483_, 1, v_value_3481_);
v___x_3484_ = lean_array_push(v_x_3478_, v___x_3483_);
v_x_3478_ = v___x_3484_;
v_x_3479_ = v_tail_3482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3486_, v_x_3487_);
lean_dec(v_x_3487_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3489_, size_t v_i_3490_, size_t v_stop_3491_, lean_object* v_b_3492_){
_start:
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_usize_dec_eq(v_i_3490_, v_stop_3491_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; size_t v___x_3496_; size_t v___x_3497_; 
v___x_3494_ = lean_array_uget_borrowed(v_as_3489_, v_i_3490_);
v___x_3495_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3492_, v___x_3494_);
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3490_, v___x_3496_);
v_i_3490_ = v___x_3497_;
v_b_3492_ = v___x_3495_;
goto _start;
}
else
{
return v_b_3492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3499_, lean_object* v_i_3500_, lean_object* v_stop_3501_, lean_object* v_b_3502_){
_start:
{
size_t v_i_boxed_3503_; size_t v_stop_boxed_3504_; lean_object* v_res_3505_; 
v_i_boxed_3503_ = lean_unbox_usize(v_i_3500_);
lean_dec(v_i_3500_);
v_stop_boxed_3504_ = lean_unbox_usize(v_stop_3501_);
lean_dec(v_stop_3501_);
v_res_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3499_, v_i_boxed_3503_, v_stop_boxed_3504_, v_b_3502_);
lean_dec_ref(v_as_3499_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3506_, lean_object* v___x_3507_, lean_object* v_as_3508_, size_t v_sz_3509_, size_t v_i_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_usize_dec_lt(v_i_3510_, v_sz_3509_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v___x_3507_);
lean_dec(v_sp_3506_);
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_b_3511_);
return v___x_3516_;
}
else
{
lean_object* v_a_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v_fst_3520_; lean_object* v_snd_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3559_; 
v_a_3517_ = lean_array_uget_borrowed(v_as_3508_, v_i_3510_);
v_fst_3518_ = lean_ctor_get(v_a_3517_, 0);
v_snd_3519_ = lean_ctor_get(v_a_3517_, 1);
v_fst_3520_ = lean_ctor_get(v_b_3511_, 0);
v_snd_3521_ = lean_ctor_get(v_b_3511_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_b_3511_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3523_ = v_b_3511_;
v_isShared_3524_ = v_isSharedCheck_3559_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_snd_3521_);
lean_inc(v_fst_3520_);
lean_dec(v_b_3511_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3559_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___y_3526_; lean_object* v_size_3546_; lean_object* v_buckets_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_size_3546_ = lean_ctor_get(v_snd_3519_, 0);
v_buckets_3547_ = lean_ctor_get(v_snd_3519_, 1);
v___x_3548_ = lean_mk_empty_array_with_capacity(v_size_3546_);
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = lean_array_get_size(v_buckets_3547_);
v___x_3551_ = lean_nat_dec_lt(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
v___y_3526_ = v___x_3548_;
goto v___jp_3525_;
}
else
{
uint8_t v___x_3552_; 
v___x_3552_ = lean_nat_dec_le(v___x_3550_, v___x_3550_);
if (v___x_3552_ == 0)
{
if (v___x_3551_ == 0)
{
v___y_3526_ = v___x_3548_;
goto v___jp_3525_;
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3550_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3547_, v___x_3553_, v___x_3554_, v___x_3548_);
v___y_3526_ = v___x_3555_;
goto v___jp_3525_;
}
}
else
{
size_t v___x_3556_; size_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = lean_usize_of_nat(v___x_3550_);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3547_, v___x_3556_, v___x_3557_, v___x_3548_);
v___y_3526_ = v___x_3558_;
goto v___jp_3525_;
}
}
v___jp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3524_ == 0)
{
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_fst_3520_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_snd_3521_);
v___x_3528_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v_sz_3529_ = lean_array_size(v___y_3526_);
v___x_3530_ = ((size_t)0ULL);
lean_inc(v___x_3507_);
lean_inc(v_sp_3506_);
lean_inc(v_fst_3518_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3518_, v_sp_3506_, v___x_3507_, v___y_3526_, v_sz_3529_, v___x_3530_, v___x_3528_, v___y_3512_, v___y_3513_);
lean_dec_ref(v___y_3526_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v_fst_3533_; lean_object* v_snd_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3544_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v_fst_3533_ = lean_ctor_get(v_a_3532_, 0);
v_snd_3534_ = lean_ctor_get(v_a_3532_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3532_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3536_ = v_a_3532_;
v_isShared_3537_ = v_isSharedCheck_3544_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_snd_3534_);
lean_inc(v_fst_3533_);
lean_dec(v_a_3532_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3544_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_fst_3533_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_snd_3534_);
v___x_3539_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
size_t v___x_3540_; size_t v___x_3541_; 
v___x_3540_ = ((size_t)1ULL);
v___x_3541_ = lean_usize_add(v_i_3510_, v___x_3540_);
v_i_3510_ = v___x_3541_;
v_b_3511_ = v___x_3539_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3507_);
lean_dec(v_sp_3506_);
return v___x_3531_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3560_, lean_object* v___x_3561_, lean_object* v_as_3562_, lean_object* v_sz_3563_, lean_object* v_i_3564_, lean_object* v_b_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
size_t v_sz_boxed_3569_; size_t v_i_boxed_3570_; lean_object* v_res_3571_; 
v_sz_boxed_3569_ = lean_unbox_usize(v_sz_3563_);
lean_dec(v_sz_3563_);
v_i_boxed_3570_ = lean_unbox_usize(v_i_3564_);
lean_dec(v_i_3564_);
v_res_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3560_, v___x_3561_, v_as_3562_, v_sz_boxed_3569_, v_i_boxed_3570_, v_b_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec_ref(v_as_3562_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3572_, lean_object* v_as_3573_, size_t v_i_3574_, size_t v_stop_3575_){
_start:
{
uint8_t v___x_3576_; 
v___x_3576_ = lean_usize_dec_eq(v_i_3574_, v_stop_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v_snd_3578_; lean_object* v_size_3579_; uint8_t v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3577_ = lean_array_uget_borrowed(v_as_3573_, v_i_3574_);
v_snd_3578_ = lean_ctor_get(v___x_3577_, 1);
v_size_3579_ = lean_ctor_get(v_snd_3578_, 0);
v___x_3580_ = 1;
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = lean_nat_dec_eq(v_size_3579_, v___x_3581_);
if (v___x_3582_ == 0)
{
return v___x_3580_;
}
else
{
if (v___y_3572_ == 0)
{
size_t v___x_3583_; size_t v___x_3584_; 
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_add(v_i_3574_, v___x_3583_);
v_i_3574_ = v___x_3584_;
goto _start;
}
else
{
return v___x_3580_;
}
}
}
else
{
uint8_t v___x_3586_; 
v___x_3586_ = 0;
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3587_, lean_object* v_as_3588_, lean_object* v_i_3589_, lean_object* v_stop_3590_){
_start:
{
uint8_t v___y_18029__boxed_3591_; size_t v_i_boxed_3592_; size_t v_stop_boxed_3593_; uint8_t v_res_3594_; lean_object* v_r_3595_; 
v___y_18029__boxed_3591_ = lean_unbox(v___y_3587_);
v_i_boxed_3592_ = lean_unbox_usize(v_i_3589_);
lean_dec(v_i_3589_);
v_stop_boxed_3593_ = lean_unbox_usize(v_stop_3590_);
lean_dec(v_stop_3590_);
v_res_3594_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_18029__boxed_3591_, v_as_3588_, v_i_boxed_3592_, v_stop_boxed_3593_);
lean_dec_ref(v_as_3588_);
v_r_3595_ = lean_box(v_res_3594_);
return v_r_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3596_, lean_object* v_v_3597_, lean_object* v_t_3598_){
_start:
{
lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; 
if (lean_obj_tag(v_t_3598_) == 0)
{
lean_object* v_size_3613_; lean_object* v_k_3614_; lean_object* v_v_3615_; lean_object* v_l_3616_; lean_object* v_r_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3877_; 
v_size_3613_ = lean_ctor_get(v_t_3598_, 0);
v_k_3614_ = lean_ctor_get(v_t_3598_, 1);
v_v_3615_ = lean_ctor_get(v_t_3598_, 2);
v_l_3616_ = lean_ctor_get(v_t_3598_, 3);
v_r_3617_ = lean_ctor_get(v_t_3598_, 4);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_t_3598_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3619_ = v_t_3598_;
v_isShared_3620_ = v_isSharedCheck_3877_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_r_3617_);
lean_inc(v_l_3616_);
lean_inc(v_v_3615_);
lean_inc(v_k_3614_);
lean_inc(v_size_3613_);
lean_dec(v_t_3598_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3877_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; uint8_t v___y_3671_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v_fst_3873_; lean_object* v_snd_3874_; uint8_t v___x_3875_; 
v_fst_3871_ = lean_ctor_get(v_k_3596_, 0);
v_snd_3872_ = lean_ctor_get(v_k_3596_, 1);
v_fst_3873_ = lean_ctor_get(v_k_3614_, 0);
v_snd_3874_ = lean_ctor_get(v_k_3614_, 1);
v___x_3875_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3871_, v_fst_3873_);
if (v___x_3875_ == 1)
{
uint8_t v___x_3876_; 
v___x_3876_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3872_, v_snd_3874_);
v___y_3671_ = v___x_3876_;
goto v___jp_3670_;
}
else
{
v___y_3671_ = v___x_3875_;
goto v___jp_3670_;
}
v___jp_3621_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_nat_add(v___y_3623_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec(v___y_3623_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 3, v___y_3624_);
lean_ctor_set(v___x_3619_, 0, v___x_3629_);
v___x_3631_ = v___x_3619_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v___y_3624_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_r_3617_);
v___x_3631_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3632_, 0, v___y_3625_);
lean_ctor_set(v___x_3632_, 1, v___y_3626_);
lean_ctor_set(v___x_3632_, 2, v___y_3627_);
lean_ctor_set(v___x_3632_, 3, v___y_3622_);
lean_ctor_set(v___x_3632_, 4, v___x_3631_);
return v___x_3632_;
}
}
v___jp_3634_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_nat_add(v___y_3639_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec(v___y_3639_);
v___x_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___y_3638_);
lean_ctor_set(v___x_3648_, 2, v___y_3642_);
lean_ctor_set(v___x_3648_, 3, v___y_3643_);
lean_ctor_set(v___x_3648_, 4, v___y_3645_);
v___x_3649_ = lean_nat_add(v___y_3636_, v___y_3644_);
lean_dec(v___y_3644_);
if (lean_obj_tag(v___y_3635_) == 0)
{
lean_object* v_size_3650_; 
v_size_3650_ = lean_ctor_get(v___y_3635_, 0);
lean_inc(v_size_3650_);
v___y_3622_ = v___x_3648_;
v___y_3623_ = v___x_3649_;
v___y_3624_ = v___y_3635_;
v___y_3625_ = v___y_3637_;
v___y_3626_ = v___y_3640_;
v___y_3627_ = v___y_3641_;
v___y_3628_ = v_size_3650_;
goto v___jp_3621_;
}
else
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_unsigned_to_nat(0u);
v___y_3622_ = v___x_3648_;
v___y_3623_ = v___x_3649_;
v___y_3624_ = v___y_3635_;
v___y_3625_ = v___y_3637_;
v___y_3626_ = v___y_3640_;
v___y_3627_ = v___y_3641_;
v___y_3628_ = v___x_3651_;
goto v___jp_3621_;
}
}
v___jp_3652_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_nat_add(v___y_3655_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec(v___y_3655_);
v___x_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v_k_3614_);
lean_ctor_set(v___x_3666_, 2, v_v_3615_);
lean_ctor_set(v___x_3666_, 3, v_l_3616_);
lean_ctor_set(v___x_3666_, 4, v___y_3654_);
v___x_3667_ = lean_nat_add(v___y_3662_, v___y_3661_);
lean_dec(v___y_3661_);
if (lean_obj_tag(v___y_3658_) == 0)
{
lean_object* v_size_3668_; 
v_size_3668_ = lean_ctor_get(v___y_3658_, 0);
lean_inc(v_size_3668_);
v___y_3600_ = v___y_3653_;
v___y_3601_ = v___y_3657_;
v___y_3602_ = v___y_3656_;
v___y_3603_ = v___x_3666_;
v___y_3604_ = v___x_3667_;
v___y_3605_ = v___y_3658_;
v___y_3606_ = v___y_3659_;
v___y_3607_ = v___y_3660_;
v___y_3608_ = v___y_3663_;
v___y_3609_ = v_size_3668_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
v___y_3600_ = v___y_3653_;
v___y_3601_ = v___y_3657_;
v___y_3602_ = v___y_3656_;
v___y_3603_ = v___x_3666_;
v___y_3604_ = v___x_3667_;
v___y_3605_ = v___y_3658_;
v___y_3606_ = v___y_3659_;
v___y_3607_ = v___y_3660_;
v___y_3608_ = v___y_3663_;
v___y_3609_ = v___x_3669_;
goto v___jp_3599_;
}
}
v___jp_3670_:
{
switch(v___y_3671_)
{
case 0:
{
lean_object* v_impl_3672_; lean_object* v___x_3673_; 
lean_dec(v_size_3613_);
v_impl_3672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3596_, v_v_3597_, v_l_3616_);
v___x_3673_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3617_) == 0)
{
lean_object* v_size_3674_; lean_object* v_size_3675_; lean_object* v_k_3676_; lean_object* v_v_3677_; lean_object* v_l_3678_; lean_object* v_r_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_size_3674_ = lean_ctor_get(v_r_3617_, 0);
v_size_3675_ = lean_ctor_get(v_impl_3672_, 0);
lean_inc(v_size_3675_);
v_k_3676_ = lean_ctor_get(v_impl_3672_, 1);
lean_inc(v_k_3676_);
v_v_3677_ = lean_ctor_get(v_impl_3672_, 2);
lean_inc(v_v_3677_);
v_l_3678_ = lean_ctor_get(v_impl_3672_, 3);
lean_inc(v_l_3678_);
v_r_3679_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3679_);
v___x_3680_ = lean_unsigned_to_nat(3u);
v___x_3681_ = lean_nat_mul(v___x_3680_, v_size_3674_);
v___x_3682_ = lean_nat_dec_lt(v___x_3681_, v_size_3675_);
lean_dec(v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_dec(v_r_3679_);
lean_dec(v_l_3678_);
lean_dec(v_v_3677_);
lean_dec(v_k_3676_);
lean_del_object(v___x_3619_);
v___x_3683_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3684_ = lean_nat_add(v___x_3683_, v_size_3674_);
lean_dec(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_k_3614_);
lean_ctor_set(v___x_3685_, 2, v_v_3615_);
lean_ctor_set(v___x_3685_, 3, v_impl_3672_);
lean_ctor_set(v___x_3685_, 4, v_r_3617_);
return v___x_3685_;
}
else
{
lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3722_; 
v_isSharedCheck_3722_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; lean_object* v_unused_3724_; lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; 
v_unused_3723_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_impl_3672_, 2);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_impl_3672_, 1);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3727_);
v___x_3687_ = v_impl_3672_;
v_isShared_3688_ = v_isSharedCheck_3722_;
goto v_resetjp_3686_;
}
else
{
lean_dec(v_impl_3672_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3722_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_size_3689_; lean_object* v_size_3690_; lean_object* v_k_3691_; lean_object* v_v_3692_; lean_object* v_l_3693_; lean_object* v_r_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v_size_3689_ = lean_ctor_get(v_l_3678_, 0);
v_size_3690_ = lean_ctor_get(v_r_3679_, 0);
v_k_3691_ = lean_ctor_get(v_r_3679_, 1);
v_v_3692_ = lean_ctor_get(v_r_3679_, 2);
v_l_3693_ = lean_ctor_get(v_r_3679_, 3);
v_r_3694_ = lean_ctor_get(v_r_3679_, 4);
v___x_3695_ = lean_unsigned_to_nat(2u);
v___x_3696_ = lean_nat_mul(v___x_3695_, v_size_3689_);
v___x_3697_ = lean_nat_dec_lt(v_size_3690_, v___x_3696_);
lean_dec(v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_inc(v_r_3694_);
lean_inc(v_l_3693_);
lean_inc(v_v_3692_);
lean_inc(v_k_3691_);
lean_del_object(v___x_3687_);
lean_dec(v_r_3679_);
v___x_3698_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3699_ = lean_nat_add(v___x_3698_, v_size_3674_);
lean_dec(v___x_3698_);
v___x_3700_ = lean_nat_add(v___x_3673_, v_size_3689_);
if (lean_obj_tag(v_l_3693_) == 0)
{
lean_object* v_size_3701_; 
v_size_3701_ = lean_ctor_get(v_l_3693_, 0);
lean_inc(v_size_3701_);
lean_inc(v_size_3674_);
v___y_3635_ = v_r_3694_;
v___y_3636_ = v___x_3673_;
v___y_3637_ = v___x_3699_;
v___y_3638_ = v_k_3676_;
v___y_3639_ = v___x_3700_;
v___y_3640_ = v_k_3691_;
v___y_3641_ = v_v_3692_;
v___y_3642_ = v_v_3677_;
v___y_3643_ = v_l_3678_;
v___y_3644_ = v_size_3674_;
v___y_3645_ = v_l_3693_;
v___y_3646_ = v_size_3701_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3674_);
v___y_3635_ = v_r_3694_;
v___y_3636_ = v___x_3673_;
v___y_3637_ = v___x_3699_;
v___y_3638_ = v_k_3676_;
v___y_3639_ = v___x_3700_;
v___y_3640_ = v_k_3691_;
v___y_3641_ = v_v_3692_;
v___y_3642_ = v_v_3677_;
v___y_3643_ = v_l_3678_;
v___y_3644_ = v_size_3674_;
v___y_3645_ = v_l_3693_;
v___y_3646_ = v___x_3702_;
goto v___jp_3634_;
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_del_object(v___x_3619_);
v___x_3703_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3704_ = lean_nat_add(v___x_3703_, v_size_3674_);
lean_dec(v___x_3703_);
v___x_3705_ = lean_nat_add(v___x_3673_, v_size_3674_);
v___x_3706_ = lean_nat_add(v___x_3705_, v_size_3690_);
lean_dec(v___x_3705_);
lean_inc_ref(v_r_3617_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 4, v_r_3617_);
lean_ctor_set(v___x_3687_, 3, v_r_3679_);
lean_ctor_set(v___x_3687_, 2, v_v_3615_);
lean_ctor_set(v___x_3687_, 1, v_k_3614_);
lean_ctor_set(v___x_3687_, 0, v___x_3706_);
v___x_3708_ = v___x_3687_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_r_3679_);
lean_ctor_set(v_reuseFailAlloc_3721_, 4, v_r_3617_);
v___x_3708_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
v_isSharedCheck_3715_ = !lean_is_exclusive(v_r_3617_);
if (v_isSharedCheck_3715_ == 0)
{
lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; 
v_unused_3716_ = lean_ctor_get(v_r_3617_, 4);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_r_3617_, 3);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_r_3617_, 2);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_r_3617_, 1);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_r_3617_, 0);
lean_dec(v_unused_3720_);
v___x_3710_ = v_r_3617_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_dec(v_r_3617_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 4, v___x_3708_);
lean_ctor_set(v___x_3710_, 3, v_l_3678_);
lean_ctor_set(v___x_3710_, 2, v_v_3677_);
lean_ctor_set(v___x_3710_, 1, v_k_3676_);
lean_ctor_set(v___x_3710_, 0, v___x_3704_);
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_l_3678_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v___x_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3728_; 
lean_del_object(v___x_3619_);
v_l_3728_ = lean_ctor_get(v_impl_3672_, 3);
lean_inc(v_l_3728_);
if (lean_obj_tag(v_l_3728_) == 0)
{
lean_object* v_r_3729_; lean_object* v_k_3730_; lean_object* v_v_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
v_r_3729_ = lean_ctor_get(v_impl_3672_, 4);
v_k_3730_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3731_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3741_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3742_);
v___x_3733_ = v_impl_3672_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_r_3729_);
lean_inc(v_v_3731_);
lean_inc(v_k_3730_);
lean_dec(v_impl_3672_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3729_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 3, v_r_3729_);
lean_ctor_set(v___x_3733_, 2, v_v_3615_);
lean_ctor_set(v___x_3733_, 1, v_k_3614_);
lean_ctor_set(v___x_3733_, 0, v___x_3673_);
v___x_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v_r_3729_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v_r_3729_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3735_);
lean_ctor_set(v___x_3738_, 1, v_k_3730_);
lean_ctor_set(v___x_3738_, 2, v_v_3731_);
lean_ctor_set(v___x_3738_, 3, v_l_3728_);
lean_ctor_set(v___x_3738_, 4, v___x_3737_);
return v___x_3738_;
}
}
}
else
{
lean_object* v_r_3743_; 
v_r_3743_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3743_);
if (lean_obj_tag(v_r_3743_) == 0)
{
lean_object* v_k_3744_; lean_object* v_v_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3766_; 
v_k_3744_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3745_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3767_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3769_);
v___x_3747_ = v_impl_3672_;
v_isShared_3748_ = v_isSharedCheck_3766_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_v_3745_);
lean_inc(v_k_3744_);
lean_dec(v_impl_3672_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3766_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_k_3749_; lean_object* v_v_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3762_; 
v_k_3749_ = lean_ctor_get(v_r_3743_, 1);
v_v_3750_ = lean_ctor_get(v_r_3743_, 2);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_r_3743_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; 
v_unused_3763_ = lean_ctor_get(v_r_3743_, 4);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_r_3743_, 3);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_r_3743_, 0);
lean_dec(v_unused_3765_);
v___x_3752_ = v_r_3743_;
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_v_3750_);
lean_inc(v_k_3749_);
lean_dec(v_r_3743_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3762_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = lean_unsigned_to_nat(3u);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 4, v_l_3728_);
lean_ctor_set(v___x_3752_, 3, v_l_3728_);
lean_ctor_set(v___x_3752_, 2, v_v_3745_);
lean_ctor_set(v___x_3752_, 1, v_k_3744_);
lean_ctor_set(v___x_3752_, 0, v___x_3673_);
v___x_3756_ = v___x_3752_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3728_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_l_3728_);
v___x_3756_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 4, v_l_3728_);
lean_ctor_set(v___x_3747_, 2, v_v_3615_);
lean_ctor_set(v___x_3747_, 1, v_k_3614_);
lean_ctor_set(v___x_3747_, 0, v___x_3673_);
v___x_3758_ = v___x_3747_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_l_3728_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_l_3728_);
v___x_3758_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3754_);
lean_ctor_set(v___x_3759_, 1, v_k_3749_);
lean_ctor_set(v___x_3759_, 2, v_v_3750_);
lean_ctor_set(v___x_3759_, 3, v___x_3756_);
lean_ctor_set(v___x_3759_, 4, v___x_3758_);
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_unsigned_to_nat(2u);
v___x_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v_k_3614_);
lean_ctor_set(v___x_3771_, 2, v_v_3615_);
lean_ctor_set(v___x_3771_, 3, v_impl_3672_);
lean_ctor_set(v___x_3771_, 4, v_r_3743_);
return v___x_3771_;
}
}
}
}
case 1:
{
lean_object* v___x_3772_; 
lean_del_object(v___x_3619_);
lean_dec(v_v_3615_);
lean_dec(v_k_3614_);
v___x_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3772_, 0, v_size_3613_);
lean_ctor_set(v___x_3772_, 1, v_k_3596_);
lean_ctor_set(v___x_3772_, 2, v_v_3597_);
lean_ctor_set(v___x_3772_, 3, v_l_3616_);
lean_ctor_set(v___x_3772_, 4, v_r_3617_);
return v___x_3772_;
}
default: 
{
lean_object* v_impl_3773_; lean_object* v___x_3774_; 
lean_del_object(v___x_3619_);
lean_dec(v_size_3613_);
v_impl_3773_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3596_, v_v_3597_, v_r_3617_);
v___x_3774_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3616_) == 0)
{
lean_object* v_size_3775_; lean_object* v_size_3776_; lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v_l_3779_; lean_object* v_r_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_size_3775_ = lean_ctor_get(v_l_3616_, 0);
v_size_3776_ = lean_ctor_get(v_impl_3773_, 0);
lean_inc(v_size_3776_);
v_k_3777_ = lean_ctor_get(v_impl_3773_, 1);
lean_inc(v_k_3777_);
v_v_3778_ = lean_ctor_get(v_impl_3773_, 2);
lean_inc(v_v_3778_);
v_l_3779_ = lean_ctor_get(v_impl_3773_, 3);
lean_inc(v_l_3779_);
v_r_3780_ = lean_ctor_get(v_impl_3773_, 4);
lean_inc(v_r_3780_);
v___x_3781_ = lean_unsigned_to_nat(3u);
v___x_3782_ = lean_nat_mul(v___x_3781_, v_size_3775_);
v___x_3783_ = lean_nat_dec_lt(v___x_3782_, v_size_3776_);
lean_dec(v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec(v_r_3780_);
lean_dec(v_l_3779_);
lean_dec(v_v_3778_);
lean_dec(v_k_3777_);
v___x_3784_ = lean_nat_add(v___x_3774_, v_size_3775_);
v___x_3785_ = lean_nat_add(v___x_3784_, v_size_3776_);
lean_dec(v_size_3776_);
lean_dec(v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v_k_3614_);
lean_ctor_set(v___x_3786_, 2, v_v_3615_);
lean_ctor_set(v___x_3786_, 3, v_l_3616_);
lean_ctor_set(v___x_3786_, 4, v_impl_3773_);
return v___x_3786_;
}
else
{
lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3821_; 
v_isSharedCheck_3821_ = !lean_is_exclusive(v_impl_3773_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; lean_object* v_unused_3823_; lean_object* v_unused_3824_; lean_object* v_unused_3825_; lean_object* v_unused_3826_; 
v_unused_3822_ = lean_ctor_get(v_impl_3773_, 4);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_impl_3773_, 3);
lean_dec(v_unused_3823_);
v_unused_3824_ = lean_ctor_get(v_impl_3773_, 2);
lean_dec(v_unused_3824_);
v_unused_3825_ = lean_ctor_get(v_impl_3773_, 1);
lean_dec(v_unused_3825_);
v_unused_3826_ = lean_ctor_get(v_impl_3773_, 0);
lean_dec(v_unused_3826_);
v___x_3788_ = v_impl_3773_;
v_isShared_3789_ = v_isSharedCheck_3821_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v_impl_3773_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3821_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_size_3790_; lean_object* v_k_3791_; lean_object* v_v_3792_; lean_object* v_l_3793_; lean_object* v_r_3794_; lean_object* v_size_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_size_3790_ = lean_ctor_get(v_l_3779_, 0);
v_k_3791_ = lean_ctor_get(v_l_3779_, 1);
v_v_3792_ = lean_ctor_get(v_l_3779_, 2);
v_l_3793_ = lean_ctor_get(v_l_3779_, 3);
v_r_3794_ = lean_ctor_get(v_l_3779_, 4);
v_size_3795_ = lean_ctor_get(v_r_3780_, 0);
v___x_3796_ = lean_unsigned_to_nat(2u);
v___x_3797_ = lean_nat_mul(v___x_3796_, v_size_3795_);
v___x_3798_ = lean_nat_dec_lt(v_size_3790_, v___x_3797_);
lean_dec(v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_inc(v_size_3795_);
lean_inc(v_r_3794_);
lean_inc(v_l_3793_);
lean_inc(v_v_3792_);
lean_inc(v_k_3791_);
lean_del_object(v___x_3788_);
lean_dec(v_l_3779_);
v___x_3799_ = lean_nat_add(v___x_3774_, v_size_3775_);
v___x_3800_ = lean_nat_add(v___x_3799_, v_size_3776_);
lean_dec(v_size_3776_);
if (lean_obj_tag(v_l_3793_) == 0)
{
lean_object* v_size_3801_; 
v_size_3801_ = lean_ctor_get(v_l_3793_, 0);
lean_inc(v_size_3801_);
v___y_3653_ = v_v_3792_;
v___y_3654_ = v_l_3793_;
v___y_3655_ = v___x_3799_;
v___y_3656_ = v_k_3777_;
v___y_3657_ = v_r_3780_;
v___y_3658_ = v_r_3794_;
v___y_3659_ = v___x_3800_;
v___y_3660_ = v_k_3791_;
v___y_3661_ = v_size_3795_;
v___y_3662_ = v___x_3774_;
v___y_3663_ = v_v_3778_;
v___y_3664_ = v_size_3801_;
goto v___jp_3652_;
}
else
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_unsigned_to_nat(0u);
v___y_3653_ = v_v_3792_;
v___y_3654_ = v_l_3793_;
v___y_3655_ = v___x_3799_;
v___y_3656_ = v_k_3777_;
v___y_3657_ = v_r_3780_;
v___y_3658_ = v_r_3794_;
v___y_3659_ = v___x_3800_;
v___y_3660_ = v_k_3791_;
v___y_3661_ = v_size_3795_;
v___y_3662_ = v___x_3774_;
v___y_3663_ = v_v_3778_;
v___y_3664_ = v___x_3802_;
goto v___jp_3652_;
}
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3803_ = lean_nat_add(v___x_3774_, v_size_3775_);
v___x_3804_ = lean_nat_add(v___x_3803_, v_size_3776_);
lean_dec(v_size_3776_);
v___x_3805_ = lean_nat_add(v___x_3803_, v_size_3790_);
lean_dec(v___x_3803_);
lean_inc_ref(v_l_3616_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 4, v_l_3779_);
lean_ctor_set(v___x_3788_, 3, v_l_3616_);
lean_ctor_set(v___x_3788_, 2, v_v_3615_);
lean_ctor_set(v___x_3788_, 1, v_k_3614_);
lean_ctor_set(v___x_3788_, 0, v___x_3805_);
v___x_3807_ = v___x_3788_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_l_3616_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_l_3779_);
v___x_3807_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
v_isSharedCheck_3814_ = !lean_is_exclusive(v_l_3616_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; 
v_unused_3815_ = lean_ctor_get(v_l_3616_, 4);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_l_3616_, 3);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_l_3616_, 2);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_l_3616_, 1);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_l_3616_, 0);
lean_dec(v_unused_3819_);
v___x_3809_ = v_l_3616_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v_l_3616_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 4, v_r_3780_);
lean_ctor_set(v___x_3809_, 3, v___x_3807_);
lean_ctor_set(v___x_3809_, 2, v_v_3778_);
lean_ctor_set(v___x_3809_, 1, v_k_3777_);
lean_ctor_set(v___x_3809_, 0, v___x_3804_);
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3780_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3827_; 
v_l_3827_ = lean_ctor_get(v_impl_3773_, 3);
lean_inc(v_l_3827_);
if (lean_obj_tag(v_l_3827_) == 0)
{
lean_object* v_r_3828_; lean_object* v_k_3829_; lean_object* v_v_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3851_; 
v_r_3828_ = lean_ctor_get(v_impl_3773_, 4);
v_k_3829_ = lean_ctor_get(v_impl_3773_, 1);
v_v_3830_ = lean_ctor_get(v_impl_3773_, 2);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_impl_3773_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; lean_object* v_unused_3853_; 
v_unused_3852_ = lean_ctor_get(v_impl_3773_, 3);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_impl_3773_, 0);
lean_dec(v_unused_3853_);
v___x_3832_ = v_impl_3773_;
v_isShared_3833_ = v_isSharedCheck_3851_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_r_3828_);
lean_inc(v_v_3830_);
lean_inc(v_k_3829_);
lean_dec(v_impl_3773_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3851_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_k_3834_; lean_object* v_v_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3847_; 
v_k_3834_ = lean_ctor_get(v_l_3827_, 1);
v_v_3835_ = lean_ctor_get(v_l_3827_, 2);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_l_3827_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3848_ = lean_ctor_get(v_l_3827_, 4);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_l_3827_, 3);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_l_3827_, 0);
lean_dec(v_unused_3850_);
v___x_3837_ = v_l_3827_;
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_v_3835_);
lean_inc(v_k_3834_);
lean_dec(v_l_3827_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3839_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3828_, 2);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v_r_3828_);
lean_ctor_set(v___x_3837_, 3, v_r_3828_);
lean_ctor_set(v___x_3837_, 2, v_v_3615_);
lean_ctor_set(v___x_3837_, 1, v_k_3614_);
lean_ctor_set(v___x_3837_, 0, v___x_3774_);
v___x_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v_r_3828_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_r_3828_);
v___x_3841_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3843_; 
lean_inc(v_r_3828_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 3, v_r_3828_);
lean_ctor_set(v___x_3832_, 0, v___x_3774_);
v___x_3843_ = v___x_3832_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_k_3829_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_v_3830_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_r_3828_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_r_3828_);
v___x_3843_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3839_);
lean_ctor_set(v___x_3844_, 1, v_k_3834_);
lean_ctor_set(v___x_3844_, 2, v_v_3835_);
lean_ctor_set(v___x_3844_, 3, v___x_3841_);
lean_ctor_set(v___x_3844_, 4, v___x_3843_);
return v___x_3844_;
}
}
}
}
}
else
{
lean_object* v_r_3854_; 
v_r_3854_ = lean_ctor_get(v_impl_3773_, 4);
lean_inc(v_r_3854_);
if (lean_obj_tag(v_r_3854_) == 0)
{
lean_object* v_k_3855_; lean_object* v_v_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3865_; 
v_k_3855_ = lean_ctor_get(v_impl_3773_, 1);
v_v_3856_ = lean_ctor_get(v_impl_3773_, 2);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_impl_3773_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; lean_object* v_unused_3867_; lean_object* v_unused_3868_; 
v_unused_3866_ = lean_ctor_get(v_impl_3773_, 4);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_impl_3773_, 3);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_impl_3773_, 0);
lean_dec(v_unused_3868_);
v___x_3858_ = v_impl_3773_;
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_v_3856_);
lean_inc(v_k_3855_);
lean_dec(v_impl_3773_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3860_ = lean_unsigned_to_nat(3u);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 4, v_l_3827_);
lean_ctor_set(v___x_3858_, 2, v_v_3615_);
lean_ctor_set(v___x_3858_, 1, v_k_3614_);
lean_ctor_set(v___x_3858_, 0, v___x_3774_);
v___x_3862_ = v___x_3858_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_l_3827_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_l_3827_);
v___x_3862_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3860_);
lean_ctor_set(v___x_3863_, 1, v_k_3855_);
lean_ctor_set(v___x_3863_, 2, v_v_3856_);
lean_ctor_set(v___x_3863_, 3, v___x_3862_);
lean_ctor_set(v___x_3863_, 4, v_r_3854_);
return v___x_3863_;
}
}
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_unsigned_to_nat(2u);
v___x_3870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v_k_3614_);
lean_ctor_set(v___x_3870_, 2, v_v_3615_);
lean_ctor_set(v___x_3870_, 3, v_r_3854_);
lean_ctor_set(v___x_3870_, 4, v_impl_3773_);
return v___x_3870_;
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
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v_k_3596_);
lean_ctor_set(v___x_3879_, 2, v_v_3597_);
lean_ctor_set(v___x_3879_, 3, v_t_3598_);
lean_ctor_set(v___x_3879_, 4, v_t_3598_);
return v___x_3879_;
}
v___jp_3599_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = lean_nat_add(v___y_3604_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec(v___y_3604_);
v___x_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v___y_3602_);
lean_ctor_set(v___x_3611_, 2, v___y_3608_);
lean_ctor_set(v___x_3611_, 3, v___y_3605_);
lean_ctor_set(v___x_3611_, 4, v___y_3601_);
v___x_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3612_, 0, v___y_3606_);
lean_ctor_set(v___x_3612_, 1, v___y_3607_);
lean_ctor_set(v___x_3612_, 2, v___y_3600_);
lean_ctor_set(v___x_3612_, 3, v___y_3603_);
lean_ctor_set(v___x_3612_, 4, v___x_3611_);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_3880_, lean_object* v_k_3881_, lean_object* v_fallback_3882_){
_start:
{
if (lean_obj_tag(v_t_3880_) == 0)
{
lean_object* v_k_3883_; lean_object* v_v_3884_; lean_object* v_l_3885_; lean_object* v_r_3886_; uint8_t v___y_3888_; lean_object* v_fst_3891_; lean_object* v_snd_3892_; lean_object* v_fst_3893_; lean_object* v_snd_3894_; uint8_t v___x_3895_; 
v_k_3883_ = lean_ctor_get(v_t_3880_, 1);
v_v_3884_ = lean_ctor_get(v_t_3880_, 2);
v_l_3885_ = lean_ctor_get(v_t_3880_, 3);
v_r_3886_ = lean_ctor_get(v_t_3880_, 4);
v_fst_3891_ = lean_ctor_get(v_k_3881_, 0);
v_snd_3892_ = lean_ctor_get(v_k_3881_, 1);
v_fst_3893_ = lean_ctor_get(v_k_3883_, 0);
v_snd_3894_ = lean_ctor_get(v_k_3883_, 1);
v___x_3895_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3891_, v_fst_3893_);
if (v___x_3895_ == 1)
{
uint8_t v___x_3896_; 
v___x_3896_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3892_, v_snd_3894_);
v___y_3888_ = v___x_3896_;
goto v___jp_3887_;
}
else
{
v___y_3888_ = v___x_3895_;
goto v___jp_3887_;
}
v___jp_3887_:
{
switch(v___y_3888_)
{
case 0:
{
v_t_3880_ = v_l_3885_;
goto _start;
}
case 1:
{
lean_inc(v_v_3884_);
return v_v_3884_;
}
default: 
{
v_t_3880_ = v_r_3886_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_3882_);
return v_fallback_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_3897_, lean_object* v_k_3898_, lean_object* v_fallback_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_3897_, v_k_3898_, v_fallback_3899_);
lean_dec(v_fallback_3899_);
lean_dec_ref(v_k_3898_);
lean_dec(v_t_3897_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_3901_, lean_object* v_as_3902_, size_t v_sz_3903_, size_t v_i_3904_, lean_object* v_b_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_usize_dec_lt(v_i_3904_, v_sz_3903_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec(v___x_3901_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_b_3905_);
return v___x_3910_;
}
else
{
lean_object* v_a_3911_; lean_object* v_fst_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3940_; 
v_a_3911_ = lean_array_uget(v_as_3902_, v_i_3904_);
v_fst_3912_ = lean_ctor_get(v_a_3911_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v_a_3911_, 1);
lean_dec(v_unused_3941_);
v___x_3914_ = v_a_3911_;
v_isShared_3915_ = v_isSharedCheck_3940_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_fst_3912_);
lean_dec(v_a_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3940_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; 
lean_inc(v_fst_3912_);
v___x_3916_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3912_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___y_3920_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_3917_) == 0)
{
lean_inc(v___x_3901_);
v___y_3920_ = v___x_3901_;
goto v___jp_3919_;
}
else
{
lean_object* v_val_3931_; 
v_val_3931_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v_a_3917_, 1);
v___y_3920_ = v_val_3931_;
goto v___jp_3919_;
}
v___jp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v_fst_3912_);
lean_ctor_set(v___x_3914_, 0, v___y_3920_);
v___x_3922_ = v___x_3914_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___y_3920_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_fst_3912_);
v___x_3922_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; size_t v___x_3927_; size_t v___x_3928_; 
v___x_3923_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_3905_, v___x_3922_, v___x_3918_);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_nat_add(v___x_3923_, v___x_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_3922_, v___x_3925_, v_b_3905_);
v___x_3927_ = ((size_t)1ULL);
v___x_3928_ = lean_usize_add(v_i_3904_, v___x_3927_);
v_i_3904_ = v___x_3928_;
v_b_3905_ = v___x_3926_;
goto _start;
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_del_object(v___x_3914_);
lean_dec(v_fst_3912_);
lean_dec(v_b_3905_);
lean_dec(v___x_3901_);
v_a_3932_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3916_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3916_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_3942_, lean_object* v_as_3943_, lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
size_t v_sz_boxed_3950_; size_t v_i_boxed_3951_; lean_object* v_res_3952_; 
v_sz_boxed_3950_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3951_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_3942_, v_as_3943_, v_sz_boxed_3950_, v_i_boxed_3951_, v_b_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec_ref(v_as_3943_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_3953_, lean_object* v_init_3954_, lean_object* v_x_3955_){
_start:
{
if (lean_obj_tag(v_x_3955_) == 0)
{
lean_object* v_k_3957_; lean_object* v_v_3958_; lean_object* v_l_3959_; lean_object* v_r_3960_; lean_object* v___x_3961_; lean_object* v_a_3962_; lean_object* v_a_3963_; lean_object* v_fst_3964_; lean_object* v_snd_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3980_; 
v_k_3957_ = lean_ctor_get(v_x_3955_, 1);
lean_inc(v_k_3957_);
v_v_3958_ = lean_ctor_get(v_x_3955_, 2);
lean_inc(v_v_3958_);
v_l_3959_ = lean_ctor_get(v_x_3955_, 3);
lean_inc(v_l_3959_);
v_r_3960_ = lean_ctor_get(v_x_3955_, 4);
lean_inc(v_r_3960_);
lean_dec_ref_known(v_x_3955_, 5);
lean_inc_ref(v_fst_3953_);
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_3953_, v_init_3954_, v_l_3959_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
v_a_3963_ = lean_ctor_get(v_a_3962_, 0);
lean_inc(v_a_3963_);
lean_dec(v_a_3962_);
v_fst_3964_ = lean_ctor_get(v_k_3957_, 0);
v_snd_3965_ = lean_ctor_get(v_k_3957_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_k_3957_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3967_ = v_k_3957_;
v_isShared_3968_ = v_isSharedCheck_3980_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_snd_3965_);
lean_inc(v_fst_3964_);
lean_dec(v_k_3957_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3980_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v_optName_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v_optName_3969_ = lean_ctor_get(v_fst_3953_, 1);
v___x_3970_ = 1;
lean_inc(v_optName_3969_);
v___x_3971_ = l_Lean_Name_toString(v_optName_3969_, v___x_3970_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set_tag(v___x_3967_, 1);
v___x_3973_ = v___x_3967_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_fst_3964_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_snd_3965_);
v___x_3973_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
double v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = lean_float_of_nat(v_v_3958_);
v___x_3975_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_3975_, 0, v___x_3974_);
v___x_3976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3971_);
lean_ctor_set(v___x_3976_, 1, v___x_3973_);
lean_ctor_set(v___x_3976_, 2, v___x_3975_);
v___x_3977_ = lean_array_push(v_a_3963_, v___x_3976_);
v_init_3954_ = v___x_3977_;
v_x_3955_ = v_r_3960_;
goto _start;
}
}
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec_ref(v_fst_3953_);
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v_init_3954_);
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_3983_, lean_object* v_init_3984_, lean_object* v_x_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_3983_, v_init_3984_, v_x_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_3988_, lean_object* v_as_3989_, size_t v_sz_3990_, size_t v_i_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_a_3997_; uint8_t v___x_4001_; 
v___x_4001_ = lean_usize_dec_lt(v_i_3991_, v_sz_3990_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; 
lean_dec(v___x_3988_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v_b_3992_);
return v___x_4002_;
}
else
{
lean_object* v_a_4003_; lean_object* v_snd_4004_; lean_object* v_fst_4005_; lean_object* v_size_4006_; lean_object* v_buckets_4007_; lean_object* v___x_4008_; lean_object* v___y_4010_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v_a_4003_ = lean_array_uget_borrowed(v_as_3989_, v_i_3991_);
v_snd_4004_ = lean_ctor_get(v_a_4003_, 1);
v_fst_4005_ = lean_ctor_get(v_a_4003_, 0);
v_size_4006_ = lean_ctor_get(v_snd_4004_, 0);
v_buckets_4007_ = lean_ctor_get(v_snd_4004_, 1);
v___x_4008_ = lean_box(1);
v___x_4044_ = lean_mk_empty_array_with_capacity(v_size_4006_);
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = lean_array_get_size(v_buckets_4007_);
v___x_4047_ = lean_nat_dec_lt(v___x_4045_, v___x_4046_);
if (v___x_4047_ == 0)
{
v___y_4010_ = v___x_4044_;
goto v___jp_4009_;
}
else
{
uint8_t v___x_4048_; 
v___x_4048_ = lean_nat_dec_le(v___x_4046_, v___x_4046_);
if (v___x_4048_ == 0)
{
if (v___x_4047_ == 0)
{
v___y_4010_ = v___x_4044_;
goto v___jp_4009_;
}
else
{
size_t v___x_4049_; size_t v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = ((size_t)0ULL);
v___x_4050_ = lean_usize_of_nat(v___x_4046_);
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4007_, v___x_4049_, v___x_4050_, v___x_4044_);
v___y_4010_ = v___x_4051_;
goto v___jp_4009_;
}
}
else
{
size_t v___x_4052_; size_t v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = ((size_t)0ULL);
v___x_4053_ = lean_usize_of_nat(v___x_4046_);
v___x_4054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4007_, v___x_4052_, v___x_4053_, v___x_4044_);
v___y_4010_ = v___x_4054_;
goto v___jp_4009_;
}
}
v___jp_4009_:
{
size_t v_sz_4011_; size_t v___x_4012_; lean_object* v___x_4013_; 
v_sz_4011_ = lean_array_size(v___y_4010_);
v___x_4012_ = ((size_t)0ULL);
lean_inc(v___x_3988_);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_3988_, v___y_4010_, v_sz_4011_, v___x_4012_, v___x_4008_, v___y_3993_, v___y_3994_);
lean_dec_ref(v___y_4010_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
lean_inc(v_fst_4005_);
v___x_4015_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4005_, v_b_3992_, v_a_4014_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v_a_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v_a_4017_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_a_4017_);
lean_dec(v_a_4016_);
v_a_3997_ = v_a_4017_;
goto v___jp_3996_;
}
else
{
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4027_; 
v_a_4018_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4020_ = v___x_4015_;
v_isShared_4021_ = v_isSharedCheck_4027_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4015_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4027_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
if (lean_obj_tag(v_a_4018_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; 
lean_dec(v___x_3988_);
v_a_4022_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v_a_4018_, 1);
if (v_isShared_4021_ == 0)
{
lean_ctor_set_tag(v___x_4020_, 0);
lean_ctor_set(v___x_4020_, 0, v_a_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
else
{
lean_object* v_a_4026_; 
lean_del_object(v___x_4020_);
v_a_4026_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v_a_4018_, 1);
v_a_3997_ = v_a_4026_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v___x_3988_);
v_a_4028_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4015_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4015_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec_ref(v_b_3992_);
lean_dec(v___x_3988_);
v_a_4036_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4013_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4013_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
}
v___jp_3996_:
{
size_t v___x_3998_; size_t v___x_3999_; 
v___x_3998_ = ((size_t)1ULL);
v___x_3999_ = lean_usize_add(v_i_3991_, v___x_3998_);
v_i_3991_ = v___x_3999_;
v_b_3992_ = v_a_3997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4055_, lean_object* v_as_4056_, lean_object* v_sz_4057_, lean_object* v_i_4058_, lean_object* v_b_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
size_t v_sz_boxed_4063_; size_t v_i_boxed_4064_; lean_object* v_res_4065_; 
v_sz_boxed_4063_ = lean_unbox_usize(v_sz_4057_);
lean_dec(v_sz_4057_);
v_i_boxed_4064_ = lean_unbox_usize(v_i_4058_);
lean_dec(v_i_4058_);
v_res_4065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4055_, v_as_4056_, v_sz_boxed_4063_, v_i_boxed_4064_, v_b_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec_ref(v_as_4056_);
return v_res_4065_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = l_Lean_maxRecDepth;
v___x_4073_ = l_Lean_Options_empty;
v___x_4074_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4073_, v___x_4072_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4075_, lean_object* v_linterOpts_4076_, lean_object* v_sp_4077_, lean_object* v_env_4078_, lean_object* v_mod_4079_){
_start:
{
lean_object* v_msg_4082_; lean_object* v_a_4087_; lean_object* v_a_4091_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v_a_4122_; lean_object* v___y_4126_; lean_object* v___y_4129_; uint8_t v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; uint8_t v___y_4136_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_env_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; lean_object* v___y_4216_; uint8_t v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; uint8_t v___y_4221_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v_fileName_4264_; lean_object* v_fileMap_4265_; lean_object* v_currRecDepth_4266_; lean_object* v_ref_4267_; lean_object* v_currNamespace_4268_; lean_object* v_openDecls_4269_; lean_object* v_initHeartbeats_4270_; lean_object* v_maxHeartbeats_4271_; lean_object* v_quotContext_4272_; lean_object* v_currMacroScope_4273_; lean_object* v_cancelTk_x3f_4274_; uint8_t v_suppressElabErrors_4275_; lean_object* v_inheritedTraceOptions_4276_; lean_object* v___y_4277_; uint8_t v___y_4293_; uint8_t v___x_4313_; 
v___x_4105_ = lean_unsigned_to_nat(0u);
v___x_4106_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4107_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4108_ = lean_io_get_num_heartbeats();
v___x_4109_ = l_Lean_firstFrontendMacroScope;
v___x_4110_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4111_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_box(0);
v___x_4114_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4115_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4116_ = 1;
v___x_4117_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4118_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4119_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4119_, 0, v_env_4078_);
lean_ctor_set(v___x_4119_, 1, v___x_4110_);
lean_ctor_set(v___x_4119_, 2, v___x_4111_);
lean_ctor_set(v___x_4119_, 3, v___x_4114_);
lean_ctor_set(v___x_4119_, 4, v___x_4115_);
lean_ctor_set(v___x_4119_, 5, v___x_4106_);
lean_ctor_set(v___x_4119_, 6, v___x_4107_);
lean_ctor_set(v___x_4119_, 7, v___x_4117_);
lean_ctor_set(v___x_4119_, 8, v___x_4118_);
v___x_4120_ = lean_st_mk_ref(v___x_4119_);
v___x_4205_ = l_Lean_inheritedTraceOptions;
v___x_4206_ = lean_st_ref_get(v___x_4205_);
v___x_4207_ = lean_st_ref_get(v___x_4120_);
v_env_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc_ref(v_env_4208_);
lean_dec(v___x_4207_);
v___x_4209_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4210_ = l_Lean_instInhabitedFileMap_default;
v___x_4211_ = l_Lean_Options_empty;
v___x_4212_ = lean_box(0);
v___x_4213_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4214_ = 0;
v___x_4260_ = lean_box(0);
v___x_4261_ = l_Lean_Name_getRoot(v_mod_4079_);
v___x_4262_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4313_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4208_);
lean_dec_ref(v_env_4208_);
if (v___x_4313_ == 0)
{
if (v___x_4262_ == 0)
{
lean_inc(v___x_4120_);
v_fileName_4264_ = v___x_4209_;
v_fileMap_4265_ = v___x_4210_;
v_currRecDepth_4266_ = v___x_4105_;
v_ref_4267_ = v___x_4212_;
v_currNamespace_4268_ = v___x_4112_;
v_openDecls_4269_ = v___x_4113_;
v_initHeartbeats_4270_ = v___x_4108_;
v_maxHeartbeats_4271_ = v___x_4213_;
v_quotContext_4272_ = v___x_4112_;
v_currMacroScope_4273_ = v___x_4109_;
v_cancelTk_x3f_4274_ = v___x_4260_;
v_suppressElabErrors_4275_ = v___x_4214_;
v_inheritedTraceOptions_4276_ = v___x_4206_;
v___y_4277_ = v___x_4120_;
goto v___jp_4263_;
}
else
{
v___y_4293_ = v___x_4313_;
goto v___jp_4292_;
}
}
else
{
v___y_4293_ = v___x_4262_;
goto v___jp_4292_;
}
v___jp_4081_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4083_ = l_Lean_MessageData_toString(v_msg_4082_);
v___x_4084_ = lean_mk_io_user_error(v___x_4083_);
v___x_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
v___jp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_mk_io_user_error(v_a_4087_);
v___x_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
v___jp_4090_:
{
if (lean_obj_tag(v_a_4091_) == 0)
{
lean_object* v_msg_4092_; 
v_msg_4092_ = lean_ctor_get(v_a_4091_, 1);
lean_inc_ref(v_msg_4092_);
lean_dec_ref_known(v_a_4091_, 2);
v_msg_4082_ = v_msg_4092_;
goto v___jp_4081_;
}
else
{
lean_object* v_id_4093_; lean_object* v___x_4094_; 
v_id_4093_ = lean_ctor_get(v_a_4091_, 0);
lean_inc(v_id_4093_);
lean_dec_ref_known(v_a_4091_, 2);
v___x_4094_ = l_Lean_InternalExceptionId_getName(v_id_4093_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec(v_id_4093_);
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4097_ = 1;
v___x_4098_ = l_Lean_Name_toString(v_a_4095_, v___x_4097_);
v___x_4099_ = lean_string_append(v___x_4096_, v___x_4098_);
lean_dec_ref(v___x_4098_);
v_a_4087_ = v___x_4099_;
goto v___jp_4086_;
}
else
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_dec_ref_known(v___x_4094_, 1);
v___x_4100_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4101_ = l_Nat_reprFast(v_id_4093_);
v___x_4102_ = lean_string_append(v___x_4100_, v___x_4101_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4104_ = lean_string_append(v___x_4102_, v___x_4103_);
v_a_4087_ = v___x_4104_;
goto v___jp_4086_;
}
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_st_ref_get(v___x_4120_);
lean_dec(v___x_4120_);
lean_dec(v___x_4123_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4122_);
return v___x_4124_;
}
v___jp_4125_:
{
lean_object* v_a_4127_; 
v_a_4127_ = lean_ctor_get(v___y_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___y_4126_);
v_a_4122_ = v_a_4127_;
goto v___jp_4121_;
}
v___jp_4128_:
{
switch(v___y_4131_)
{
case 0:
{
lean_dec(v_sp_4077_);
if (v___y_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec_ref(v___y_4135_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v___y_4129_);
v___x_4137_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4079_, v___x_4116_);
v___x_4139_ = lean_string_append(v___x_4137_, v___x_4138_);
lean_dec_ref(v___x_4138_);
v___x_4140_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4141_ = lean_string_append(v___x_4139_, v___x_4140_);
v___x_4142_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4141_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4136_, v_a_4143_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
v___y_4126_ = v___x_4144_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___x_4120_);
v_a_4145_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4147_ = v___x_4142_;
v_isShared_4148_ = v_isSharedCheck_4154_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4142_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4154_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4149_ = lean_io_error_to_string(v_a_4145_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 3);
lean_ctor_set(v___x_4147_, 0, v___x_4149_);
v___x_4151_ = v___x_4147_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_MessageData_ofFormat(v___x_4151_);
v_msg_4082_ = v___x_4152_;
goto v___jp_4081_;
}
}
}
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4155_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4156_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4079_, v___y_4136_);
v___x_4157_ = lean_string_append(v___x_4155_, v___x_4156_);
lean_dec_ref(v___x_4156_);
v___x_4158_ = lean_array_get_size(v___y_4129_);
lean_dec_ref(v___y_4129_);
v___x_4159_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4135_, v___y_4132_, v___x_4116_, v___x_4157_, v___x_4158_, v___x_4116_, v___y_4133_, v___y_4134_);
lean_dec_ref(v___y_4132_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_MessageData_toString(v_a_4160_);
v___x_4162_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4161_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4136_, v_a_4163_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
v___y_4126_ = v___x_4164_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4174_; 
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___x_4120_);
v_a_4165_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4167_ = v___x_4162_;
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4162_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4169_ = lean_io_error_to_string(v_a_4165_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 3);
lean_ctor_set(v___x_4167_, 0, v___x_4169_);
v___x_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_MessageData_ofFormat(v___x_4171_);
v_msg_4082_ = v___x_4172_;
goto v___jp_4081_;
}
}
}
}
else
{
lean_object* v_a_4175_; 
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___x_4120_);
v_a_4175_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4159_, 1);
v_a_4091_ = v_a_4175_;
goto v___jp_4090_;
}
}
}
case 1:
{
lean_object* v___x_4176_; lean_object* v_env_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; size_t v_sz_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v___y_4132_);
lean_dec_ref(v___y_4129_);
lean_dec(v_mod_4079_);
v___x_4176_ = lean_st_ref_get(v___y_4134_);
v_env_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc_ref(v_env_4177_);
lean_dec(v___x_4176_);
v___x_4178_ = l_Lean_Environment_mainModule(v_env_4177_);
lean_dec_ref(v_env_4177_);
v___x_4179_ = lean_box(v___y_4130_);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4118_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v_sz_4181_ = lean_array_size(v___y_4135_);
v___x_4182_ = ((size_t)0ULL);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4077_, v___x_4178_, v___y_4135_, v_sz_4181_, v___x_4182_, v___x_4180_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec_ref(v___y_4135_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v_fst_4185_; lean_object* v_snd_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v_fst_4185_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_fst_4185_);
v_snd_4186_ = lean_ctor_get(v_a_4184_, 1);
lean_inc(v_snd_4186_);
lean_dec(v_a_4184_);
v___x_4187_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4187_, 0, v_fst_4185_);
v___x_4188_ = lean_unbox(v_snd_4186_);
lean_dec(v_snd_4186_);
lean_ctor_set_uint8(v___x_4187_, sizeof(void*)*1, v___x_4188_);
v_a_4122_ = v___x_4187_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4189_; 
lean_dec(v___x_4120_);
v_a_4189_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4183_, 1);
v_a_4091_ = v_a_4189_;
goto v___jp_4090_;
}
}
default: 
{
lean_object* v___x_4190_; lean_object* v_env_4191_; lean_object* v___x_4192_; size_t v_sz_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
lean_dec_ref(v___y_4132_);
lean_dec_ref(v___y_4129_);
lean_dec(v_mod_4079_);
lean_dec(v_sp_4077_);
v___x_4190_ = lean_st_ref_get(v___y_4134_);
v_env_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc_ref(v_env_4191_);
lean_dec(v___x_4190_);
v___x_4192_ = l_Lean_Environment_mainModule(v_env_4191_);
lean_dec_ref(v_env_4191_);
v_sz_4193_ = lean_array_size(v___y_4135_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4192_, v___y_4135_, v_sz_4193_, v___x_4194_, v___x_4118_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec_ref(v___y_4135_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set_tag(v___x_4198_, 2);
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v_a_4122_ = v___x_4201_;
goto v___jp_4121_;
}
}
}
else
{
lean_object* v_a_4204_; 
lean_dec(v___x_4120_);
v_a_4204_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4195_, 1);
v_a_4091_ = v_a_4204_;
goto v___jp_4090_;
}
}
}
}
v___jp_4215_:
{
if (v___y_4221_ == 0)
{
lean_object* v___x_4222_; 
lean_inc_ref(v___y_4216_);
v___x_4222_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4219_, v___y_4216_, v___y_4218_, v___y_4220_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = lean_array_get_size(v_a_4223_);
v___x_4225_ = lean_nat_dec_lt(v___x_4105_, v___x_4224_);
if (v___x_4225_ == 0)
{
v___y_4129_ = v___y_4216_;
v___y_4130_ = v___y_4221_;
v___y_4131_ = v___y_4217_;
v___y_4132_ = v___y_4219_;
v___y_4133_ = v___y_4218_;
v___y_4134_ = v___y_4220_;
v___y_4135_ = v_a_4223_;
v___y_4136_ = v___y_4221_;
goto v___jp_4128_;
}
else
{
if (v___x_4225_ == 0)
{
v___y_4129_ = v___y_4216_;
v___y_4130_ = v___y_4221_;
v___y_4131_ = v___y_4217_;
v___y_4132_ = v___y_4219_;
v___y_4133_ = v___y_4218_;
v___y_4134_ = v___y_4220_;
v___y_4135_ = v_a_4223_;
v___y_4136_ = v___y_4221_;
goto v___jp_4128_;
}
else
{
size_t v___x_4226_; size_t v___x_4227_; uint8_t v___x_4228_; 
v___x_4226_ = ((size_t)0ULL);
v___x_4227_ = lean_usize_of_nat(v___x_4224_);
v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4221_, v_a_4223_, v___x_4226_, v___x_4227_);
v___y_4129_ = v___y_4216_;
v___y_4130_ = v___y_4221_;
v___y_4131_ = v___y_4217_;
v___y_4132_ = v___y_4219_;
v___y_4133_ = v___y_4218_;
v___y_4134_ = v___y_4220_;
v___y_4135_ = v_a_4223_;
v___y_4136_ = v___x_4228_;
goto v___jp_4128_;
}
}
}
else
{
lean_object* v_a_4229_; 
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec_ref(v___y_4216_);
lean_dec(v___x_4120_);
lean_dec(v_mod_4079_);
lean_dec(v_sp_4077_);
v_a_4229_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4222_, 1);
v_a_4091_ = v_a_4229_;
goto v___jp_4090_;
}
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec_ref(v___y_4216_);
lean_dec(v_sp_4077_);
v___x_4230_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4231_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4079_, v___y_4221_);
v___x_4232_ = lean_string_append(v___x_4230_, v___x_4231_);
lean_dec_ref(v___x_4231_);
v___x_4233_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4234_ = lean_string_append(v___x_4232_, v___x_4233_);
v___x_4235_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4234_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4236_; 
lean_dec_ref_known(v___x_4235_, 1);
v___x_4236_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4122_ = v___x_4236_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v___x_4120_);
v_a_4237_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4239_ = v___x_4235_;
v_isShared_4240_ = v_isSharedCheck_4246_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4235_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4246_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4241_ = lean_io_error_to_string(v_a_4237_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set_tag(v___x_4239_, 3);
lean_ctor_set(v___x_4239_, 0, v___x_4241_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_MessageData_ofFormat(v___x_4243_);
v_msg_4082_ = v___x_4244_;
goto v___jp_4081_;
}
}
}
}
}
v___jp_4247_:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4252_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = lean_array_get_size(v_a_4254_);
v___x_4256_ = lean_nat_dec_eq(v___x_4255_, v___x_4105_);
if (v___x_4256_ == 0)
{
v___y_4216_ = v_a_4254_;
v___y_4217_ = v___y_4248_;
v___y_4218_ = v___y_4250_;
v___y_4219_ = v___y_4249_;
v___y_4220_ = v___y_4251_;
v___y_4221_ = v___x_4256_;
goto v___jp_4215_;
}
else
{
uint8_t v___x_4257_; uint8_t v___x_4258_; 
v___x_4257_ = 0;
v___x_4258_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4248_, v___x_4257_);
v___y_4216_ = v_a_4254_;
v___y_4217_ = v___y_4248_;
v___y_4218_ = v___y_4250_;
v___y_4219_ = v___y_4249_;
v___y_4220_ = v___y_4251_;
v___y_4221_ = v___x_4258_;
goto v___jp_4215_;
}
}
else
{
lean_object* v_a_4259_; 
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___x_4120_);
lean_dec(v_mod_4079_);
lean_dec(v_sp_4077_);
v_a_4259_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4253_, 1);
v_a_4091_ = v_a_4259_;
goto v___jp_4090_;
}
}
v___jp_4263_:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4261_, v___y_4277_);
lean_dec(v___x_4261_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4290_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4281_ = v___x_4278_;
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
uint8_t v_lintOnly_4283_; uint8_t v_mode_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v_lintOnly_4283_ = lean_ctor_get_uint8(v_args_4075_, sizeof(void*)*3);
v_mode_4284_ = lean_ctor_get_uint8(v_args_4075_, sizeof(void*)*3 + 1);
v___x_4285_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4273_);
lean_inc(v_quotContext_4272_);
lean_inc(v_maxHeartbeats_4271_);
lean_inc(v_openDecls_4269_);
lean_inc(v_currNamespace_4268_);
lean_inc(v_ref_4267_);
lean_inc_ref(v_fileMap_4265_);
lean_inc_ref(v_fileName_4264_);
v___x_4286_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4286_, 0, v_fileName_4264_);
lean_ctor_set(v___x_4286_, 1, v_fileMap_4265_);
lean_ctor_set(v___x_4286_, 2, v___x_4211_);
lean_ctor_set(v___x_4286_, 3, v_currRecDepth_4266_);
lean_ctor_set(v___x_4286_, 4, v___x_4285_);
lean_ctor_set(v___x_4286_, 5, v_ref_4267_);
lean_ctor_set(v___x_4286_, 6, v_currNamespace_4268_);
lean_ctor_set(v___x_4286_, 7, v_openDecls_4269_);
lean_ctor_set(v___x_4286_, 8, v_initHeartbeats_4270_);
lean_ctor_set(v___x_4286_, 9, v_maxHeartbeats_4271_);
lean_ctor_set(v___x_4286_, 10, v_quotContext_4272_);
lean_ctor_set(v___x_4286_, 11, v_currMacroScope_4273_);
lean_ctor_set(v___x_4286_, 12, v_cancelTk_x3f_4274_);
lean_ctor_set(v___x_4286_, 13, v_inheritedTraceOptions_4276_);
lean_ctor_set_uint8(v___x_4286_, sizeof(void*)*14, v___x_4262_);
lean_ctor_set_uint8(v___x_4286_, sizeof(void*)*14 + 1, v_suppressElabErrors_4275_);
if (v_lintOnly_4283_ == 0)
{
lean_del_object(v___x_4281_);
lean_dec_ref(v_linterOpts_4076_);
v___y_4248_ = v_mode_4284_;
v___y_4249_ = v_a_4279_;
v___y_4250_ = v___x_4286_;
v___y_4251_ = v___y_4277_;
v___y_4252_ = v___x_4260_;
goto v___jp_4247_;
}
else
{
lean_object* v___x_4288_; 
if (v_isShared_4282_ == 0)
{
lean_ctor_set_tag(v___x_4281_, 1);
lean_ctor_set(v___x_4281_, 0, v_linterOpts_4076_);
v___x_4288_ = v___x_4281_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_linterOpts_4076_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4248_ = v_mode_4284_;
v___y_4249_ = v_a_4279_;
v___y_4250_ = v___x_4286_;
v___y_4251_ = v___y_4277_;
v___y_4252_ = v___x_4288_;
goto v___jp_4247_;
}
}
}
}
else
{
lean_object* v_a_4291_; 
lean_dec(v___y_4277_);
lean_dec_ref(v_inheritedTraceOptions_4276_);
lean_dec(v_cancelTk_x3f_4274_);
lean_dec(v_initHeartbeats_4270_);
lean_dec(v_currRecDepth_4266_);
lean_dec(v___x_4120_);
lean_dec(v_mod_4079_);
lean_dec(v_sp_4077_);
lean_dec_ref(v_linterOpts_4076_);
v_a_4291_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4278_, 1);
v_a_4091_ = v_a_4291_;
goto v___jp_4090_;
}
}
v___jp_4292_:
{
if (v___y_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v_env_4295_; lean_object* v_nextMacroScope_4296_; lean_object* v_ngen_4297_; lean_object* v_auxDeclNGen_4298_; lean_object* v_traceState_4299_; lean_object* v_messages_4300_; lean_object* v_infoState_4301_; lean_object* v_snapshotTasks_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4311_; 
v___x_4294_ = lean_st_ref_take(v___x_4120_);
v_env_4295_ = lean_ctor_get(v___x_4294_, 0);
v_nextMacroScope_4296_ = lean_ctor_get(v___x_4294_, 1);
v_ngen_4297_ = lean_ctor_get(v___x_4294_, 2);
v_auxDeclNGen_4298_ = lean_ctor_get(v___x_4294_, 3);
v_traceState_4299_ = lean_ctor_get(v___x_4294_, 4);
v_messages_4300_ = lean_ctor_get(v___x_4294_, 6);
v_infoState_4301_ = lean_ctor_get(v___x_4294_, 7);
v_snapshotTasks_4302_ = lean_ctor_get(v___x_4294_, 8);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4311_ == 0)
{
lean_object* v_unused_4312_; 
v_unused_4312_ = lean_ctor_get(v___x_4294_, 5);
lean_dec(v_unused_4312_);
v___x_4304_ = v___x_4294_;
v_isShared_4305_ = v_isSharedCheck_4311_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_snapshotTasks_4302_);
lean_inc(v_infoState_4301_);
lean_inc(v_messages_4300_);
lean_inc(v_traceState_4299_);
lean_inc(v_auxDeclNGen_4298_);
lean_inc(v_ngen_4297_);
lean_inc(v_nextMacroScope_4296_);
lean_inc(v_env_4295_);
lean_dec(v___x_4294_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4311_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4308_; 
v___x_4306_ = l_Lean_Kernel_enableDiag(v_env_4295_, v___x_4262_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 5, v___x_4106_);
lean_ctor_set(v___x_4304_, 0, v___x_4306_);
v___x_4308_ = v___x_4304_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_nextMacroScope_4296_);
lean_ctor_set(v_reuseFailAlloc_4310_, 2, v_ngen_4297_);
lean_ctor_set(v_reuseFailAlloc_4310_, 3, v_auxDeclNGen_4298_);
lean_ctor_set(v_reuseFailAlloc_4310_, 4, v_traceState_4299_);
lean_ctor_set(v_reuseFailAlloc_4310_, 5, v___x_4106_);
lean_ctor_set(v_reuseFailAlloc_4310_, 6, v_messages_4300_);
lean_ctor_set(v_reuseFailAlloc_4310_, 7, v_infoState_4301_);
lean_ctor_set(v_reuseFailAlloc_4310_, 8, v_snapshotTasks_4302_);
v___x_4308_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_st_ref_set(v___x_4120_, v___x_4308_);
lean_inc(v___x_4120_);
v_fileName_4264_ = v___x_4209_;
v_fileMap_4265_ = v___x_4210_;
v_currRecDepth_4266_ = v___x_4105_;
v_ref_4267_ = v___x_4212_;
v_currNamespace_4268_ = v___x_4112_;
v_openDecls_4269_ = v___x_4113_;
v_initHeartbeats_4270_ = v___x_4108_;
v_maxHeartbeats_4271_ = v___x_4213_;
v_quotContext_4272_ = v___x_4112_;
v_currMacroScope_4273_ = v___x_4109_;
v_cancelTk_x3f_4274_ = v___x_4260_;
v_suppressElabErrors_4275_ = v___x_4214_;
v_inheritedTraceOptions_4276_ = v___x_4206_;
v___y_4277_ = v___x_4120_;
goto v___jp_4263_;
}
}
}
else
{
lean_inc(v___x_4120_);
v_fileName_4264_ = v___x_4209_;
v_fileMap_4265_ = v___x_4210_;
v_currRecDepth_4266_ = v___x_4105_;
v_ref_4267_ = v___x_4212_;
v_currNamespace_4268_ = v___x_4112_;
v_openDecls_4269_ = v___x_4113_;
v_initHeartbeats_4270_ = v___x_4108_;
v_maxHeartbeats_4271_ = v___x_4213_;
v_quotContext_4272_ = v___x_4112_;
v_currMacroScope_4273_ = v___x_4109_;
v_cancelTk_x3f_4274_ = v___x_4260_;
v_suppressElabErrors_4275_ = v___x_4214_;
v_inheritedTraceOptions_4276_ = v___x_4206_;
v___y_4277_ = v___x_4120_;
goto v___jp_4263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4314_, lean_object* v_linterOpts_4315_, lean_object* v_sp_4316_, lean_object* v_env_4317_, lean_object* v_mod_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4314_, v_linterOpts_4315_, v_sp_4316_, v_env_4317_, v_mod_4318_);
lean_dec_ref(v_args_4314_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4321_, lean_object* v_t_4322_, lean_object* v_k_4323_, lean_object* v_fallback_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4322_, v_k_4323_, v_fallback_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4326_, lean_object* v_t_4327_, lean_object* v_k_4328_, lean_object* v_fallback_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4326_, v_t_4327_, v_k_4328_, v_fallback_4329_);
lean_dec(v_fallback_4329_);
lean_dec_ref(v_k_4328_);
lean_dec(v_t_4327_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4331_, lean_object* v_k_4332_, lean_object* v_v_4333_, lean_object* v_t_4334_, lean_object* v_hl_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4332_, v_v_4333_, v_t_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4337_, lean_object* v_init_4338_, lean_object* v_x_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4337_, v_init_4338_, v_x_4339_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4344_, lean_object* v_init_4345_, lean_object* v_x_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4344_, v_init_4345_, v_x_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4351_, lean_object* v_constName_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4352_, v___y_4353_, v___y_4354_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4357_, lean_object* v_constName_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4357_, v_constName_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4363_, lean_object* v_ref_4364_, lean_object* v_constName_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4364_, v_constName_4365_, v___y_4366_, v___y_4367_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_ref_4371_, lean_object* v_constName_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4370_, v_ref_4371_, v_constName_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v_ref_4371_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4377_, lean_object* v_ref_4378_, lean_object* v_msg_4379_, lean_object* v_declHint_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4378_, v_msg_4379_, v_declHint_4380_, v___y_4381_, v___y_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4385_, lean_object* v_ref_4386_, lean_object* v_msg_4387_, lean_object* v_declHint_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4385_, v_ref_4386_, v_msg_4387_, v_declHint_4388_, v___y_4389_, v___y_4390_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v_ref_4386_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4393_, lean_object* v_declHint_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4393_, v_declHint_4394_, v___y_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4399_, lean_object* v_declHint_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4399_, v_declHint_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4405_, lean_object* v_ref_4406_, lean_object* v_msg_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4406_, v_msg_4407_, v___y_4408_, v___y_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4412_, lean_object* v_ref_4413_, lean_object* v_msg_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4412_, v_ref_4413_, v_msg_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v_ref_4413_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4419_, lean_object* v_msg_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4420_, v___y_4421_, v___y_4422_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4425_, lean_object* v_msg_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4425_, v_msg_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_enable_initializer_execution();
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_compacted_region_free(v_region_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4438_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4444_, lean_object* v_k_4445_, uint8_t v_v_4446_){
_start:
{
lean_object* v_map_4447_; uint8_t v_hasTrace_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4462_; 
v_map_4447_ = lean_ctor_get(v_o_4444_, 0);
v_hasTrace_4448_ = lean_ctor_get_uint8(v_o_4444_, sizeof(void*)*1);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_o_4444_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4450_ = v_o_4444_;
v_isShared_4451_ = v_isSharedCheck_4462_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_map_4447_);
lean_dec(v_o_4444_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4462_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4452_, 0, v_v_4446_);
lean_inc(v_k_4445_);
v___x_4453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4445_, v___x_4452_, v_map_4447_);
if (v_hasTrace_4448_ == 0)
{
lean_object* v___x_4454_; uint8_t v___x_4455_; lean_object* v___x_4457_; 
v___x_4454_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4455_ = l_Lean_Name_isPrefixOf(v___x_4454_, v_k_4445_);
lean_dec(v_k_4445_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4453_);
v___x_4457_ = v___x_4450_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4453_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*1, v___x_4455_);
return v___x_4457_;
}
}
else
{
lean_object* v___x_4460_; 
lean_dec(v_k_4445_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4453_);
v___x_4460_ = v___x_4450_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4453_);
lean_ctor_set_uint8(v_reuseFailAlloc_4461_, sizeof(void*)*1, v_hasTrace_4448_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4463_, lean_object* v_k_4464_, lean_object* v_v_4465_){
_start:
{
uint8_t v_v_boxed_4466_; lean_object* v_res_4467_; 
v_v_boxed_4466_ = lean_unbox(v_v_4465_);
v_res_4467_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4463_, v_k_4464_, v_v_boxed_4466_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_4468_){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; uint32_t v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4470_ = lean_unsigned_to_nat(80u);
v___x_4471_ = l_Lean_Json_pretty(v_s_4468_, v___x_4470_);
v___x_4472_ = 10;
v___x_4473_ = lean_string_push(v___x_4471_, v___x_4472_);
v___x_4474_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v_s_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_as_4478_, size_t v_sz_4479_, size_t v_i_4480_, lean_object* v_b_4481_){
_start:
{
uint8_t v___x_4483_; 
v___x_4483_ = lean_usize_dec_lt(v_i_4480_, v_sz_4479_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v_b_4481_);
return v___x_4484_;
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_a_4485_ = lean_array_uget_borrowed(v_as_4478_, v_i_4480_);
lean_inc(v_a_4485_);
v___x_4486_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4485_);
v___x_4487_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v___x_4486_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v___x_4488_; size_t v___x_4489_; size_t v___x_4490_; 
lean_dec_ref_known(v___x_4487_, 1);
v___x_4488_ = lean_box(0);
v___x_4489_ = ((size_t)1ULL);
v___x_4490_ = lean_usize_add(v_i_4480_, v___x_4489_);
v_i_4480_ = v___x_4490_;
v_b_4481_ = v___x_4488_;
goto _start;
}
else
{
return v___x_4487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_as_4492_, lean_object* v_sz_4493_, lean_object* v_i_4494_, lean_object* v_b_4495_, lean_object* v___y_4496_){
_start:
{
size_t v_sz_boxed_4497_; size_t v_i_boxed_4498_; lean_object* v_res_4499_; 
v_sz_boxed_4497_ = lean_unbox_usize(v_sz_4493_);
lean_dec(v_sz_4493_);
v_i_boxed_4498_ = lean_unbox_usize(v_i_4494_);
lean_dec(v_i_4494_);
v_res_4499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v_as_4492_, v_sz_boxed_4497_, v_i_boxed_4498_, v_b_4495_);
lean_dec_ref(v_as_4492_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_as_4500_, size_t v_i_4501_, size_t v_stop_4502_, lean_object* v_b_4503_){
_start:
{
uint8_t v___x_4504_; 
v___x_4504_ = lean_usize_dec_eq(v_i_4501_, v_stop_4502_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; lean_object* v_fst_4506_; lean_object* v_snd_4507_; uint8_t v___x_4508_; lean_object* v___x_4509_; size_t v___x_4510_; size_t v___x_4511_; 
v___x_4505_ = lean_array_uget_borrowed(v_as_4500_, v_i_4501_);
v_fst_4506_ = lean_ctor_get(v___x_4505_, 0);
v_snd_4507_ = lean_ctor_get(v___x_4505_, 1);
v___x_4508_ = lean_unbox(v_snd_4507_);
lean_inc(v_fst_4506_);
v___x_4509_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4503_, v_fst_4506_, v___x_4508_);
v___x_4510_ = ((size_t)1ULL);
v___x_4511_ = lean_usize_add(v_i_4501_, v___x_4510_);
v_i_4501_ = v___x_4511_;
v_b_4503_ = v___x_4509_;
goto _start;
}
else
{
return v_b_4503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_as_4513_, lean_object* v_i_4514_, lean_object* v_stop_4515_, lean_object* v_b_4516_){
_start:
{
size_t v_i_boxed_4517_; size_t v_stop_boxed_4518_; lean_object* v_res_4519_; 
v_i_boxed_4517_ = lean_unbox_usize(v_i_4514_);
lean_dec(v_i_4514_);
v_stop_boxed_4518_ = lean_unbox_usize(v_stop_4515_);
lean_dec(v_stop_4515_);
v_res_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_as_4513_, v_i_boxed_4517_, v_stop_boxed_4518_, v_b_4516_);
lean_dec_ref(v_as_4513_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(lean_object* v___x_4529_, lean_object* v_args_4530_, lean_object* v___x_4531_, lean_object* v_as_4532_, size_t v_sz_4533_, size_t v_i_4534_, lean_object* v_b_4535_){
_start:
{
lean_object* v_a_4538_; lean_object* v___x_4542_; uint8_t v_anyFailed_4543_; uint8_t v_anyUnlocated_4544_; lean_object* v___x_4545_; lean_object* v_envLinterModule_4546_; uint8_t v___x_4547_; 
v___x_4542_ = lean_unsigned_to_nat(0u);
v_anyFailed_4543_ = lean_nat_dec_eq(v___x_4529_, v___x_4542_);
v_anyUnlocated_4544_ = 1;
v___x_4545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__3));
v_envLinterModule_4546_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4546_, 0, v___x_4545_);
lean_ctor_set_uint8(v_envLinterModule_4546_, sizeof(void*)*1, v_anyFailed_4543_);
lean_ctor_set_uint8(v_envLinterModule_4546_, sizeof(void*)*1 + 1, v_anyUnlocated_4544_);
lean_ctor_set_uint8(v_envLinterModule_4546_, sizeof(void*)*1 + 2, v_anyFailed_4543_);
v___x_4547_ = lean_usize_dec_lt(v_i_4534_, v_sz_4533_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; 
lean_dec_ref_known(v_envLinterModule_4546_, 1);
lean_dec(v___x_4531_);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_b_4535_);
return v___x_4548_;
}
else
{
lean_object* v___x_4549_; lean_object* v_a_4550_; lean_object* v___x_4551_; 
v___x_4549_ = lean_enable_initializer_execution();
v_a_4550_ = lean_array_uget_borrowed(v_as_4532_, v_i_4534_);
lean_inc(v_a_4550_);
v___x_4551_ = l_Lean_findOLean(v_a_4550_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4553_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v___x_4553_ = l_Lean_readModuleData(v_a_4552_);
lean_dec(v_a_4552_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v_fst_4555_; lean_object* v_snd_4556_; uint8_t v___x_4557_; lean_object* v_snd_4558_; lean_object* v_snd_4559_; lean_object* v_snd_4560_; lean_object* v_fst_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4789_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v_fst_4555_ = lean_ctor_get(v_a_4554_, 0);
lean_inc(v_fst_4555_);
v_snd_4556_ = lean_ctor_get(v_a_4554_, 1);
lean_inc(v_snd_4556_);
lean_dec(v_a_4554_);
v___x_4557_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4555_);
lean_dec(v_fst_4555_);
v_snd_4558_ = lean_ctor_get(v_b_4535_, 1);
lean_inc(v_snd_4558_);
v_snd_4559_ = lean_ctor_get(v_snd_4558_, 1);
lean_inc(v_snd_4559_);
v_snd_4560_ = lean_ctor_get(v_snd_4559_, 1);
lean_inc(v_snd_4560_);
v_fst_4561_ = lean_ctor_get(v_b_4535_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_b_4535_);
if (v_isSharedCheck_4789_ == 0)
{
lean_object* v_unused_4790_; 
v_unused_4790_ = lean_ctor_get(v_b_4535_, 1);
lean_dec(v_unused_4790_);
v___x_4563_ = v_b_4535_;
v_isShared_4564_ = v_isSharedCheck_4789_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_fst_4561_);
lean_dec(v_b_4535_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4789_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v_fst_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4787_; 
v_fst_4565_ = lean_ctor_get(v_snd_4558_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_snd_4558_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; 
v_unused_4788_ = lean_ctor_get(v_snd_4558_, 1);
lean_dec(v_unused_4788_);
v___x_4567_ = v_snd_4558_;
v_isShared_4568_ = v_isSharedCheck_4787_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_fst_4565_);
lean_dec(v_snd_4558_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4787_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v_fst_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4785_; 
v_fst_4569_ = lean_ctor_get(v_snd_4559_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_snd_4559_);
if (v_isSharedCheck_4785_ == 0)
{
lean_object* v_unused_4786_; 
v_unused_4786_ = lean_ctor_get(v_snd_4559_, 1);
lean_dec(v_unused_4786_);
v___x_4571_ = v_snd_4559_;
v_isShared_4572_ = v_isSharedCheck_4785_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_fst_4569_);
lean_dec(v_snd_4559_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4785_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v_fst_4573_; lean_object* v_snd_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4784_; 
v_fst_4573_ = lean_ctor_get(v_snd_4560_, 0);
v_snd_4574_ = lean_ctor_get(v_snd_4560_, 1);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_snd_4560_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4576_ = v_snd_4560_;
v_isShared_4577_ = v_isSharedCheck_4784_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snd_4574_);
lean_inc(v_fst_4573_);
lean_dec(v_snd_4560_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4784_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___y_4579_; lean_object* v___y_4580_; uint8_t v_anyFailed_4581_; uint8_t v_anyUnlocated_4582_; lean_object* v_records_4583_; lean_object* v_codeQualityEntries_4584_; lean_object* v___y_4678_; lean_object* v___y_4679_; uint8_t v_anyFailed_4680_; uint8_t v_anyUnlocated_4681_; lean_object* v_records_4682_; lean_object* v_codeQualityEntries_4683_; lean_object* v___y_4701_; lean_object* v___y_4702_; uint8_t v___y_4743_; 
if (v___x_4557_ == 0)
{
uint8_t v___x_4782_; 
v___x_4782_ = 2;
v___y_4743_ = v___x_4782_;
goto v___jp_4742_;
}
else
{
uint8_t v___x_4783_; 
v___x_4783_ = 1;
v___y_4743_ = v___x_4783_;
goto v___jp_4742_;
}
v___jp_4578_:
{
uint8_t v_mode_4585_; uint8_t v___x_4586_; uint8_t v___x_4587_; 
v_mode_4585_ = lean_ctor_get_uint8(v_args_4530_, sizeof(void*)*3 + 1);
v___x_4586_ = 2;
v___x_4587_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4585_, v___x_4586_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = l_Lean_Name_getRoot(v_a_4550_);
lean_inc(v___x_4531_);
v___x_4589_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4530_, v___y_4580_, v___x_4531_, v___y_4579_, v___x_4588_, v_snd_4574_);
lean_dec_ref(v___y_4580_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v_outcome_4591_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref_known(v___x_4589_, 1);
v_outcome_4591_ = lean_ctor_get(v_a_4590_, 0);
if (lean_obj_tag(v_outcome_4591_) == 0)
{
uint8_t v_failed_4592_; 
v_failed_4592_ = lean_ctor_get_uint8(v_outcome_4591_, 0);
if (v_failed_4592_ == 0)
{
lean_object* v_checkedModules_4593_; lean_object* v___x_4595_; 
v_checkedModules_4593_ = lean_ctor_get(v_a_4590_, 1);
lean_inc(v_checkedModules_4593_);
lean_dec(v_a_4590_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 1, v_checkedModules_4593_);
lean_ctor_set(v___x_4576_, 0, v_codeQualityEntries_4584_);
v___x_4595_ = v___x_4576_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_codeQualityEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_checkedModules_4593_);
v___x_4595_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4597_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 1, v___x_4595_);
lean_ctor_set(v___x_4571_, 0, v_records_4583_);
v___x_4597_ = v___x_4571_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_records_4583_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4598_ = lean_box(v_anyUnlocated_4582_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4597_);
lean_ctor_set(v___x_4567_, 0, v___x_4598_);
v___x_4600_ = v___x_4567_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v___x_4597_);
v___x_4600_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4601_ = lean_box(v_anyFailed_4581_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4600_);
lean_ctor_set(v___x_4563_, 0, v___x_4601_);
v___x_4603_ = v___x_4563_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4600_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
v_a_4538_ = v___x_4603_;
goto v___jp_4537_;
}
}
}
}
}
else
{
lean_object* v_checkedModules_4608_; lean_object* v___x_4610_; 
v_checkedModules_4608_ = lean_ctor_get(v_a_4590_, 1);
lean_inc(v_checkedModules_4608_);
lean_dec(v_a_4590_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 1, v_checkedModules_4608_);
lean_ctor_set(v___x_4576_, 0, v_codeQualityEntries_4584_);
v___x_4610_ = v___x_4576_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_codeQualityEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_checkedModules_4608_);
v___x_4610_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
lean_object* v___x_4612_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 1, v___x_4610_);
lean_ctor_set(v___x_4571_, 0, v_records_4583_);
v___x_4612_ = v___x_4571_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_records_4583_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = lean_box(v_anyUnlocated_4582_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4612_);
lean_ctor_set(v___x_4567_, 0, v___x_4613_);
v___x_4615_ = v___x_4567_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4613_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v___x_4612_);
v___x_4615_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4616_ = lean_box(v_anyUnlocated_4544_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4615_);
lean_ctor_set(v___x_4563_, 0, v___x_4616_);
v___x_4618_ = v___x_4563_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___x_4615_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
v_a_4538_ = v___x_4618_;
goto v___jp_4537_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4623_; lean_object* v_records_4624_; uint8_t v_unlocated_4625_; lean_object* v___x_4626_; 
lean_inc_ref(v_outcome_4591_);
v_checkedModules_4623_ = lean_ctor_get(v_a_4590_, 1);
lean_inc(v_checkedModules_4623_);
lean_dec(v_a_4590_);
v_records_4624_ = lean_ctor_get(v_outcome_4591_, 0);
lean_inc_ref(v_records_4624_);
v_unlocated_4625_ = lean_ctor_get_uint8(v_outcome_4591_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4591_, 1);
v___x_4626_ = l_Array_append___redArg(v_records_4583_, v_records_4624_);
lean_dec_ref(v_records_4624_);
if (v_unlocated_4625_ == 0)
{
lean_object* v___x_4628_; 
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 1, v_checkedModules_4623_);
lean_ctor_set(v___x_4576_, 0, v_codeQualityEntries_4584_);
v___x_4628_ = v___x_4576_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_codeQualityEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_checkedModules_4623_);
v___x_4628_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4630_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 1, v___x_4628_);
lean_ctor_set(v___x_4571_, 0, v___x_4626_);
v___x_4630_ = v___x_4571_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v___x_4628_);
v___x_4630_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4631_ = lean_box(v_anyUnlocated_4582_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4630_);
lean_ctor_set(v___x_4567_, 0, v___x_4631_);
v___x_4633_ = v___x_4567_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4630_);
v___x_4633_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4634_ = lean_box(v_anyFailed_4581_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4633_);
lean_ctor_set(v___x_4563_, 0, v___x_4634_);
v___x_4636_ = v___x_4563_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4637_, 1, v___x_4633_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
v_a_4538_ = v___x_4636_;
goto v___jp_4537_;
}
}
}
}
}
else
{
lean_object* v___x_4642_; 
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 1, v_checkedModules_4623_);
lean_ctor_set(v___x_4576_, 0, v_codeQualityEntries_4584_);
v___x_4642_ = v___x_4576_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_codeQualityEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4654_, 1, v_checkedModules_4623_);
v___x_4642_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4644_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 1, v___x_4642_);
lean_ctor_set(v___x_4571_, 0, v___x_4626_);
v___x_4644_ = v___x_4571_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4645_ = lean_box(v_anyUnlocated_4544_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4644_);
lean_ctor_set(v___x_4567_, 0, v___x_4645_);
v___x_4647_ = v___x_4567_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4652_, 1, v___x_4644_);
v___x_4647_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4648_; lean_object* v___x_4650_; 
v___x_4648_ = lean_box(v_anyFailed_4581_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4647_);
lean_ctor_set(v___x_4563_, 0, v___x_4648_);
v___x_4650_ = v___x_4563_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v___x_4647_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
v_a_4538_ = v___x_4650_;
goto v___jp_4537_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec_ref(v_codeQualityEntries_4584_);
lean_dec_ref(v_records_4583_);
lean_del_object(v___x_4576_);
lean_del_object(v___x_4571_);
lean_del_object(v___x_4567_);
lean_del_object(v___x_4563_);
lean_dec(v___x_4531_);
v_a_4655_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4589_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4589_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v___x_4664_; 
lean_dec_ref(v___y_4580_);
lean_dec_ref(v___y_4579_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v_codeQualityEntries_4584_);
v___x_4664_ = v___x_4576_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_codeQualityEntries_4584_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_snd_4574_);
v___x_4664_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
lean_object* v___x_4666_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 1, v___x_4664_);
lean_ctor_set(v___x_4571_, 0, v_records_4583_);
v___x_4666_ = v___x_4571_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_records_4583_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4667_; lean_object* v___x_4669_; 
v___x_4667_ = lean_box(v_anyUnlocated_4582_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4666_);
lean_ctor_set(v___x_4567_, 0, v___x_4667_);
v___x_4669_ = v___x_4567_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4667_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v___x_4666_);
v___x_4669_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_box(v_anyFailed_4581_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 1, v___x_4669_);
lean_ctor_set(v___x_4563_, 0, v___x_4670_);
v___x_4672_ = v___x_4563_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4673_, 1, v___x_4669_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
v_a_4538_ = v___x_4672_;
goto v___jp_4537_;
}
}
}
}
}
}
v___jp_4677_:
{
lean_object* v___x_4684_; 
lean_inc(v_a_4550_);
lean_inc_ref(v___y_4678_);
lean_inc(v___x_4531_);
lean_inc_ref(v___y_4679_);
v___x_4684_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4530_, v___y_4679_, v___x_4531_, v___y_4678_, v_a_4550_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
switch(lean_obj_tag(v_a_4685_))
{
case 0:
{
uint8_t v_failed_4686_; 
v_failed_4686_ = lean_ctor_get_uint8(v_a_4685_, 0);
lean_dec_ref_known(v_a_4685_, 0);
if (v_failed_4686_ == 0)
{
v___y_4579_ = v___y_4678_;
v___y_4580_ = v___y_4679_;
v_anyFailed_4581_ = v_anyFailed_4680_;
v_anyUnlocated_4582_ = v_anyUnlocated_4681_;
v_records_4583_ = v_records_4682_;
v_codeQualityEntries_4584_ = v_codeQualityEntries_4683_;
goto v___jp_4578_;
}
else
{
v___y_4579_ = v___y_4678_;
v___y_4580_ = v___y_4679_;
v_anyFailed_4581_ = v_anyUnlocated_4544_;
v_anyUnlocated_4582_ = v_anyUnlocated_4681_;
v_records_4583_ = v_records_4682_;
v_codeQualityEntries_4584_ = v_codeQualityEntries_4683_;
goto v___jp_4578_;
}
}
case 1:
{
lean_object* v_records_4687_; uint8_t v_unlocated_4688_; lean_object* v___x_4689_; 
v_records_4687_ = lean_ctor_get(v_a_4685_, 0);
lean_inc_ref(v_records_4687_);
v_unlocated_4688_ = lean_ctor_get_uint8(v_a_4685_, sizeof(void*)*1);
lean_dec_ref_known(v_a_4685_, 1);
v___x_4689_ = l_Array_append___redArg(v_records_4682_, v_records_4687_);
lean_dec_ref(v_records_4687_);
if (v_unlocated_4688_ == 0)
{
v___y_4579_ = v___y_4678_;
v___y_4580_ = v___y_4679_;
v_anyFailed_4581_ = v_anyFailed_4680_;
v_anyUnlocated_4582_ = v_anyUnlocated_4681_;
v_records_4583_ = v___x_4689_;
v_codeQualityEntries_4584_ = v_codeQualityEntries_4683_;
goto v___jp_4578_;
}
else
{
v___y_4579_ = v___y_4678_;
v___y_4580_ = v___y_4679_;
v_anyFailed_4581_ = v_anyFailed_4680_;
v_anyUnlocated_4582_ = v_anyUnlocated_4544_;
v_records_4583_ = v___x_4689_;
v_codeQualityEntries_4584_ = v_codeQualityEntries_4683_;
goto v___jp_4578_;
}
}
default: 
{
lean_object* v_entries_4690_; lean_object* v___x_4691_; 
v_entries_4690_ = lean_ctor_get(v_a_4685_, 0);
lean_inc_ref(v_entries_4690_);
lean_dec_ref_known(v_a_4685_, 1);
v___x_4691_ = l_Array_append___redArg(v_codeQualityEntries_4683_, v_entries_4690_);
lean_dec_ref(v_entries_4690_);
v___y_4579_ = v___y_4678_;
v___y_4580_ = v___y_4679_;
v_anyFailed_4581_ = v_anyFailed_4680_;
v_anyUnlocated_4582_ = v_anyUnlocated_4681_;
v_records_4583_ = v_records_4682_;
v_codeQualityEntries_4584_ = v___x_4691_;
goto v___jp_4578_;
}
}
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref(v_codeQualityEntries_4683_);
lean_dec_ref(v_records_4682_);
lean_dec_ref(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_del_object(v___x_4576_);
lean_dec(v_snd_4574_);
lean_del_object(v___x_4571_);
lean_del_object(v___x_4567_);
lean_del_object(v___x_4563_);
lean_dec(v___x_4531_);
v_a_4692_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4684_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4684_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
v___jp_4700_:
{
lean_object* v___x_4703_; lean_object* v_toEnvExtension_4704_; lean_object* v_asyncMode_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v_merged_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4740_; 
v___x_4703_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_4704_ = lean_ctor_get(v___x_4703_, 0);
v_asyncMode_4705_ = lean_ctor_get(v_toEnvExtension_4704_, 2);
v___x_4706_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_4707_ = lean_box(0);
lean_inc_ref(v___y_4701_);
v___x_4708_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4706_, v___x_4703_, v___y_4701_, v_asyncMode_4705_, v___x_4707_);
v_merged_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4740_ == 0)
{
lean_object* v_unused_4741_; 
v_unused_4741_ = lean_ctor_get(v___x_4708_, 1);
lean_dec(v_unused_4741_);
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4740_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_merged_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4740_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 1, v_merged_4709_);
lean_ctor_set(v___x_4711_, 0, v___y_4702_);
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___y_4702_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v_merged_4709_);
v___x_4714_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4530_, v___x_4714_, v___y_4701_, v_a_4550_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
switch(lean_obj_tag(v_a_4716_))
{
case 0:
{
uint8_t v___x_4717_; 
v___x_4717_ = lean_unbox(v_fst_4561_);
lean_dec(v_fst_4561_);
if (v___x_4717_ == 0)
{
uint8_t v_failed_4718_; uint8_t v___x_4719_; 
v_failed_4718_ = lean_ctor_get_uint8(v_a_4716_, 0);
lean_dec_ref_known(v_a_4716_, 0);
v___x_4719_ = lean_unbox(v_fst_4565_);
lean_dec(v_fst_4565_);
v___y_4678_ = v___y_4701_;
v___y_4679_ = v___x_4714_;
v_anyFailed_4680_ = v_failed_4718_;
v_anyUnlocated_4681_ = v___x_4719_;
v_records_4682_ = v_fst_4569_;
v_codeQualityEntries_4683_ = v_fst_4573_;
goto v___jp_4677_;
}
else
{
uint8_t v___x_4720_; 
lean_dec_ref_known(v_a_4716_, 0);
v___x_4720_ = lean_unbox(v_fst_4565_);
lean_dec(v_fst_4565_);
v___y_4678_ = v___y_4701_;
v___y_4679_ = v___x_4714_;
v_anyFailed_4680_ = v_anyUnlocated_4544_;
v_anyUnlocated_4681_ = v___x_4720_;
v_records_4682_ = v_fst_4569_;
v_codeQualityEntries_4683_ = v_fst_4573_;
goto v___jp_4677_;
}
}
case 1:
{
lean_object* v_records_4721_; uint8_t v_unlocated_4722_; lean_object* v___x_4723_; 
v_records_4721_ = lean_ctor_get(v_a_4716_, 0);
lean_inc_ref(v_records_4721_);
v_unlocated_4722_ = lean_ctor_get_uint8(v_a_4716_, sizeof(void*)*1);
lean_dec_ref_known(v_a_4716_, 1);
v___x_4723_ = l_Array_append___redArg(v_fst_4569_, v_records_4721_);
lean_dec_ref(v_records_4721_);
if (v_unlocated_4722_ == 0)
{
uint8_t v___x_4724_; uint8_t v___x_4725_; 
v___x_4724_ = lean_unbox(v_fst_4561_);
lean_dec(v_fst_4561_);
v___x_4725_ = lean_unbox(v_fst_4565_);
lean_dec(v_fst_4565_);
v___y_4678_ = v___y_4701_;
v___y_4679_ = v___x_4714_;
v_anyFailed_4680_ = v___x_4724_;
v_anyUnlocated_4681_ = v___x_4725_;
v_records_4682_ = v___x_4723_;
v_codeQualityEntries_4683_ = v_fst_4573_;
goto v___jp_4677_;
}
else
{
uint8_t v___x_4726_; 
lean_dec(v_fst_4565_);
v___x_4726_ = lean_unbox(v_fst_4561_);
lean_dec(v_fst_4561_);
v___y_4678_ = v___y_4701_;
v___y_4679_ = v___x_4714_;
v_anyFailed_4680_ = v___x_4726_;
v_anyUnlocated_4681_ = v_anyUnlocated_4544_;
v_records_4682_ = v___x_4723_;
v_codeQualityEntries_4683_ = v_fst_4573_;
goto v___jp_4677_;
}
}
default: 
{
lean_object* v_entries_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; uint8_t v___x_4730_; 
v_entries_4727_ = lean_ctor_get(v_a_4716_, 0);
lean_inc_ref(v_entries_4727_);
lean_dec_ref_known(v_a_4716_, 1);
v___x_4728_ = l_Array_append___redArg(v_fst_4573_, v_entries_4727_);
lean_dec_ref(v_entries_4727_);
v___x_4729_ = lean_unbox(v_fst_4561_);
lean_dec(v_fst_4561_);
v___x_4730_ = lean_unbox(v_fst_4565_);
lean_dec(v_fst_4565_);
v___y_4678_ = v___y_4701_;
v___y_4679_ = v___x_4714_;
v_anyFailed_4680_ = v___x_4729_;
v_anyUnlocated_4681_ = v___x_4730_;
v_records_4682_ = v_fst_4569_;
v_codeQualityEntries_4683_ = v___x_4728_;
goto v___jp_4677_;
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_dec_ref(v___x_4714_);
lean_dec_ref(v___y_4701_);
lean_del_object(v___x_4576_);
lean_dec(v_snd_4574_);
lean_dec(v_fst_4573_);
lean_del_object(v___x_4571_);
lean_dec(v_fst_4569_);
lean_del_object(v___x_4567_);
lean_dec(v_fst_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_fst_4561_);
lean_dec(v___x_4531_);
v_a_4731_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4715_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4715_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
}
v___jp_4742_:
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_compacted_region_free(v_snd_4556_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; uint32_t v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
lean_dec_ref_known(v___x_4744_, 1);
lean_inc(v_a_4550_);
v___x_4745_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4745_, 0, v_a_4550_);
lean_ctor_set_uint8(v___x_4745_, sizeof(void*)*1, v_anyFailed_4543_);
lean_ctor_set_uint8(v___x_4745_, sizeof(void*)*1 + 1, v_anyUnlocated_4544_);
lean_ctor_set_uint8(v___x_4745_, sizeof(void*)*1 + 2, v_anyFailed_4543_);
v___x_4746_ = lean_unsigned_to_nat(2u);
v___x_4747_ = lean_mk_empty_array_with_capacity(v___x_4746_);
v___x_4748_ = lean_array_push(v___x_4747_, v___x_4745_);
v___x_4749_ = lean_array_push(v___x_4748_, v_envLinterModule_4546_);
v___x_4750_ = l_Lean_Options_empty;
v___x_4751_ = 1024;
v___x_4752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___closed__4));
v___x_4753_ = lean_box(1);
v___x_4754_ = l_Lean_importModules(v___x_4749_, v___x_4750_, v___x_4751_, v___x_4752_, v_anyFailed_4543_, v_anyUnlocated_4544_, v___y_4743_, v___x_4753_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v_linterOverrides_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v_linterOverrides_4756_ = lean_ctor_get(v_args_4530_, 0);
v___x_4757_ = lean_array_get_size(v_linterOverrides_4756_);
v___x_4758_ = lean_nat_dec_lt(v___x_4542_, v___x_4757_);
if (v___x_4758_ == 0)
{
v___y_4701_ = v_a_4755_;
v___y_4702_ = v___x_4750_;
goto v___jp_4700_;
}
else
{
uint8_t v___x_4759_; 
v___x_4759_ = lean_nat_dec_le(v___x_4757_, v___x_4757_);
if (v___x_4759_ == 0)
{
if (v___x_4758_ == 0)
{
v___y_4701_ = v_a_4755_;
v___y_4702_ = v___x_4750_;
goto v___jp_4700_;
}
else
{
size_t v___x_4760_; size_t v___x_4761_; lean_object* v___x_4762_; 
v___x_4760_ = ((size_t)0ULL);
v___x_4761_ = lean_usize_of_nat(v___x_4757_);
v___x_4762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_linterOverrides_4756_, v___x_4760_, v___x_4761_, v___x_4750_);
v___y_4701_ = v_a_4755_;
v___y_4702_ = v___x_4762_;
goto v___jp_4700_;
}
}
else
{
size_t v___x_4763_; size_t v___x_4764_; lean_object* v___x_4765_; 
v___x_4763_ = ((size_t)0ULL);
v___x_4764_ = lean_usize_of_nat(v___x_4757_);
v___x_4765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v_linterOverrides_4756_, v___x_4763_, v___x_4764_, v___x_4750_);
v___y_4701_ = v_a_4755_;
v___y_4702_ = v___x_4765_;
goto v___jp_4700_;
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_del_object(v___x_4576_);
lean_dec(v_snd_4574_);
lean_dec(v_fst_4573_);
lean_del_object(v___x_4571_);
lean_dec(v_fst_4569_);
lean_del_object(v___x_4567_);
lean_dec(v_fst_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_fst_4561_);
lean_dec(v___x_4531_);
v_a_4766_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4754_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4754_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_del_object(v___x_4576_);
lean_dec(v_snd_4574_);
lean_dec(v_fst_4573_);
lean_del_object(v___x_4571_);
lean_dec(v_fst_4569_);
lean_del_object(v___x_4567_);
lean_dec(v_fst_4565_);
lean_del_object(v___x_4563_);
lean_dec(v_fst_4561_);
lean_dec_ref_known(v_envLinterModule_4546_, 1);
lean_dec(v___x_4531_);
v_a_4774_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4744_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4744_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
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
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec_ref_known(v_envLinterModule_4546_, 1);
lean_dec_ref(v_b_4535_);
lean_dec(v___x_4531_);
v_a_4791_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4553_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4553_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec_ref_known(v_envLinterModule_4546_, 1);
lean_dec_ref(v_b_4535_);
lean_dec(v___x_4531_);
v_a_4799_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4551_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4551_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
v___jp_4537_:
{
size_t v___x_4539_; size_t v___x_4540_; 
v___x_4539_ = ((size_t)1ULL);
v___x_4540_ = lean_usize_add(v_i_4534_, v___x_4539_);
v_i_4534_ = v___x_4540_;
v_b_4535_ = v_a_4538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v___x_4807_, lean_object* v_args_4808_, lean_object* v___x_4809_, lean_object* v_as_4810_, lean_object* v_sz_4811_, lean_object* v_i_4812_, lean_object* v_b_4813_, lean_object* v___y_4814_){
_start:
{
size_t v_sz_boxed_4815_; size_t v_i_boxed_4816_; lean_object* v_res_4817_; 
v_sz_boxed_4815_ = lean_unbox_usize(v_sz_4811_);
lean_dec(v_sz_4811_);
v_i_boxed_4816_ = lean_unbox_usize(v_i_4812_);
lean_dec(v_i_4812_);
v_res_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_4807_, v_args_4808_, v___x_4809_, v_as_4810_, v_sz_boxed_4815_, v_i_boxed_4816_, v_b_4813_);
lean_dec_ref(v_as_4810_);
lean_dec_ref(v_args_4808_);
lean_dec(v___x_4807_);
return v_res_4817_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4818_ = l_Lean_NameSet_empty;
v___x_4819_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
lean_ctor_set(v___x_4820_, 1, v___x_4818_);
return v___x_4820_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_4822_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_4823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
lean_ctor_set(v___x_4823_, 1, v___x_4821_);
return v___x_4823_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = 0;
v___x_4826_ = lean_box_uint32(v___x_4825_);
return v___x_4826_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = 1;
v___x_4828_ = lean_box_uint32(v___x_4827_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_4829_){
_start:
{
lean_object* v_mods_4831_; uint8_t v_mode_4832_; lean_object* v_srcSearchPath_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v_anyFailed_4836_; 
v_mods_4831_ = lean_ctor_get(v_args_4829_, 1);
lean_inc_ref(v_mods_4831_);
v_mode_4832_ = lean_ctor_get_uint8(v_args_4829_, sizeof(void*)*3 + 1);
v_srcSearchPath_4833_ = lean_ctor_get(v_args_4829_, 2);
v___x_4834_ = lean_array_get_size(v_mods_4831_);
v___x_4835_ = lean_unsigned_to_nat(0u);
v_anyFailed_4836_ = lean_nat_dec_eq(v___x_4834_, v___x_4835_);
if (v_anyFailed_4836_ == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_4837_) == 0)
{
lean_object* v_a_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; size_t v_sz_4845_; size_t v___x_4846_; lean_object* v___x_4847_; 
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc(v_a_4838_);
lean_dec_ref_known(v___x_4837_, 1);
lean_inc(v_srcSearchPath_4833_);
v___x_4839_ = l_List_appendTR___redArg(v_srcSearchPath_4833_, v_a_4838_);
v___x_4840_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_4841_ = lean_box(v_anyFailed_4836_);
v___x_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
lean_ctor_set(v___x_4842_, 1, v___x_4840_);
v___x_4843_ = lean_box(v_anyFailed_4836_);
v___x_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
lean_ctor_set(v___x_4844_, 1, v___x_4842_);
v_sz_4845_ = lean_array_size(v_mods_4831_);
v___x_4846_ = ((size_t)0ULL);
v___x_4847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_4834_, v_args_4829_, v___x_4839_, v_mods_4831_, v_sz_4845_, v___x_4846_, v___x_4844_);
lean_dec_ref(v_mods_4831_);
lean_dec_ref(v_args_4829_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4913_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4913_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4913_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
switch(v_mode_4832_)
{
case 0:
{
lean_object* v_fst_4852_; uint8_t v___x_4853_; 
v_fst_4852_ = lean_ctor_get(v_a_4848_, 0);
lean_inc(v_fst_4852_);
lean_dec(v_a_4848_);
v___x_4853_ = lean_unbox(v_fst_4852_);
lean_dec(v_fst_4852_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4854_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v___x_4854_);
v___x_4856_ = v___x_4850_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
else
{
lean_object* v___x_4858_; lean_object* v___x_4860_; 
v___x_4858_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v___x_4858_);
v___x_4860_ = v___x_4850_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
case 1:
{
lean_object* v_snd_4862_; lean_object* v_snd_4863_; lean_object* v_fst_4864_; lean_object* v_fst_4865_; lean_object* v___x_4866_; 
v_snd_4862_ = lean_ctor_get(v_a_4848_, 1);
lean_inc(v_snd_4862_);
lean_del_object(v___x_4850_);
lean_dec(v_a_4848_);
v_snd_4863_ = lean_ctor_get(v_snd_4862_, 1);
lean_inc(v_snd_4863_);
v_fst_4864_ = lean_ctor_get(v_snd_4862_, 0);
lean_inc(v_fst_4864_);
lean_dec(v_snd_4862_);
v_fst_4865_ = lean_ctor_get(v_snd_4863_, 0);
lean_inc(v_fst_4865_);
lean_dec(v_snd_4863_);
v___x_4866_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_4865_);
lean_dec(v_fst_4865_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4879_; 
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4879_ == 0)
{
lean_object* v_unused_4880_; 
v_unused_4880_ = lean_ctor_get(v___x_4866_, 0);
lean_dec(v_unused_4880_);
v___x_4868_ = v___x_4866_;
v_isShared_4869_ = v_isSharedCheck_4879_;
goto v_resetjp_4867_;
}
else
{
lean_dec(v___x_4866_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4879_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
uint8_t v___x_4870_; 
v___x_4870_ = lean_unbox(v_fst_4864_);
lean_dec(v_fst_4864_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4871_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4871_);
v___x_4873_ = v___x_4868_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4875_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4875_);
v___x_4877_ = v___x_4868_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
lean_dec(v_fst_4864_);
v_a_4881_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4866_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4866_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
default: 
{
lean_object* v_snd_4889_; lean_object* v_snd_4890_; lean_object* v_snd_4891_; lean_object* v_fst_4892_; lean_object* v___x_4893_; size_t v_sz_4894_; lean_object* v___x_4895_; 
v_snd_4889_ = lean_ctor_get(v_a_4848_, 1);
lean_inc(v_snd_4889_);
lean_del_object(v___x_4850_);
lean_dec(v_a_4848_);
v_snd_4890_ = lean_ctor_get(v_snd_4889_, 1);
lean_inc(v_snd_4890_);
lean_dec(v_snd_4889_);
v_snd_4891_ = lean_ctor_get(v_snd_4890_, 1);
lean_inc(v_snd_4891_);
lean_dec(v_snd_4890_);
v_fst_4892_ = lean_ctor_get(v_snd_4891_, 0);
lean_inc(v_fst_4892_);
lean_dec(v_snd_4891_);
v___x_4893_ = lean_box(0);
v_sz_4894_ = lean_array_size(v_fst_4892_);
v___x_4895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v_fst_4892_, v_sz_4894_, v___x_4846_, v___x_4893_);
lean_dec(v_fst_4892_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4903_; 
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; 
v_unused_4904_ = lean_ctor_get(v___x_4895_, 0);
lean_dec(v_unused_4904_);
v___x_4897_ = v___x_4895_;
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
else
{
lean_dec(v___x_4895_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
v_a_4905_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4895_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4895_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
v_a_4914_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4847_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4847_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec_ref(v_mods_4831_);
lean_dec_ref(v_args_4829_);
v_a_4922_ = lean_ctor_get(v___x_4837_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4837_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4837_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec_ref(v_mods_4831_);
lean_dec_ref(v_args_4829_);
v___x_4930_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__2));
v___x_4931_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_4930_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4939_; 
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v___x_4931_, 0);
lean_dec(v_unused_4940_);
v___x_4933_ = v___x_4931_;
v_isShared_4934_ = v_isSharedCheck_4939_;
goto v_resetjp_4932_;
}
else
{
lean_dec(v___x_4931_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4939_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v___x_4935_);
v___x_4937_ = v___x_4933_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
v_a_4941_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4931_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4931_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Lake_BuiltinLint_run(v_args_4949_);
return v_res_4951_;
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
