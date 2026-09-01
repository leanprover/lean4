// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter public import Lean.Linter.PersistentLintLog import Lean.Elab.DocString.Builtin.Postponed import Lean.Linter.CodeQuality
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
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
lean_object* l_Lean_Linter_CodeQuality_getPackageChecks(lean_object*, lean_object*);
lean_object* l_Lean_Linter_CodeQuality_runPackageChecks(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_linter_doc_deferred;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Doc_DeferredCheck_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Linter_getAllCodeQualityEntries(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "set_option "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " false in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_BuiltinLint_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_run___closed__0;
static lean_once_cell_t l_Lake_BuiltinLint_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_run___closed__1;
static lean_once_cell_t l_Lake_BuiltinLint_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_run___closed__2;
static const lean_string_object l_Lake_BuiltinLint_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__3 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__3_value;
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
uint8_t v_x_21__boxed_69_; uint8_t v_y_22__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_21__boxed_69_ = lean_unbox(v_x_67_);
v_y_22__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lake_BuiltinLint_instBEqMode_beq(v_x_21__boxed_69_, v_y_22__boxed_70_);
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
v_mode_154_ = lean_ctor_get_uint8(v_args_152_, sizeof(void*)*4 + 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(size_t v_sz_337_, size_t v_i_338_, lean_object* v_bs_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_lt(v_i_338_, v_sz_337_);
if (v___x_340_ == 0)
{
return v_bs_339_;
}
else
{
lean_object* v_v_341_; lean_object* v_entry_342_; lean_object* v___x_343_; lean_object* v_bs_x27_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; 
v_v_341_ = lean_array_uget_borrowed(v_bs_339_, v_i_338_);
v_entry_342_ = lean_ctor_get(v_v_341_, 1);
lean_inc_ref(v_entry_342_);
v___x_343_ = lean_unsigned_to_nat(0u);
v_bs_x27_344_ = lean_array_uset(v_bs_339_, v_i_338_, v___x_343_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_338_, v___x_345_);
v___x_347_ = lean_array_uset(v_bs_x27_344_, v_i_338_, v_entry_342_);
v_i_338_ = v___x_346_;
v_bs_339_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0___boxed(lean_object* v_sz_349_, lean_object* v_i_350_, lean_object* v_bs_351_){
_start:
{
size_t v_sz_boxed_352_; size_t v_i_boxed_353_; lean_object* v_res_354_; 
v_sz_boxed_352_ = lean_unbox_usize(v_sz_349_);
lean_dec(v_sz_349_);
v_i_boxed_353_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_boxed_352_, v_i_boxed_353_, v_bs_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(lean_object* v_linterOpts_355_, lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_, lean_object* v_b_359_){
_start:
{
lean_object* v___y_361_; uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_eq(v_i_357_, v_stop_358_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v_linter_x3f_367_; 
v___x_366_ = lean_array_uget_borrowed(v_as_356_, v_i_357_);
v_linter_x3f_367_ = lean_ctor_get(v___x_366_, 0);
if (lean_obj_tag(v_linter_x3f_367_) == 0)
{
lean_object* v___x_368_; 
lean_inc(v___x_366_);
v___x_368_ = lean_array_push(v_b_359_, v___x_366_);
v___y_361_ = v___x_368_;
goto v___jp_360_;
}
else
{
lean_object* v_val_369_; uint8_t v___x_370_; 
v_val_369_ = lean_ctor_get(v_linter_x3f_367_, 0);
v___x_370_ = l_Lean_Linter_isLinterEnabledByOptions(v_val_369_, v_linterOpts_355_);
if (v___x_370_ == 0)
{
v___y_361_ = v_b_359_;
goto v___jp_360_;
}
else
{
lean_object* v___x_371_; 
lean_inc(v___x_366_);
v___x_371_ = lean_array_push(v_b_359_, v___x_366_);
v___y_361_ = v___x_371_;
goto v___jp_360_;
}
}
}
else
{
return v_b_359_;
}
v___jp_360_:
{
size_t v___x_362_; size_t v___x_363_; 
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_357_, v___x_362_);
v_i_357_ = v___x_363_;
v_b_359_ = v___y_361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1___boxed(lean_object* v_linterOpts_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_, lean_object* v_b_376_){
_start:
{
size_t v_i_boxed_377_; size_t v_stop_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_377_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_378_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_372_, v_as_373_, v_i_boxed_377_, v_stop_boxed_378_, v_b_376_);
lean_dec_ref(v_as_373_);
lean_dec_ref(v_linterOpts_372_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(lean_object* v_args_382_, lean_object* v_linterOpts_383_, lean_object* v_mod_384_, lean_object* v_as_385_, size_t v_sz_386_, size_t v_i_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_a_390_; uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_394_ == 0)
{
return v_b_388_;
}
else
{
lean_object* v_a_395_; lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_439_; 
v_a_395_ = lean_array_uget(v_as_385_, v_i_387_);
v_fst_396_ = lean_ctor_get(v_a_395_, 0);
v_snd_397_ = lean_ctor_get(v_a_395_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_439_ == 0)
{
v___x_399_ = v_a_395_;
v_isShared_400_ = v_isSharedCheck_439_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_a_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_439_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_438_; 
v_fst_401_ = lean_ctor_get(v_b_388_, 0);
v_snd_402_ = lean_ctor_get(v_b_388_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_438_ == 0)
{
v___x_404_ = v_b_388_;
v_isShared_405_ = v_isSharedCheck_438_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_b_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_438_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___y_407_; lean_object* v___y_408_; uint8_t v___y_421_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = l_Lean_Name_getRoot(v_mod_384_);
v___x_436_ = l_Lean_Name_isPrefixOf(v___x_435_, v_fst_396_);
lean_dec(v___x_435_);
if (v___x_436_ == 0)
{
v___y_421_ = v___x_436_;
goto v___jp_420_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_NameSet_contains(v_fst_401_, v_fst_396_);
if (v___x_437_ == 0)
{
v___y_421_ = v___x_436_;
goto v___jp_420_;
}
else
{
lean_del_object(v___x_404_);
lean_dec(v_snd_397_);
lean_dec(v_fst_396_);
goto v___jp_416_;
}
}
v___jp_406_:
{
size_t v_sz_409_; size_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v_sz_409_ = lean_array_size(v___y_408_);
v___x_410_ = ((size_t)0ULL);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_409_, v___x_410_, v___y_408_);
v___x_412_ = l_Array_append___redArg(v_snd_402_, v___x_411_);
lean_dec_ref(v___x_411_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_412_);
lean_ctor_set(v___x_404_, 0, v___y_407_);
v___x_414_ = v___x_404_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___y_407_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v_a_390_ = v___x_414_;
goto v___jp_389_;
}
}
v___jp_416_:
{
lean_object* v___x_418_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v_snd_402_);
lean_ctor_set(v___x_399_, 0, v_fst_401_);
v___x_418_ = v___x_399_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_fst_401_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_402_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v_a_390_ = v___x_418_;
goto v___jp_389_;
}
}
v___jp_420_:
{
if (v___y_421_ == 0)
{
lean_del_object(v___x_404_);
lean_dec(v_snd_397_);
lean_dec(v_fst_396_);
goto v___jp_416_;
}
else
{
uint8_t v_lintOnly_422_; lean_object* v___x_423_; 
lean_del_object(v___x_399_);
v_lintOnly_422_ = lean_ctor_get_uint8(v_args_382_, sizeof(void*)*4);
v___x_423_ = l_Lean_NameSet_insert(v_fst_401_, v_fst_396_);
if (v_lintOnly_422_ == 0)
{
v___y_407_ = v___x_423_;
v___y_408_ = v_snd_397_;
goto v___jp_406_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_array_get_size(v_snd_397_);
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0));
v___x_427_ = lean_nat_dec_lt(v___x_424_, v___x_425_);
if (v___x_427_ == 0)
{
lean_dec(v_snd_397_);
v___y_407_ = v___x_423_;
v___y_408_ = v___x_426_;
goto v___jp_406_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_le(v___x_425_, v___x_425_);
if (v___x_428_ == 0)
{
if (v___x_427_ == 0)
{
lean_dec(v_snd_397_);
v___y_407_ = v___x_423_;
v___y_408_ = v___x_426_;
goto v___jp_406_;
}
else
{
size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((size_t)0ULL);
v___x_430_ = lean_usize_of_nat(v___x_425_);
v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_383_, v_snd_397_, v___x_429_, v___x_430_, v___x_426_);
lean_dec(v_snd_397_);
v___y_407_ = v___x_423_;
v___y_408_ = v___x_431_;
goto v___jp_406_;
}
}
else
{
size_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((size_t)0ULL);
v___x_433_ = lean_usize_of_nat(v___x_425_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_383_, v_snd_397_, v___x_432_, v___x_433_, v___x_426_);
lean_dec(v_snd_397_);
v___y_407_ = v___x_423_;
v___y_408_ = v___x_434_;
goto v___jp_406_;
}
}
}
}
}
}
}
}
v___jp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_387_, v___x_391_);
v_i_387_ = v___x_392_;
v_b_388_ = v_a_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___boxed(lean_object* v_args_440_, lean_object* v_linterOpts_441_, lean_object* v_mod_442_, lean_object* v_as_443_, lean_object* v_sz_444_, lean_object* v_i_445_, lean_object* v_b_446_){
_start:
{
size_t v_sz_boxed_447_; size_t v_i_boxed_448_; lean_object* v_res_449_; 
v_sz_boxed_447_ = lean_unbox_usize(v_sz_444_);
lean_dec(v_sz_444_);
v_i_boxed_448_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_440_, v_linterOpts_441_, v_mod_442_, v_as_443_, v_sz_boxed_447_, v_i_boxed_448_, v_b_446_);
lean_dec_ref(v_as_443_);
lean_dec(v_mod_442_);
lean_dec_ref(v_linterOpts_441_);
lean_dec_ref(v_args_440_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(lean_object* v_args_452_, lean_object* v_linterOpts_453_, lean_object* v_env_454_, lean_object* v_mod_455_, lean_object* v_collectedModules_456_){
_start:
{
lean_object* v_acc_457_; lean_object* v___x_458_; lean_object* v___x_459_; size_t v_sz_460_; size_t v___x_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_acc_457_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v___x_458_ = l_Lean_Linter_getAllCodeQualityEntries(v_env_454_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_collectedModules_456_);
lean_ctor_set(v___x_459_, 1, v_acc_457_);
v_sz_460_ = lean_array_size(v___x_458_);
v___x_461_ = ((size_t)0ULL);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_args_452_, v_linterOpts_453_, v_mod_455_, v___x_458_, v_sz_460_, v___x_461_, v___x_459_);
lean_dec_ref(v___x_458_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
v_snd_464_ = lean_ctor_get(v___x_462_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_462_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v___x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v_fst_463_);
lean_ctor_set(v___x_466_, 0, v_snd_464_);
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_snd_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_fst_463_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___boxed(lean_object* v_args_472_, lean_object* v_linterOpts_473_, lean_object* v_env_474_, lean_object* v_mod_475_, lean_object* v_collectedModules_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_472_, v_linterOpts_473_, v_env_474_, v_mod_475_, v_collectedModules_476_);
lean_dec(v_mod_475_);
lean_dec_ref(v_env_474_);
lean_dec_ref(v_linterOpts_473_);
lean_dec_ref(v_args_472_);
return v_res_477_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_478_){
_start:
{
uint8_t v_isModule_480_; 
v_isModule_480_ = lean_ctor_get_uint8(v_modData_478_, sizeof(void*)*5);
return v_isModule_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_481_, lean_object* v_a_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_481_);
lean_dec_ref(v_modData_481_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_487_){
_start:
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 32;
v___x_489_ = lean_uint32_dec_eq(v_c_487_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 9;
v___x_491_ = lean_uint32_dec_eq(v_c_487_, v___x_490_);
return v___x_491_;
}
else
{
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_492_){
_start:
{
uint32_t v_c_boxed_493_; uint8_t v_res_494_; lean_object* v_r_495_; 
v_c_boxed_493_ = lean_unbox_uint32(v_c_492_);
lean_dec(v_c_492_);
v_res_494_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_496_, lean_object* v_stopPos_497_, lean_object* v_i_498_){
_start:
{
uint8_t v___y_500_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_add(v_i_498_, v___x_503_);
v___x_505_ = lean_nat_dec_le(v___x_504_, v_stopPos_497_);
lean_dec(v___x_504_);
if (v___x_505_ == 0)
{
return v_i_498_;
}
else
{
if (v___x_505_ == 0)
{
v___y_500_ = v___x_505_;
goto v___jp_499_;
}
else
{
uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_string_utf8_get(v_s_496_, v_i_498_);
v___x_507_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_506_);
v___y_500_ = v___x_507_;
goto v___jp_499_;
}
}
v___jp_499_:
{
if (v___y_500_ == 0)
{
return v_i_498_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_string_utf8_next(v_s_496_, v_i_498_);
lean_dec(v_i_498_);
v_i_498_ = v___x_501_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_508_, lean_object* v_stopPos_509_, lean_object* v_i_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_508_, v_stopPos_509_, v_i_510_);
lean_dec(v_stopPos_509_);
lean_dec_ref(v_s_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_e_515_; lean_object* v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_string_utf8_byte_size(v_line_512_);
v_e_515_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_512_, v___x_514_, v___x_513_);
v___x_516_ = lean_string_utf8_extract(v_line_512_, v___x_513_, v_e_515_);
lean_dec(v_e_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_517_);
lean_dec_ref(v_line_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_523_);
lean_dec_ref(v_s_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
return v_x_525_;
}
else
{
lean_object* v_key_527_; lean_object* v_value_528_; lean_object* v_tail_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_key_527_ = lean_ctor_get(v_x_526_, 0);
v_value_528_ = lean_ctor_get(v_x_526_, 1);
v_tail_529_ = lean_ctor_get(v_x_526_, 2);
lean_inc(v_value_528_);
lean_inc(v_key_527_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_key_527_);
lean_ctor_set(v___x_530_, 1, v_value_528_);
v___x_531_ = lean_array_push(v_x_525_, v___x_530_);
v_x_525_ = v___x_531_;
v_x_526_ = v_tail_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_533_, v_x_534_);
lean_dec(v_x_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_, lean_object* v_b_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; size_t v___x_543_; size_t v___x_544_; 
v___x_541_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_542_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_539_, v___x_541_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_537_, v___x_543_);
v_i_537_ = v___x_544_;
v_b_539_ = v___x_542_;
goto _start;
}
else
{
return v_b_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_stop_548_, lean_object* v_b_549_){
_start:
{
size_t v_i_boxed_550_; size_t v_stop_boxed_551_; lean_object* v_res_552_; 
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_stop_boxed_551_ = lean_unbox_usize(v_stop_548_);
lean_dec(v_stop_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_546_, v_i_boxed_550_, v_stop_boxed_551_, v_b_549_);
lean_dec_ref(v_as_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_553_){
_start:
{
lean_object* v___x_555_; lean_object* v_putStr_556_; lean_object* v___x_557_; 
v___x_555_ = lean_get_stderr();
v_putStr_556_ = lean_ctor_get(v___x_555_, 4);
lean_inc_ref(v_putStr_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = lean_apply_2(v_putStr_556_, v_s_553_, lean_box(0));
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_561_){
_start:
{
uint32_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = 10;
v___x_564_ = lean_string_push(v_s_561_, v___x_563_);
v___x_565_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
return v_x_569_;
}
else
{
lean_object* v_key_571_; lean_object* v_value_572_; lean_object* v_tail_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_key_571_ = lean_ctor_get(v_x_570_, 0);
v_value_572_ = lean_ctor_get(v_x_570_, 1);
v_tail_573_ = lean_ctor_get(v_x_570_, 2);
lean_inc(v_value_572_);
lean_inc(v_key_571_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_key_571_);
lean_ctor_set(v___x_574_, 1, v_value_572_);
v___x_575_ = lean_array_push(v_x_569_, v___x_574_);
v_x_569_ = v___x_575_;
v_x_570_ = v_tail_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_577_, v_x_578_);
lean_dec(v_x_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_580_, size_t v_i_581_, size_t v_stop_582_, lean_object* v_b_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_usize_dec_eq(v_i_581_, v_stop_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; size_t v___x_587_; size_t v___x_588_; 
v___x_585_ = lean_array_uget_borrowed(v_as_580_, v_i_581_);
v___x_586_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_583_, v___x_585_);
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_581_, v___x_587_);
v_i_581_ = v___x_588_;
v_b_583_ = v___x_586_;
goto _start;
}
else
{
return v_b_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_590_, lean_object* v_i_591_, lean_object* v_stop_592_, lean_object* v_b_593_){
_start:
{
size_t v_i_boxed_594_; size_t v_stop_boxed_595_; lean_object* v_res_596_; 
v_i_boxed_594_ = lean_unbox_usize(v_i_591_);
lean_dec(v_i_591_);
v_stop_boxed_595_ = lean_unbox_usize(v_stop_592_);
lean_dec(v_stop_592_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_590_, v_i_boxed_594_, v_stop_boxed_595_, v_b_593_);
lean_dec_ref(v_as_590_);
return v_res_596_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_597_, lean_object* v_b_598_){
_start:
{
lean_object* v_fst_599_; lean_object* v_fst_600_; uint8_t v___x_601_; 
v_fst_599_ = lean_ctor_get(v_b_598_, 0);
v_fst_600_ = lean_ctor_get(v_a_597_, 0);
v___x_601_ = lean_nat_dec_lt(v_fst_599_, v_fst_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_602_, v_b_603_);
lean_dec_ref(v_b_603_);
lean_dec_ref(v_a_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_606_, lean_object* v_pivot_607_, lean_object* v_as_608_, lean_object* v_i_609_, lean_object* v_k_610_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_lt(v_k_610_, v_hi_606_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_k_610_);
v___x_612_ = lean_array_fswap(v_as_608_, v_i_609_, v_hi_606_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_i_609_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v_fst_614_; lean_object* v___x_615_; lean_object* v_fst_616_; uint8_t v___x_617_; 
v_fst_614_ = lean_ctor_get(v_pivot_607_, 0);
v___x_615_ = lean_array_fget_borrowed(v_as_608_, v_k_610_);
v_fst_616_ = lean_ctor_get(v___x_615_, 0);
v___x_617_ = lean_nat_dec_lt(v_fst_614_, v_fst_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_k_610_, v___x_618_);
lean_dec(v_k_610_);
v_k_610_ = v___x_619_;
goto _start;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_array_fswap(v_as_608_, v_i_609_, v_k_610_);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v_i_609_, v___x_622_);
lean_dec(v_i_609_);
v___x_624_ = lean_nat_add(v_k_610_, v___x_622_);
lean_dec(v_k_610_);
v_as_608_ = v___x_621_;
v_i_609_ = v___x_623_;
v_k_610_ = v___x_624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_626_, lean_object* v_pivot_627_, lean_object* v_as_628_, lean_object* v_i_629_, lean_object* v_k_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_626_, v_pivot_627_, v_as_628_, v_i_629_, v_k_630_);
lean_dec_ref(v_pivot_627_);
lean_dec(v_hi_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_632_, lean_object* v_as_633_, lean_object* v_lo_634_, lean_object* v_hi_635_){
_start:
{
lean_object* v___y_637_; uint8_t v___x_647_; 
v___x_647_ = lean_nat_dec_lt(v_lo_634_, v_hi_635_);
if (v___x_647_ == 0)
{
lean_dec(v_lo_634_);
return v_as_633_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_mid_650_; lean_object* v___y_652_; lean_object* v___y_658_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_648_ = lean_nat_add(v_lo_634_, v_hi_635_);
v___x_649_ = lean_unsigned_to_nat(1u);
v_mid_650_ = lean_nat_shiftr(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
v___x_663_ = lean_array_fget_borrowed(v_as_633_, v_mid_650_);
v___x_664_ = lean_array_fget_borrowed(v_as_633_, v_lo_634_);
v___x_665_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
v___y_658_ = v_as_633_;
goto v___jp_657_;
}
else
{
lean_object* v___x_666_; 
v___x_666_ = lean_array_fswap(v_as_633_, v_lo_634_, v_mid_650_);
v___y_658_ = v___x_666_;
goto v___jp_657_;
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_array_fget_borrowed(v___y_652_, v_mid_650_);
v___x_654_ = lean_array_fget_borrowed(v___y_652_, v_hi_635_);
v___x_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_dec(v_mid_650_);
v___y_637_ = v___y_652_;
goto v___jp_636_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_array_fswap(v___y_652_, v_mid_650_, v_hi_635_);
lean_dec(v_mid_650_);
v___y_637_ = v___x_656_;
goto v___jp_636_;
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_array_fget_borrowed(v___y_658_, v_hi_635_);
v___x_660_ = lean_array_fget_borrowed(v___y_658_, v_lo_634_);
v___x_661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
v___y_652_ = v___y_658_;
goto v___jp_651_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = lean_array_fswap(v___y_658_, v_lo_634_, v_hi_635_);
v___y_652_ = v___x_662_;
goto v___jp_651_;
}
}
}
v___jp_636_:
{
lean_object* v_pivot_638_; lean_object* v___x_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; uint8_t v___x_642_; 
v_pivot_638_ = lean_array_fget(v___y_637_, v_hi_635_);
lean_inc_n(v_lo_634_, 2);
v___x_639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_635_, v_pivot_638_, v___y_637_, v_lo_634_, v_lo_634_);
lean_dec(v_pivot_638_);
v_fst_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_fst_640_);
v_snd_641_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_snd_641_);
lean_dec_ref(v___x_639_);
v___x_642_ = lean_nat_dec_le(v_hi_635_, v_fst_640_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_632_, v_snd_641_, v_lo_634_, v_fst_640_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_fst_640_, v___x_644_);
lean_dec(v_fst_640_);
v_as_633_ = v___x_643_;
v_lo_634_ = v___x_645_;
goto _start;
}
else
{
lean_dec(v_fst_640_);
lean_dec(v_lo_634_);
return v_snd_641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_667_, lean_object* v_as_668_, lean_object* v_lo_669_, lean_object* v_hi_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_667_, v_as_668_, v_lo_669_, v_hi_670_);
lean_dec(v_hi_670_);
lean_dec(v_n_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v_a_675_, lean_object* v_b_676_){
_start:
{
lean_object* v_it_678_; lean_object* v_startInclusive_679_; lean_object* v_endExclusive_680_; 
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v_currPos_684_; lean_object* v_searcher_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_708_; 
v_currPos_684_ = lean_ctor_get(v_a_675_, 0);
v_searcher_685_ = lean_ctor_get(v_a_675_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_708_ == 0)
{
v___x_687_ = v_a_675_;
v_isShared_688_ = v_isSharedCheck_708_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_searcher_685_);
lean_inc(v_currPos_684_);
lean_dec(v_a_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_708_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint8_t v_decide_689_; 
v_decide_689_ = lean_nat_dec_eq(v_searcher_685_, v___x_674_);
if (v_decide_689_ == 0)
{
uint32_t v___x_690_; uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_690_ = 10;
v___x_691_ = lean_string_utf8_get_fast(v_a_672_, v_searcher_685_);
v___x_692_ = lean_uint32_dec_eq(v___x_691_, v___x_690_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_string_utf8_next_fast(v_a_672_, v_searcher_685_);
lean_dec(v_searcher_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_693_);
v___x_695_ = v___x_687_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_currPos_684_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_a_675_ = v___x_695_;
goto _start;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_slice_701_; lean_object* v_nextIt_703_; 
v___x_698_ = lean_string_utf8_next_fast(v_a_672_, v_searcher_685_);
v___x_699_ = lean_nat_sub(v___x_698_, v_searcher_685_);
v___x_700_ = lean_nat_add(v_searcher_685_, v___x_699_);
lean_dec(v___x_699_);
v_slice_701_ = l_String_Slice_subslice_x21(v___x_673_, v_currPos_684_, v_searcher_685_);
lean_inc(v___x_700_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_700_);
lean_ctor_set(v___x_687_, 0, v___x_700_);
v_nextIt_703_ = v___x_687_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_700_);
v_nextIt_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v_startInclusive_704_; lean_object* v_endExclusive_705_; 
v_startInclusive_704_ = lean_ctor_get(v_slice_701_, 0);
lean_inc(v_startInclusive_704_);
v_endExclusive_705_ = lean_ctor_get(v_slice_701_, 1);
lean_inc(v_endExclusive_705_);
lean_dec_ref(v_slice_701_);
v_it_678_ = v_nextIt_703_;
v_startInclusive_679_ = v_startInclusive_704_;
v_endExclusive_680_ = v_endExclusive_705_;
goto v___jp_677_;
}
}
}
else
{
lean_object* v___x_707_; 
lean_del_object(v___x_687_);
lean_dec(v_searcher_685_);
v___x_707_ = lean_box(1);
lean_inc(v___x_674_);
v_it_678_ = v___x_707_;
v_startInclusive_679_ = v_currPos_684_;
v_endExclusive_680_ = v___x_674_;
goto v___jp_677_;
}
}
}
else
{
lean_dec(v___x_674_);
lean_dec_ref(v_a_672_);
return v_b_676_;
}
v___jp_677_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc_ref(v_a_672_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_a_672_);
lean_ctor_set(v___x_681_, 1, v_startInclusive_679_);
lean_ctor_set(v___x_681_, 2, v_endExclusive_680_);
v___x_682_ = lean_array_push(v_b_676_, v___x_681_);
v_a_675_ = v_it_678_;
v_b_676_ = v___x_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_a_712_, lean_object* v_b_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_709_, v___x_710_, v___x_711_, v_a_712_, v_b_713_);
lean_dec_ref(v___x_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v___x_720_; lean_object* v_bs_x27_721_; lean_object* v___x_722_; size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_v_719_ = lean_array_uget(v_bs_717_, v_i_716_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_bs_x27_721_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_720_);
v___x_722_ = l_String_Slice_toString(v_v_719_);
lean_dec(v_v_719_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_716_, v___x_723_);
v___x_725_ = lean_array_uset(v_bs_x27_721_, v_i_716_, v___x_722_);
v_i_716_ = v___x_724_;
v_bs_717_ = v___x_725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_bs_729_){
_start:
{
size_t v_sz_boxed_730_; size_t v_i_boxed_731_; lean_object* v_res_732_; 
v_sz_boxed_730_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_730_, v_i_boxed_731_, v_bs_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
return v_x_733_;
}
else
{
lean_object* v_key_735_; lean_object* v_value_736_; lean_object* v_tail_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_760_; 
v_key_735_ = lean_ctor_get(v_x_734_, 0);
v_value_736_ = lean_ctor_get(v_x_734_, 1);
v_tail_737_ = lean_ctor_get(v_x_734_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_760_ == 0)
{
v___x_739_ = v_x_734_;
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_tail_737_);
lean_inc(v_value_736_);
lean_inc(v_key_735_);
lean_dec(v_x_734_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; uint64_t v___x_742_; uint64_t v___x_743_; uint64_t v___x_744_; uint64_t v_fold_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_741_ = lean_array_get_size(v_x_733_);
v___x_742_ = lean_uint64_of_nat(v_key_735_);
v___x_743_ = 32ULL;
v___x_744_ = lean_uint64_shift_right(v___x_742_, v___x_743_);
v_fold_745_ = lean_uint64_xor(v___x_742_, v___x_744_);
v___x_746_ = 16ULL;
v___x_747_ = lean_uint64_shift_right(v_fold_745_, v___x_746_);
v___x_748_ = lean_uint64_xor(v_fold_745_, v___x_747_);
v___x_749_ = lean_uint64_to_usize(v___x_748_);
v___x_750_ = lean_usize_of_nat(v___x_741_);
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_sub(v___x_750_, v___x_751_);
v___x_753_ = lean_usize_land(v___x_749_, v___x_752_);
v___x_754_ = lean_array_uget_borrowed(v_x_733_, v___x_753_);
lean_inc(v___x_754_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 2, v___x_754_);
v___x_756_ = v___x_739_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_key_735_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_value_736_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v___x_754_);
v___x_756_ = v_reuseFailAlloc_759_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; 
v___x_757_ = lean_array_uset(v_x_733_, v___x_753_, v___x_756_);
v_x_733_ = v___x_757_;
v_x_734_ = v_tail_737_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_761_, lean_object* v_source_762_, lean_object* v_target_763_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_array_get_size(v_source_762_);
v___x_765_ = lean_nat_dec_lt(v_i_761_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec_ref(v_source_762_);
lean_dec(v_i_761_);
return v_target_763_;
}
else
{
lean_object* v_es_766_; lean_object* v___x_767_; lean_object* v_source_768_; lean_object* v_target_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_es_766_ = lean_array_fget(v_source_762_, v_i_761_);
v___x_767_ = lean_box(0);
v_source_768_ = lean_array_fset(v_source_762_, v_i_761_, v___x_767_);
v_target_769_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_763_, v_es_766_);
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_add(v_i_761_, v___x_770_);
lean_dec(v_i_761_);
v_i_761_ = v___x_771_;
v_source_762_ = v_source_768_;
v_target_763_ = v_target_769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_nbuckets_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_774_ = lean_array_get_size(v_data_773_);
v___x_775_ = lean_unsigned_to_nat(2u);
v_nbuckets_776_ = lean_nat_mul(v___x_774_, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_box(0);
v___x_779_ = lean_mk_array(v_nbuckets_776_, v___x_778_);
v___x_780_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_777_, v_data_773_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
else
{
lean_object* v_key_784_; lean_object* v_tail_785_; uint8_t v___x_786_; 
v_key_784_ = lean_ctor_get(v_x_782_, 0);
v_tail_785_ = lean_ctor_get(v_x_782_, 2);
v___x_786_ = lean_nat_dec_eq(v_key_784_, v_a_781_);
if (v___x_786_ == 0)
{
v_x_782_ = v_tail_785_;
goto _start;
}
else
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_788_, lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_788_, v_x_789_);
lean_dec(v_x_789_);
lean_dec(v_a_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_792_, lean_object* v_b_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_dec(v_b_793_);
lean_dec(v_a_792_);
return v_x_794_;
}
else
{
lean_object* v_key_795_; lean_object* v_value_796_; lean_object* v_tail_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_809_; 
v_key_795_ = lean_ctor_get(v_x_794_, 0);
v_value_796_ = lean_ctor_get(v_x_794_, 1);
v_tail_797_ = lean_ctor_get(v_x_794_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_809_ == 0)
{
v___x_799_ = v_x_794_;
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_tail_797_);
lean_inc(v_value_796_);
lean_inc(v_key_795_);
lean_dec(v_x_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
uint8_t v___x_801_; 
v___x_801_ = lean_nat_dec_eq(v_key_795_, v_a_792_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_792_, v_b_793_, v_tail_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 2, v___x_802_);
v___x_804_ = v___x_799_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_key_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_value_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v___x_807_; 
lean_dec(v_value_796_);
lean_dec(v_key_795_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_b_793_);
lean_ctor_set(v___x_799_, 0, v_a_792_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_792_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_b_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_tail_797_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_size_813_; lean_object* v_buckets_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_857_; 
v_size_813_ = lean_ctor_get(v_m_810_, 0);
v_buckets_814_ = lean_ctor_get(v_m_810_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_m_810_);
if (v_isSharedCheck_857_ == 0)
{
v___x_816_ = v_m_810_;
v_isShared_817_ = v_isSharedCheck_857_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_buckets_814_);
lean_inc(v_size_813_);
lean_dec(v_m_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_857_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v_fold_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v_bkt_831_; uint8_t v___x_832_; 
v___x_818_ = lean_array_get_size(v_buckets_814_);
v___x_819_ = lean_uint64_of_nat(v_a_811_);
v___x_820_ = 32ULL;
v___x_821_ = lean_uint64_shift_right(v___x_819_, v___x_820_);
v_fold_822_ = lean_uint64_xor(v___x_819_, v___x_821_);
v___x_823_ = 16ULL;
v___x_824_ = lean_uint64_shift_right(v_fold_822_, v___x_823_);
v___x_825_ = lean_uint64_xor(v_fold_822_, v___x_824_);
v___x_826_ = lean_uint64_to_usize(v___x_825_);
v___x_827_ = lean_usize_of_nat(v___x_818_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_sub(v___x_827_, v___x_828_);
v___x_830_ = lean_usize_land(v___x_826_, v___x_829_);
v_bkt_831_ = lean_array_uget_borrowed(v_buckets_814_, v___x_830_);
v___x_832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_811_, v_bkt_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v_size_x27_834_; lean_object* v___x_835_; lean_object* v_buckets_x27_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v_size_x27_834_ = lean_nat_add(v_size_813_, v___x_833_);
lean_dec(v_size_813_);
lean_inc(v_bkt_831_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v_a_811_);
lean_ctor_set(v___x_835_, 1, v_b_812_);
lean_ctor_set(v___x_835_, 2, v_bkt_831_);
v_buckets_x27_836_ = lean_array_uset(v_buckets_814_, v___x_830_, v___x_835_);
v___x_837_ = lean_unsigned_to_nat(4u);
v___x_838_ = lean_nat_mul(v_size_x27_834_, v___x_837_);
v___x_839_ = lean_unsigned_to_nat(3u);
v___x_840_ = lean_nat_div(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_array_get_size(v_buckets_x27_836_);
v___x_842_ = lean_nat_dec_le(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v_val_843_; lean_object* v___x_845_; 
v_val_843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_836_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v_val_843_);
lean_ctor_set(v___x_816_, 0, v_size_x27_834_);
v___x_845_ = v___x_816_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_size_x27_834_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_val_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_848_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v_buckets_x27_836_);
lean_ctor_set(v___x_816_, 0, v_size_x27_834_);
v___x_848_ = v___x_816_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_size_x27_834_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_buckets_x27_836_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v_buckets_x27_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_inc(v_bkt_831_);
v___x_850_ = lean_box(0);
v_buckets_x27_851_ = lean_array_uset(v_buckets_814_, v___x_830_, v___x_850_);
v___x_852_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_811_, v_b_812_, v_bkt_831_);
v___x_853_ = lean_array_uset(v_buckets_x27_851_, v___x_830_, v___x_852_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_853_);
v___x_855_ = v___x_816_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_size_813_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_858_, lean_object* v_as_859_, size_t v_i_860_, size_t v_stop_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_eq(v_i_860_, v_stop_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_array_uget_borrowed(v_as_859_, v_i_860_);
v___x_864_ = lean_name_eq(v_a_858_, v___x_863_);
if (v___x_864_ == 0)
{
size_t v___x_865_; size_t v___x_866_; 
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_860_, v___x_865_);
v_i_860_ = v___x_866_;
goto _start;
}
else
{
return v___x_864_;
}
}
else
{
uint8_t v___x_868_; 
v___x_868_ = 0;
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_869_, lean_object* v_as_870_, lean_object* v_i_871_, lean_object* v_stop_872_){
_start:
{
size_t v_i_boxed_873_; size_t v_stop_boxed_874_; uint8_t v_res_875_; lean_object* v_r_876_; 
v_i_boxed_873_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_stop_boxed_874_ = lean_unbox_usize(v_stop_872_);
lean_dec(v_stop_872_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_869_, v_as_870_, v_i_boxed_873_, v_stop_boxed_874_);
lean_dec_ref(v_as_870_);
lean_dec(v_a_869_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_array_get_size(v_as_877_);
v___x_881_ = lean_nat_dec_lt(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
return v___x_881_;
}
else
{
if (v___x_881_ == 0)
{
return v___x_881_;
}
else
{
size_t v___x_882_; size_t v___x_883_; uint8_t v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_880_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_878_, v_as_877_, v___x_882_, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_885_, lean_object* v_a_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_as_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_889_, lean_object* v_fallback_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_inc(v_fallback_890_);
return v_fallback_890_;
}
else
{
lean_object* v_key_892_; lean_object* v_value_893_; lean_object* v_tail_894_; uint8_t v___x_895_; 
v_key_892_ = lean_ctor_get(v_x_891_, 0);
v_value_893_ = lean_ctor_get(v_x_891_, 1);
v_tail_894_ = lean_ctor_get(v_x_891_, 2);
v___x_895_ = lean_nat_dec_eq(v_key_892_, v_a_889_);
if (v___x_895_ == 0)
{
v_x_891_ = v_tail_894_;
goto _start;
}
else
{
lean_inc(v_value_893_);
return v_value_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_897_, lean_object* v_fallback_898_, lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_897_, v_fallback_898_, v_x_899_);
lean_dec(v_x_899_);
lean_dec(v_fallback_898_);
lean_dec(v_a_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_901_, lean_object* v_a_902_, lean_object* v_fallback_903_){
_start:
{
lean_object* v_buckets_904_; lean_object* v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_buckets_904_ = lean_ctor_get(v_m_901_, 1);
v___x_905_ = lean_array_get_size(v_buckets_904_);
v___x_906_ = lean_uint64_of_nat(v_a_902_);
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___x_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_905_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v___x_918_ = lean_array_uget_borrowed(v_buckets_904_, v___x_917_);
v___x_919_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_902_, v_fallback_903_, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_920_, lean_object* v_a_921_, lean_object* v_fallback_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_920_, v_a_921_, v_fallback_922_);
lean_dec(v_fallback_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_m_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_){
_start:
{
lean_object* v_a_932_; uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_929_);
return v___x_937_;
}
else
{
lean_object* v_a_938_; lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_a_938_ = lean_array_uget_borrowed(v_as_926_, v_i_928_);
v_fst_939_ = lean_ctor_get(v_a_938_, 0);
v_snd_940_ = lean_ctor_get(v_a_938_, 1);
v___x_941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_929_, v_fst_939_, v___x_941_);
v___x_943_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_942_, v_snd_940_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_inc(v_snd_940_);
v___x_944_ = lean_array_push(v___x_942_, v_snd_940_);
lean_inc(v_fst_939_);
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_929_, v_fst_939_, v___x_944_);
v_a_932_ = v___x_945_;
goto v___jp_931_;
}
else
{
lean_dec(v___x_942_);
v_a_932_ = v_b_929_;
goto v___jp_931_;
}
}
v___jp_931_:
{
size_t v___x_933_; size_t v___x_934_; 
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_928_, v___x_933_);
v_i_928_ = v___x_934_;
v_b_929_ = v_a_932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_946_, lean_object* v_sz_947_, lean_object* v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_){
_start:
{
size_t v_sz_boxed_951_; size_t v_i_boxed_952_; lean_object* v_res_953_; 
v_sz_boxed_951_ = lean_unbox_usize(v_sz_947_);
lean_dec(v_sz_947_);
v_i_boxed_952_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_946_, v_sz_boxed_951_, v_i_boxed_952_, v_b_949_);
lean_dec_ref(v_as_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_putStr_957_; lean_object* v___x_958_; 
v___x_956_ = lean_get_stdout();
v_putStr_957_ = lean_ctor_get(v___x_956_, 4);
lean_inc_ref(v_putStr_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_apply_2(v_putStr_957_, v_s_954_, lean_box(0));
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_962_){
_start:
{
uint32_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = 10;
v___x_965_ = lean_string_push(v_s_962_, v___x_964_);
v___x_966_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_967_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_970_, lean_object* v_a_971_, lean_object* v_b_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_971_, v___x_970_);
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_972_, v___x_970_);
v___x_975_ = lean_string_dec_lt(v___x_973_, v___x_974_);
lean_dec_ref(v___x_974_);
lean_dec_ref(v___x_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
uint8_t v___x_11497__boxed_979_; uint8_t v_res_980_; lean_object* v_r_981_; 
v___x_11497__boxed_979_ = lean_unbox(v___x_976_);
v_res_980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11497__boxed_979_, v_a_977_, v_b_978_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v_hi_984_, lean_object* v_pivot_985_, lean_object* v_as_986_, lean_object* v_i_987_, lean_object* v_k_988_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_lt(v_k_988_, v_hi_984_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_k_988_);
lean_dec(v_pivot_985_);
v___x_990_ = lean_array_fswap(v_as_986_, v_i_987_, v_hi_984_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_i_987_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
else
{
uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_992_ = lean_nat_dec_lt(v___x_982_, v___x_983_);
v___x_993_ = lean_array_fget_borrowed(v_as_986_, v_k_988_);
lean_inc(v___x_993_);
v___x_994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_993_, v___x_992_);
lean_inc(v_pivot_985_);
v___x_995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_985_, v___x_992_);
v___x_996_ = lean_string_dec_lt(v___x_994_, v___x_995_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_994_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_k_988_, v___x_997_);
lean_dec(v_k_988_);
v_k_988_ = v___x_998_;
goto _start;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = lean_array_fswap(v_as_986_, v_i_987_, v_k_988_);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_i_987_, v___x_1001_);
lean_dec(v_i_987_);
v___x_1003_ = lean_nat_add(v_k_988_, v___x_1001_);
lean_dec(v_k_988_);
v_as_986_ = v___x_1000_;
v_i_987_ = v___x_1002_;
v_k_988_ = v___x_1003_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v_hi_1007_, lean_object* v_pivot_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1005_, v___x_1006_, v_hi_1007_, v_pivot_1008_, v_as_1009_, v_i_1010_, v_k_1011_);
lean_dec(v_hi_1007_);
lean_dec(v___x_1006_);
lean_dec(v___x_1005_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_1013_, lean_object* v___x_1014_, lean_object* v_n_1015_, lean_object* v_as_1016_, lean_object* v_lo_1017_, lean_object* v_hi_1018_){
_start:
{
lean_object* v___y_1020_; uint8_t v___x_1030_; 
v___x_1030_ = lean_nat_dec_lt(v_lo_1017_, v_hi_1018_);
if (v___x_1030_ == 0)
{
lean_dec(v_lo_1017_);
return v_as_1016_;
}
else
{
uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_mid_1034_; lean_object* v___y_1036_; lean_object* v___y_1042_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1031_ = lean_nat_dec_lt(v___x_1013_, v___x_1014_);
v___x_1032_ = lean_nat_add(v_lo_1017_, v_hi_1018_);
v___x_1033_ = lean_unsigned_to_nat(1u);
v_mid_1034_ = lean_nat_shiftr(v___x_1032_, v___x_1033_);
lean_dec(v___x_1032_);
v___x_1047_ = lean_array_fget_borrowed(v_as_1016_, v_mid_1034_);
v___x_1048_ = lean_array_fget_borrowed(v_as_1016_, v_lo_1017_);
lean_inc(v___x_1048_);
lean_inc(v___x_1047_);
v___x_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1031_, v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
v___y_1042_ = v_as_1016_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_array_fswap(v_as_1016_, v_lo_1017_, v_mid_1034_);
v___y_1042_ = v___x_1050_;
goto v___jp_1041_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_array_fget_borrowed(v___y_1036_, v_mid_1034_);
v___x_1038_ = lean_array_fget_borrowed(v___y_1036_, v_hi_1018_);
lean_inc(v___x_1038_);
lean_inc(v___x_1037_);
v___x_1039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1031_, v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_mid_1034_);
v___y_1020_ = v___y_1036_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_array_fswap(v___y_1036_, v_mid_1034_, v_hi_1018_);
lean_dec(v_mid_1034_);
v___y_1020_ = v___x_1040_;
goto v___jp_1019_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_array_fget_borrowed(v___y_1042_, v_hi_1018_);
v___x_1044_ = lean_array_fget_borrowed(v___y_1042_, v_lo_1017_);
lean_inc(v___x_1044_);
lean_inc(v___x_1043_);
v___x_1045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1031_, v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
v___y_1036_ = v___y_1042_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_fswap(v___y_1042_, v_lo_1017_, v_hi_1018_);
v___y_1036_ = v___x_1046_;
goto v___jp_1035_;
}
}
}
v___jp_1019_:
{
lean_object* v_pivot_1021_; lean_object* v___x_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; uint8_t v___x_1025_; 
v_pivot_1021_ = lean_array_fget(v___y_1020_, v_hi_1018_);
lean_inc_n(v_lo_1017_, 2);
v___x_1022_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1013_, v___x_1014_, v_hi_1018_, v_pivot_1021_, v___y_1020_, v_lo_1017_, v_lo_1017_);
v_fst_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_fst_1023_);
v_snd_1024_ = lean_ctor_get(v___x_1022_, 1);
lean_inc(v_snd_1024_);
lean_dec_ref(v___x_1022_);
v___x_1025_ = lean_nat_dec_le(v_hi_1018_, v_fst_1023_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1013_, v___x_1014_, v_n_1015_, v_snd_1024_, v_lo_1017_, v_fst_1023_);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_fst_1023_, v___x_1027_);
lean_dec(v_fst_1023_);
v_as_1016_ = v___x_1026_;
v_lo_1017_ = v___x_1028_;
goto _start;
}
else
{
lean_dec(v_fst_1023_);
lean_dec(v_lo_1017_);
return v_snd_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v_n_1053_, lean_object* v_as_1054_, lean_object* v_lo_1055_, lean_object* v_hi_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1051_, v___x_1052_, v_n_1053_, v_as_1054_, v_lo_1055_, v_hi_1056_);
lean_dec(v_hi_1056_);
lean_dec(v_n_1053_);
lean_dec(v___x_1052_);
lean_dec(v___x_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1060_, lean_object* v___x_1061_, lean_object* v___x_1062_, size_t v_sz_1063_, size_t v_i_1064_, lean_object* v_bs_1065_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_lt(v_i_1064_, v_sz_1063_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v___x_1060_);
return v_bs_1065_;
}
else
{
uint8_t v___x_1067_; lean_object* v_v_1068_; lean_object* v___x_1069_; lean_object* v_bs_x27_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1067_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
v_v_1068_ = lean_array_uget(v_bs_1065_, v_i_1064_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v_bs_x27_1070_ = lean_array_uset(v_bs_1065_, v_i_1064_, v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1060_);
v___x_1072_ = lean_string_append(v___x_1060_, v___x_1071_);
v___x_1073_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1068_, v___x_1067_);
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1076_ = lean_string_append(v___x_1074_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1078_ = lean_string_append(v___x_1076_, v___x_1077_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1064_, v___x_1079_);
v___x_1081_ = lean_array_uset(v_bs_x27_1070_, v_i_1064_, v___x_1078_);
v_i_1064_ = v___x_1080_;
v_bs_1065_ = v___x_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v_sz_1086_, lean_object* v_i_1087_, lean_object* v_bs_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1086_);
lean_dec(v_sz_1086_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1083_, v___x_1084_, v___x_1085_, v_sz_boxed_1089_, v_i_boxed_1090_, v_bs_1088_);
lean_dec(v___x_1085_);
lean_dec(v___x_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_b_1095_){
_start:
{
lean_object* v_a_1098_; uint8_t v___x_1102_; 
v___x_1102_ = lean_usize_dec_lt(v_i_1094_, v_sz_1093_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_b_1095_);
return v___x_1103_;
}
else
{
lean_object* v_a_1104_; lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1147_; 
v_a_1104_ = lean_array_uget_borrowed(v_as_1092_, v_i_1094_);
v_fst_1105_ = lean_ctor_get(v_a_1104_, 0);
v_snd_1106_ = lean_ctor_get(v_a_1104_, 1);
v_fst_1107_ = lean_ctor_get(v_b_1095_, 0);
v_snd_1108_ = lean_ctor_get(v_b_1095_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_b_1095_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1110_ = v_b_1095_;
v_isShared_1111_ = v_isSharedCheck_1147_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_snd_1108_);
lean_inc(v_fst_1107_);
lean_dec(v_b_1095_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1147_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_sub(v_fst_1105_, v___x_1112_);
v___x_1114_ = lean_array_get_size(v_fst_1107_);
v___x_1115_ = lean_nat_dec_lt(v___x_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v___x_1113_);
if (v_isShared_1111_ == 0)
{
v___x_1117_ = v___x_1110_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_fst_1107_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_snd_1108_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v_a_1098_ = v___x_1117_;
goto v___jp_1097_;
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; lean_object* v___x_1136_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___x_1141_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_array_fget_borrowed(v_fst_1107_, v___x_1113_);
v___x_1121_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1120_);
v___x_1136_ = lean_array_get_size(v_snd_1106_);
v___x_1141_ = lean_nat_dec_eq(v___x_1136_, v___x_1119_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___y_1144_; uint8_t v___x_1146_; 
v___x_1142_ = lean_nat_sub(v___x_1136_, v___x_1112_);
v___x_1146_ = lean_nat_dec_le(v___x_1119_, v___x_1142_);
if (v___x_1146_ == 0)
{
lean_inc(v___x_1142_);
v___y_1144_ = v___x_1142_;
goto v___jp_1143_;
}
else
{
v___y_1144_ = v___x_1119_;
goto v___jp_1143_;
}
v___jp_1143_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_le(v___y_1144_, v___x_1142_);
if (v___x_1145_ == 0)
{
lean_dec(v___x_1142_);
lean_inc(v___y_1144_);
v___y_1138_ = v___y_1144_;
v___y_1139_ = v___y_1144_;
goto v___jp_1137_;
}
else
{
v___y_1138_ = v___y_1144_;
v___y_1139_ = v___x_1142_;
goto v___jp_1137_;
}
}
}
else
{
lean_inc(v_snd_1106_);
v___y_1123_ = v_snd_1106_;
goto v___jp_1122_;
}
v___jp_1122_:
{
size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v_sz_1124_ = lean_array_size(v___y_1123_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1121_, v___x_1113_, v___x_1114_, v_sz_1124_, v___x_1125_, v___y_1123_);
lean_inc(v___x_1113_);
v___x_1127_ = l_Array_extract___redArg(v_fst_1107_, v___x_1119_, v___x_1113_);
v___x_1128_ = l_Array_append___redArg(v___x_1127_, v___x_1126_);
v___x_1129_ = l_Array_extract___redArg(v_fst_1107_, v___x_1113_, v___x_1114_);
lean_dec(v_fst_1107_);
v___x_1130_ = l_Array_append___redArg(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_array_get_size(v___x_1126_);
lean_dec_ref(v___x_1126_);
v___x_1132_ = lean_nat_add(v_snd_1108_, v___x_1131_);
lean_dec(v_snd_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v___x_1132_);
lean_ctor_set(v___x_1110_, 0, v___x_1130_);
v___x_1134_ = v___x_1110_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v_a_1098_ = v___x_1134_;
goto v___jp_1097_;
}
}
v___jp_1137_:
{
lean_object* v___x_1140_; 
lean_inc(v_snd_1106_);
v___x_1140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1113_, v___x_1114_, v___x_1136_, v_snd_1106_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
v___y_1123_ = v___x_1140_;
goto v___jp_1122_;
}
}
}
}
v___jp_1097_:
{
size_t v___x_1099_; size_t v___x_1100_; 
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1094_, v___x_1099_);
v_i_1094_ = v___x_1100_;
v_b_1095_ = v_a_1098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_){
_start:
{
size_t v_sz_boxed_1153_; size_t v_i_boxed_1154_; lean_object* v_res_1155_; 
v_sz_boxed_1153_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1148_, v_sz_boxed_1153_, v_i_boxed_1154_, v_b_1151_);
lean_dec_ref(v_as_1148_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_unsigned_to_nat(16u);
v___x_1158_ = lean_mk_array(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v_a_1178_; uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_b_1175_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v_snd_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1294_; 
v_a_1184_ = lean_array_uget_borrowed(v_as_1172_, v_i_1174_);
v_snd_1185_ = lean_ctor_get(v_a_1184_, 1);
lean_inc(v_snd_1185_);
v_fst_1186_ = lean_ctor_get(v_snd_1185_, 0);
v_snd_1187_ = lean_ctor_get(v_snd_1185_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_snd_1185_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1189_ = v_snd_1185_;
v_isShared_1190_ = v_isSharedCheck_1294_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_snd_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1294_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_1193_ = lean_array_size(v_snd_1187_);
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1187_, v_sz_1193_, v___x_1194_, v___x_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___x_1211_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_box(0);
v___x_1211_ = l_IO_FS_readFile(v_fst_1186_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_size_1216_; lean_object* v_buckets_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; size_t v_sz_1220_; lean_object* v___x_1221_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1265_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
lean_dec(v_snd_1187_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_n(v_a_1212_, 2);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = lean_string_utf8_byte_size(v_a_1212_);
v___x_1214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1191_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
v___x_1215_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_1214_);
v_size_1216_ = lean_ctor_get(v_a_1196_, 0);
lean_inc(v_size_1216_);
v_buckets_1217_ = lean_ctor_get(v_a_1196_, 1);
lean_inc_ref(v_buckets_1217_);
lean_dec(v_a_1196_);
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1219_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1212_, v___x_1214_, v___x_1213_, v___x_1215_, v___x_1218_);
lean_dec_ref_known(v___x_1214_, 3);
v_sz_1220_ = lean_array_size(v___x_1219_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1220_, v___x_1194_, v___x_1219_);
v___x_1271_ = lean_mk_empty_array_with_capacity(v_size_1216_);
lean_dec(v_size_1216_);
v___x_1272_ = lean_array_get_size(v_buckets_1217_);
v___x_1273_ = lean_nat_dec_lt(v___x_1191_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v_buckets_1217_);
v___y_1265_ = v___x_1271_;
goto v___jp_1264_;
}
else
{
size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_usize_of_nat(v___x_1272_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1217_, v___x_1194_, v___x_1274_, v___x_1271_);
lean_dec_ref(v_buckets_1217_);
v___y_1265_ = v___x_1275_;
goto v___jp_1264_;
}
v___jp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1191_);
lean_ctor_set(v___x_1189_, 0, v___x_1221_);
v___x_1226_ = v___x_1189_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1191_);
v___x_1226_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
size_t v_sz_1227_; lean_object* v___x_1228_; 
v_sz_1227_ = lean_array_size(v___y_1224_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1224_, v_sz_1227_, v___x_1194_, v___x_1226_);
lean_dec_ref(v___y_1224_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_fst_1230_; lean_object* v_snd_1231_; uint8_t v___x_1232_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v_fst_1230_ = lean_ctor_get(v_a_1229_, 0);
lean_inc(v_fst_1230_);
v_snd_1231_ = lean_ctor_get(v_a_1229_, 1);
lean_inc(v_snd_1231_);
lean_dec(v_a_1229_);
v___x_1232_ = lean_nat_dec_lt(v___x_1191_, v_snd_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec(v_fst_1186_);
v_a_1178_ = v___x_1197_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1231_);
v___x_1234_ = l_Nat_reprFast(v_snd_1231_);
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v___x_1238_ = lean_nat_dec_eq(v_snd_1231_, v___y_1223_);
lean_dec(v_snd_1231_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1199_ = v___x_1237_;
v___y_1200_ = v_fst_1230_;
v___y_1201_ = v___x_1239_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1240_; 
v___x_1240_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1199_ = v___x_1237_;
v___y_1200_ = v_fst_1230_;
v___y_1201_ = v___x_1240_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_fst_1186_);
v_a_1241_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1228_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1228_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1256_; 
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1253_, v___y_1251_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec(v___y_1253_);
v___y_1223_ = v___y_1252_;
v___y_1224_ = v___x_1256_;
goto v___jp_1222_;
}
v___jp_1257_:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_le(v___y_1262_, v___y_1259_);
if (v___x_1263_ == 0)
{
lean_dec(v___y_1259_);
lean_inc(v___y_1262_);
v___y_1251_ = v___y_1258_;
v___y_1252_ = v___y_1260_;
v___y_1253_ = v___y_1261_;
v___y_1254_ = v___y_1262_;
v___y_1255_ = v___y_1262_;
goto v___jp_1250_;
}
else
{
v___y_1251_ = v___y_1258_;
v___y_1252_ = v___y_1260_;
v___y_1253_ = v___y_1261_;
v___y_1254_ = v___y_1262_;
v___y_1255_ = v___y_1259_;
goto v___jp_1250_;
}
}
v___jp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_array_get_size(v___y_1265_);
v___x_1268_ = lean_nat_dec_eq(v___x_1267_, v___x_1191_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_nat_sub(v___x_1267_, v___x_1266_);
v___x_1270_ = lean_nat_dec_le(v___x_1191_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_inc(v___x_1269_);
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___x_1269_;
v___y_1260_ = v___x_1266_;
v___y_1261_ = v___x_1267_;
v___y_1262_ = v___x_1269_;
goto v___jp_1257_;
}
else
{
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___x_1269_;
v___y_1260_ = v___x_1266_;
v___y_1261_ = v___x_1267_;
v___y_1262_ = v___x_1191_;
goto v___jp_1257_;
}
}
else
{
v___y_1223_ = v___x_1266_;
v___y_1224_ = v___y_1265_;
goto v___jp_1222_;
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref_known(v___x_1211_, 1);
lean_dec(v_a_1196_);
lean_del_object(v___x_1189_);
v___x_1276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1277_ = lean_string_append(v___x_1276_, v_fst_1186_);
lean_dec(v_fst_1186_);
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1279_ = lean_string_append(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_array_get_size(v_snd_1187_);
lean_dec(v_snd_1187_);
v___x_1281_ = l_Nat_reprFast(v___x_1280_);
v___x_1282_ = lean_string_append(v___x_1279_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
v___x_1285_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref_known(v___x_1285_, 1);
v_a_1178_ = v___x_1197_;
goto v___jp_1177_;
}
else
{
return v___x_1285_;
}
}
v___jp_1198_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1202_ = lean_string_append(v___y_1199_, v___y_1201_);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_string_append(v___x_1204_, v_fst_1186_);
v___x_1206_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_1208_ = lean_array_to_list(v___y_1200_);
v___x_1209_ = l_String_intercalate(v___x_1207_, v___x_1208_);
v___x_1210_ = l_IO_FS_writeFile(v_fst_1186_, v___x_1209_);
lean_dec_ref(v___x_1209_);
lean_dec(v_fst_1186_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec_ref_known(v___x_1210_, 1);
v_a_1178_ = v___x_1197_;
goto v___jp_1177_;
}
else
{
return v___x_1210_;
}
}
else
{
lean_dec(v___y_1200_);
lean_dec(v_fst_1186_);
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1189_);
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
v_a_1286_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1195_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1195_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
v___jp_1177_:
{
size_t v___x_1179_; size_t v___x_1180_; 
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_add(v_i_1174_, v___x_1179_);
v_i_1174_ = v___x_1180_;
v_b_1175_ = v_a_1178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_){
_start:
{
size_t v_sz_boxed_1300_; size_t v_i_boxed_1301_; lean_object* v_res_1302_; 
v_sz_boxed_1300_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1301_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1295_, v_sz_boxed_1300_, v_i_boxed_1301_, v_b_1298_);
lean_dec_ref(v_as_1295_);
return v_res_1302_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = 0;
return v___x_1305_;
}
else
{
lean_object* v_key_1306_; lean_object* v_tail_1307_; uint8_t v___x_1308_; 
v_key_1306_ = lean_ctor_get(v_x_1304_, 0);
v_tail_1307_ = lean_ctor_get(v_x_1304_, 2);
v___x_1308_ = lean_string_dec_eq(v_key_1306_, v_a_1303_);
if (v___x_1308_ == 0)
{
v_x_1304_ = v_tail_1307_;
goto _start;
}
else
{
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1310_, lean_object* v_x_1311_){
_start:
{
uint8_t v_res_1312_; lean_object* v_r_1313_; 
v_res_1312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1310_, v_x_1311_);
lean_dec(v_x_1311_);
lean_dec_ref(v_a_1310_);
v_r_1313_ = lean_box(v_res_1312_);
return v_r_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1314_, lean_object* v_b_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
lean_dec(v_b_1315_);
lean_dec_ref(v_a_1314_);
return v_x_1316_;
}
else
{
lean_object* v_key_1317_; lean_object* v_value_1318_; lean_object* v_tail_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1331_; 
v_key_1317_ = lean_ctor_get(v_x_1316_, 0);
v_value_1318_ = lean_ctor_get(v_x_1316_, 1);
v_tail_1319_ = lean_ctor_get(v_x_1316_, 2);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_x_1316_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1321_ = v_x_1316_;
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_tail_1319_);
lean_inc(v_value_1318_);
lean_inc(v_key_1317_);
lean_dec(v_x_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_string_dec_eq(v_key_1317_, v_a_1314_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1314_, v_b_1315_, v_tail_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 2, v___x_1324_);
v___x_1326_ = v___x_1321_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_key_1317_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_value_1318_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_value_1318_);
lean_dec(v_key_1317_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v_b_1315_);
lean_ctor_set(v___x_1321_, 0, v_a_1314_);
v___x_1329_ = v___x_1321_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1314_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_b_1315_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_tail_1319_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
if (lean_obj_tag(v_x_1333_) == 0)
{
return v_x_1332_;
}
else
{
lean_object* v_key_1334_; lean_object* v_value_1335_; lean_object* v_tail_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1359_; 
v_key_1334_ = lean_ctor_get(v_x_1333_, 0);
v_value_1335_ = lean_ctor_get(v_x_1333_, 1);
v_tail_1336_ = lean_ctor_get(v_x_1333_, 2);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1338_ = v_x_1333_;
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_tail_1336_);
lean_inc(v_value_1335_);
lean_inc(v_key_1334_);
lean_dec(v_x_1333_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; uint64_t v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v_fold_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1340_ = lean_array_get_size(v_x_1332_);
v___x_1341_ = lean_string_hash(v_key_1334_);
v___x_1342_ = 32ULL;
v___x_1343_ = lean_uint64_shift_right(v___x_1341_, v___x_1342_);
v_fold_1344_ = lean_uint64_xor(v___x_1341_, v___x_1343_);
v___x_1345_ = 16ULL;
v___x_1346_ = lean_uint64_shift_right(v_fold_1344_, v___x_1345_);
v___x_1347_ = lean_uint64_xor(v_fold_1344_, v___x_1346_);
v___x_1348_ = lean_uint64_to_usize(v___x_1347_);
v___x_1349_ = lean_usize_of_nat(v___x_1340_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_sub(v___x_1349_, v___x_1350_);
v___x_1352_ = lean_usize_land(v___x_1348_, v___x_1351_);
v___x_1353_ = lean_array_uget_borrowed(v_x_1332_, v___x_1352_);
lean_inc(v___x_1353_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 2, v___x_1353_);
v___x_1355_ = v___x_1338_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_key_1334_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_value_1335_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_array_uset(v_x_1332_, v___x_1352_, v___x_1355_);
v_x_1332_ = v___x_1356_;
v_x_1333_ = v_tail_1336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1360_, lean_object* v_source_1361_, lean_object* v_target_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_array_get_size(v_source_1361_);
v___x_1364_ = lean_nat_dec_lt(v_i_1360_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec_ref(v_source_1361_);
lean_dec(v_i_1360_);
return v_target_1362_;
}
else
{
lean_object* v_es_1365_; lean_object* v___x_1366_; lean_object* v_source_1367_; lean_object* v_target_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_es_1365_ = lean_array_fget(v_source_1361_, v_i_1360_);
v___x_1366_ = lean_box(0);
v_source_1367_ = lean_array_fset(v_source_1361_, v_i_1360_, v___x_1366_);
v_target_1368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1362_, v_es_1365_);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_i_1360_, v___x_1369_);
lean_dec(v_i_1360_);
v_i_1360_ = v___x_1370_;
v_source_1361_ = v_source_1367_;
v_target_1362_ = v_target_1368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_nbuckets_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1373_ = lean_array_get_size(v_data_1372_);
v___x_1374_ = lean_unsigned_to_nat(2u);
v_nbuckets_1375_ = lean_nat_mul(v___x_1373_, v___x_1374_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_mk_array(v_nbuckets_1375_, v___x_1377_);
v___x_1379_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1376_, v_data_1372_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_){
_start:
{
lean_object* v_size_1383_; lean_object* v_buckets_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1427_; 
v_size_1383_ = lean_ctor_get(v_m_1380_, 0);
v_buckets_1384_ = lean_ctor_get(v_m_1380_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_m_1380_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1386_ = v_m_1380_;
v_isShared_1387_ = v_isSharedCheck_1427_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_buckets_1384_);
lean_inc(v_size_1383_);
lean_dec(v_m_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1427_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; uint64_t v___x_1389_; uint64_t v___x_1390_; uint64_t v___x_1391_; uint64_t v_fold_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v_bkt_1401_; uint8_t v___x_1402_; 
v___x_1388_ = lean_array_get_size(v_buckets_1384_);
v___x_1389_ = lean_string_hash(v_a_1381_);
v___x_1390_ = 32ULL;
v___x_1391_ = lean_uint64_shift_right(v___x_1389_, v___x_1390_);
v_fold_1392_ = lean_uint64_xor(v___x_1389_, v___x_1391_);
v___x_1393_ = 16ULL;
v___x_1394_ = lean_uint64_shift_right(v_fold_1392_, v___x_1393_);
v___x_1395_ = lean_uint64_xor(v_fold_1392_, v___x_1394_);
v___x_1396_ = lean_uint64_to_usize(v___x_1395_);
v___x_1397_ = lean_usize_of_nat(v___x_1388_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_sub(v___x_1397_, v___x_1398_);
v___x_1400_ = lean_usize_land(v___x_1396_, v___x_1399_);
v_bkt_1401_ = lean_array_uget_borrowed(v_buckets_1384_, v___x_1400_);
v___x_1402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1381_, v_bkt_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v_size_x27_1404_; lean_object* v___x_1405_; lean_object* v_buckets_x27_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1403_ = lean_unsigned_to_nat(1u);
v_size_x27_1404_ = lean_nat_add(v_size_1383_, v___x_1403_);
lean_dec(v_size_1383_);
lean_inc(v_bkt_1401_);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v_a_1381_);
lean_ctor_set(v___x_1405_, 1, v_b_1382_);
lean_ctor_set(v___x_1405_, 2, v_bkt_1401_);
v_buckets_x27_1406_ = lean_array_uset(v_buckets_1384_, v___x_1400_, v___x_1405_);
v___x_1407_ = lean_unsigned_to_nat(4u);
v___x_1408_ = lean_nat_mul(v_size_x27_1404_, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = lean_nat_div(v___x_1408_, v___x_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_array_get_size(v_buckets_x27_1406_);
v___x_1412_ = lean_nat_dec_le(v___x_1410_, v___x_1411_);
lean_dec(v___x_1410_);
if (v___x_1412_ == 0)
{
lean_object* v_val_1413_; lean_object* v___x_1415_; 
v_val_1413_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1406_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_val_1413_);
lean_ctor_set(v___x_1386_, 0, v_size_x27_1404_);
v___x_1415_ = v___x_1386_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_size_x27_1404_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_val_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v___x_1418_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_buckets_x27_1406_);
lean_ctor_set(v___x_1386_, 0, v_size_x27_1404_);
v___x_1418_ = v___x_1386_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_size_x27_1404_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_buckets_x27_1406_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1420_; lean_object* v_buckets_x27_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_inc(v_bkt_1401_);
v___x_1420_ = lean_box(0);
v_buckets_x27_1421_ = lean_array_uset(v_buckets_1384_, v___x_1400_, v___x_1420_);
v___x_1422_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1381_, v_b_1382_, v_bkt_1401_);
v___x_1423_ = lean_array_uset(v_buckets_x27_1421_, v___x_1400_, v___x_1422_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1423_);
v___x_1425_ = v___x_1386_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_size_1383_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1428_, lean_object* v_fallback_1429_, lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_inc(v_fallback_1429_);
return v_fallback_1429_;
}
else
{
lean_object* v_key_1431_; lean_object* v_value_1432_; lean_object* v_tail_1433_; uint8_t v___x_1434_; 
v_key_1431_ = lean_ctor_get(v_x_1430_, 0);
v_value_1432_ = lean_ctor_get(v_x_1430_, 1);
v_tail_1433_ = lean_ctor_get(v_x_1430_, 2);
v___x_1434_ = lean_string_dec_eq(v_key_1431_, v_a_1428_);
if (v___x_1434_ == 0)
{
v_x_1430_ = v_tail_1433_;
goto _start;
}
else
{
lean_inc(v_value_1432_);
return v_value_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1436_, lean_object* v_fallback_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1436_, v_fallback_1437_, v_x_1438_);
lean_dec(v_x_1438_);
lean_dec(v_fallback_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1440_, lean_object* v_a_1441_, lean_object* v_fallback_1442_){
_start:
{
lean_object* v_buckets_1443_; lean_object* v___x_1444_; uint64_t v___x_1445_; uint64_t v___x_1446_; uint64_t v___x_1447_; uint64_t v_fold_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_buckets_1443_ = lean_ctor_get(v_m_1440_, 1);
v___x_1444_ = lean_array_get_size(v_buckets_1443_);
v___x_1445_ = lean_string_hash(v_a_1441_);
v___x_1446_ = 32ULL;
v___x_1447_ = lean_uint64_shift_right(v___x_1445_, v___x_1446_);
v_fold_1448_ = lean_uint64_xor(v___x_1445_, v___x_1447_);
v___x_1449_ = 16ULL;
v___x_1450_ = lean_uint64_shift_right(v_fold_1448_, v___x_1449_);
v___x_1451_ = lean_uint64_xor(v_fold_1448_, v___x_1450_);
v___x_1452_ = lean_uint64_to_usize(v___x_1451_);
v___x_1453_ = lean_usize_of_nat(v___x_1444_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_sub(v___x_1453_, v___x_1454_);
v___x_1456_ = lean_usize_land(v___x_1452_, v___x_1455_);
v___x_1457_ = lean_array_uget_borrowed(v_buckets_1443_, v___x_1456_);
v___x_1458_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1441_, v_fallback_1442_, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1459_, lean_object* v_a_1460_, lean_object* v_fallback_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1459_, v_a_1460_, v_fallback_1461_);
lean_dec(v_fallback_1461_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_m_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_b_1468_);
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v_file_1473_; lean_object* v_pos_1474_; lean_object* v_option_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1501_; 
v_a_1472_ = lean_array_uget_borrowed(v_as_1465_, v_i_1467_);
v_file_1473_ = lean_ctor_get(v_a_1472_, 0);
v_pos_1474_ = lean_ctor_get(v_a_1472_, 1);
lean_inc_ref(v_pos_1474_);
v_option_1475_ = lean_ctor_get(v_a_1472_, 2);
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1473_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_file_1473_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1468_, v_file_1473_, v___x_1477_);
lean_dec_ref_known(v___x_1477_, 2);
v_fst_1479_ = lean_ctor_get(v___x_1478_, 0);
v_snd_1480_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1482_ = v___x_1478_;
v_isShared_1483_ = v_isSharedCheck_1501_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_inc(v_fst_1479_);
lean_dec(v___x_1478_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1501_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_line_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1499_; 
v_line_1484_ = lean_ctor_get(v_pos_1474_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_pos_1474_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v_pos_1474_, 1);
lean_dec(v_unused_1500_);
v___x_1486_ = v_pos_1474_;
v_isShared_1487_ = v_isSharedCheck_1499_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_line_1484_);
lean_dec(v_pos_1474_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1499_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
lean_inc(v_option_1475_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v_option_1475_);
lean_ctor_set(v___x_1482_, 0, v_line_1484_);
v___x_1489_ = v___x_1482_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_line_1484_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_option_1475_);
v___x_1489_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_array_push(v_snd_1480_, v___x_1489_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1490_);
lean_ctor_set(v___x_1486_, 0, v_fst_1479_);
v___x_1492_ = v___x_1486_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_fst_1479_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; 
lean_inc_ref(v_file_1473_);
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1468_, v_file_1473_, v___x_1492_);
v___x_1494_ = ((size_t)1ULL);
v___x_1495_ = lean_usize_add(v_i_1467_, v___x_1494_);
v_i_1467_ = v___x_1495_;
v_b_1468_ = v___x_1493_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1502_, lean_object* v_sz_1503_, lean_object* v_i_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_){
_start:
{
size_t v_sz_boxed_1507_; size_t v_i_boxed_1508_; lean_object* v_res_1509_; 
v_sz_boxed_1507_ = lean_unbox_usize(v_sz_1503_);
lean_dec(v_sz_1503_);
v_i_boxed_1508_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1502_, v_sz_boxed_1507_, v_i_boxed_1508_, v_b_1505_);
lean_dec_ref(v_as_1502_);
return v_res_1509_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_unsigned_to_nat(16u);
v___x_1512_ = lean_mk_array(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_byFile_1515_; 
v___x_1513_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1514_ = lean_unsigned_to_nat(0u);
v_byFile_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1515_, 0, v___x_1514_);
lean_ctor_set(v_byFile_1515_, 1, v___x_1513_);
return v_byFile_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v_byFile_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v_byFile_1519_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1520_ = lean_array_size(v_records_1516_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1516_, v_sz_1520_, v___x_1521_, v_byFile_1519_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___y_1525_; lean_object* v_size_1537_; lean_object* v_buckets_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v_size_1537_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_size_1537_);
v_buckets_1538_ = lean_ctor_get(v_a_1523_, 1);
lean_inc_ref(v_buckets_1538_);
lean_dec(v_a_1523_);
v___x_1539_ = lean_mk_empty_array_with_capacity(v_size_1537_);
lean_dec(v_size_1537_);
v___x_1540_ = lean_array_get_size(v_buckets_1538_);
v___x_1541_ = lean_nat_dec_lt(v___x_1518_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec_ref(v_buckets_1538_);
v___y_1525_ = v___x_1539_;
goto v___jp_1524_;
}
else
{
size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_usize_of_nat(v___x_1540_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1538_, v___x_1521_, v___x_1542_, v___x_1539_);
lean_dec_ref(v_buckets_1538_);
v___y_1525_ = v___x_1543_;
goto v___jp_1524_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; size_t v_sz_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_box(0);
v_sz_1527_ = lean_array_size(v___y_1525_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1525_, v_sz_1527_, v___x_1521_, v___x_1526_);
lean_dec_ref(v___y_1525_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1528_, 0);
lean_dec(v_unused_1536_);
v___x_1530_ = v___x_1528_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v___x_1528_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1526_);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1526_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
return v___x_1528_;
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_a_1544_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1522_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1522_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1552_);
lean_dec_ref(v_records_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1555_, lean_object* v_m_1556_, lean_object* v_a_1557_, lean_object* v_fallback_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1556_, v_a_1557_, v_fallback_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_, lean_object* v_fallback_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1560_, v_m_1561_, v_a_1562_, v_fallback_1563_);
lean_dec(v_fallback_1563_);
lean_dec_ref(v_a_1562_);
lean_dec_ref(v_m_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1565_, lean_object* v_m_1566_, lean_object* v_a_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1566_, v_a_1567_, v_b_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_a_1572_, lean_object* v_fallback_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1571_, v_a_1572_, v_fallback_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1575_, lean_object* v_m_1576_, lean_object* v_a_1577_, lean_object* v_fallback_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1575_, v_m_1576_, v_a_1577_, v_fallback_1578_);
lean_dec(v_fallback_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_m_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1580_, lean_object* v_m_1581_, lean_object* v_a_1582_, lean_object* v_b_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1581_, v_a_1582_, v_b_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1585_, lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v_inst_1588_, lean_object* v_R_1589_, lean_object* v_a_1590_, lean_object* v_b_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1585_, v___x_1586_, v___x_1587_, v_a_1590_, v_b_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v_inst_1596_, lean_object* v_R_1597_, lean_object* v_a_1598_, lean_object* v_b_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1593_, v___x_1594_, v___x_1595_, v_inst_1596_, v_R_1597_, v_a_1598_, v_b_1599_);
lean_dec_ref(v___x_1594_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_n_1603_, lean_object* v_as_1604_, lean_object* v_lo_1605_, lean_object* v_hi_1606_, lean_object* v_w_1607_, lean_object* v_hlo_1608_, lean_object* v_hhi_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1601_, v___x_1602_, v_n_1603_, v_as_1604_, v_lo_1605_, v_hi_1606_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v_n_1613_, lean_object* v_as_1614_, lean_object* v_lo_1615_, lean_object* v_hi_1616_, lean_object* v_w_1617_, lean_object* v_hlo_1618_, lean_object* v_hhi_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1611_, v___x_1612_, v_n_1613_, v_as_1614_, v_lo_1615_, v_hi_1616_, v_w_1617_, v_hlo_1618_, v_hhi_1619_);
lean_dec(v_hi_1616_);
lean_dec(v_n_1613_);
lean_dec(v___x_1612_);
lean_dec(v___x_1611_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1621_, lean_object* v_as_1622_, lean_object* v_lo_1623_, lean_object* v_hi_1624_, lean_object* v_w_1625_, lean_object* v_hlo_1626_, lean_object* v_hhi_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1621_, v_as_1622_, v_lo_1623_, v_hi_1624_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1629_, lean_object* v_as_1630_, lean_object* v_lo_1631_, lean_object* v_hi_1632_, lean_object* v_w_1633_, lean_object* v_hlo_1634_, lean_object* v_hhi_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1629_, v_as_1630_, v_lo_1631_, v_hi_1632_, v_w_1633_, v_hlo_1634_, v_hhi_1635_);
lean_dec(v_hi_1632_);
lean_dec(v_n_1629_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_fallback_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1638_, v_fallback_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_a_1643_, lean_object* v_fallback_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1642_, v_a_1643_, v_fallback_1644_, v_x_1645_);
lean_dec(v_x_1645_);
lean_dec(v_fallback_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1651_, v_a_1652_, v_x_1653_);
lean_dec(v_x_1653_);
lean_dec_ref(v_a_1652_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1656_, lean_object* v_data_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_, lean_object* v_x_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1660_, v_b_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1664_, lean_object* v_a_1665_, lean_object* v_fallback_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1665_, v_fallback_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1669_, lean_object* v_a_1670_, lean_object* v_fallback_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1669_, v_a_1670_, v_fallback_1671_, v_x_1672_);
lean_dec(v_x_1672_);
lean_dec(v_fallback_1671_);
lean_dec(v_a_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1674_, lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1675_, v_x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_a_1679_, lean_object* v_x_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1678_, v_a_1679_, v_x_1680_);
lean_dec(v_x_1680_);
lean_dec(v_a_1679_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1683_, lean_object* v_data_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1686_, lean_object* v_a_1687_, lean_object* v_b_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1687_, v_b_1688_, v_x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v_n_1693_, lean_object* v_lo_1694_, lean_object* v_hi_1695_, lean_object* v_hhi_1696_, lean_object* v_pivot_1697_, lean_object* v_as_1698_, lean_object* v_i_1699_, lean_object* v_k_1700_, lean_object* v_ilo_1701_, lean_object* v_ik_1702_, lean_object* v_w_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1691_, v___x_1692_, v_hi_1695_, v_pivot_1697_, v_as_1698_, v_i_1699_, v_k_1700_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1705_, lean_object* v___x_1706_, lean_object* v_n_1707_, lean_object* v_lo_1708_, lean_object* v_hi_1709_, lean_object* v_hhi_1710_, lean_object* v_pivot_1711_, lean_object* v_as_1712_, lean_object* v_i_1713_, lean_object* v_k_1714_, lean_object* v_ilo_1715_, lean_object* v_ik_1716_, lean_object* v_w_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1705_, v___x_1706_, v_n_1707_, v_lo_1708_, v_hi_1709_, v_hhi_1710_, v_pivot_1711_, v_as_1712_, v_i_1713_, v_k_1714_, v_ilo_1715_, v_ik_1716_, v_w_1717_);
lean_dec(v_hi_1709_);
lean_dec(v_lo_1708_);
lean_dec(v_n_1707_);
lean_dec(v___x_1706_);
lean_dec(v___x_1705_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1719_, lean_object* v_lo_1720_, lean_object* v_hi_1721_, lean_object* v_hhi_1722_, lean_object* v_pivot_1723_, lean_object* v_as_1724_, lean_object* v_i_1725_, lean_object* v_k_1726_, lean_object* v_ilo_1727_, lean_object* v_ik_1728_, lean_object* v_w_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1721_, v_pivot_1723_, v_as_1724_, v_i_1725_, v_k_1726_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1731_, lean_object* v_lo_1732_, lean_object* v_hi_1733_, lean_object* v_hhi_1734_, lean_object* v_pivot_1735_, lean_object* v_as_1736_, lean_object* v_i_1737_, lean_object* v_k_1738_, lean_object* v_ilo_1739_, lean_object* v_ik_1740_, lean_object* v_w_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1731_, v_lo_1732_, v_hi_1733_, v_hhi_1734_, v_pivot_1735_, v_as_1736_, v_i_1737_, v_k_1738_, v_ilo_1739_, v_ik_1740_, v_w_1741_);
lean_dec_ref(v_pivot_1735_);
lean_dec(v_hi_1733_);
lean_dec(v_lo_1732_);
lean_dec(v_n_1731_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1743_, lean_object* v_i_1744_, lean_object* v_source_1745_, lean_object* v_target_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1744_, v_source_1745_, v_target_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1748_, lean_object* v_i_1749_, lean_object* v_source_1750_, lean_object* v_target_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1749_, v_source_1750_, v_target_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1754_, v_x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1758_, v_x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v_env_1765_; lean_object* v___x_1766_; lean_object* v_env_1767_; lean_object* v___x_1768_; lean_object* v_toEnvExtension_1769_; lean_object* v_asyncMode_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1764_ = lean_st_ref_get(v___y_1762_);
v_env_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_ref(v_env_1765_);
lean_dec(v___x_1764_);
v___x_1766_ = lean_st_ref_get(v___y_1762_);
v_env_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc_ref(v_env_1767_);
lean_dec(v___x_1766_);
v___x_1768_ = l_Lean_declRangeExt;
v_toEnvExtension_1769_ = lean_ctor_get(v___x_1768_, 0);
v_asyncMode_1770_ = lean_ctor_get(v_toEnvExtension_1769_, 2);
v___x_1771_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1772_ = 0;
lean_inc(v_declName_1761_);
v___x_1773_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1771_, v___x_1768_, v_env_1765_, v_declName_1761_, v_asyncMode_1770_, v___x_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = 1;
v___x_1775_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1771_, v___x_1768_, v_env_1767_, v_declName_1761_, v_asyncMode_1770_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_dec_ref(v_env_1767_);
lean_dec(v_declName_1761_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1773_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1778_, v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v_env_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = lean_st_ref_get(v___y_1783_);
v_env_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc_ref(v_env_1786_);
lean_dec(v___x_1785_);
v___x_1787_ = l_Lean_isRecCore(v_env_1786_, v_declName_1782_);
v___x_1788_ = lean_box(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1790_, v___y_1791_);
lean_dec(v___y_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_ranges_1799_; lean_object* v___x_1805_; lean_object* v_env_1806_; lean_object* v___x_1807_; lean_object* v_a_1808_; uint8_t v___y_1814_; uint8_t v___x_1818_; 
v___x_1805_ = lean_st_ref_get(v___y_1796_);
v_env_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_ref_n(v_env_1806_, 2);
lean_dec(v___x_1805_);
lean_inc_n(v_declName_1794_, 2);
v___x_1807_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1794_, v___y_1796_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1818_ = l_Lean_isAuxRecursor(v_env_1806_, v_declName_1794_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; 
lean_inc(v_declName_1794_);
v___x_1819_ = l_Lean_isNoConfusion(v_env_1806_, v_declName_1794_);
v___y_1814_ = v___x_1819_;
goto v___jp_1813_;
}
else
{
lean_dec_ref(v_env_1806_);
v___y_1814_ = v___x_1818_;
goto v___jp_1813_;
}
v___jp_1798_:
{
if (lean_obj_tag(v_ranges_1799_) == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = l_Lean_builtinDeclRanges;
v___x_1801_ = lean_st_ref_get(v___x_1800_);
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1801_, v_declName_1794_);
lean_dec(v_declName_1794_);
lean_dec(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_declName_1794_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_ranges_1799_);
return v___x_1804_;
}
}
v___jp_1809_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v_a_1812_; 
v___x_1810_ = l_Lean_Name_getPrefix(v_declName_1794_);
v___x_1811_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1810_, v___y_1796_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
v_ranges_1799_ = v_a_1812_;
goto v___jp_1798_;
}
v___jp_1813_:
{
if (v___y_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_unbox(v_a_1808_);
lean_dec(v_a_1808_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v_a_1817_; 
lean_inc(v_declName_1794_);
v___x_1816_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1794_, v___y_1796_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1816_);
v_ranges_1799_ = v_a_1817_;
goto v___jp_1798_;
}
else
{
goto v___jp_1809_;
}
}
else
{
lean_dec(v_a_1808_);
goto v___jp_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1825_, lean_object* v_site_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
if (lean_obj_tag(v_site_1826_) == 0)
{
lean_object* v_name_1830_; lean_object* v___x_1831_; 
v_name_1830_ = lean_ctor_get(v_site_1826_, 0);
lean_inc(v_name_1830_);
lean_dec_ref_known(v_site_1826_, 1);
v___x_1831_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1830_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1853_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1853_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1853_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (lean_obj_tag(v_a_1832_) == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_box(0);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v_val_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1852_; 
v_val_1840_ = lean_ctor_get(v_a_1832_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_a_1832_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1842_ = v_a_1832_;
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_val_1840_);
lean_dec(v_a_1832_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_range_1844_; lean_object* v_pos_1845_; lean_object* v___x_1847_; 
v_range_1844_ = lean_ctor_get(v_val_1840_, 0);
lean_inc_ref(v_range_1844_);
lean_dec(v_val_1840_);
v_pos_1845_ = lean_ctor_get(v_range_1844_, 0);
lean_inc_ref(v_pos_1845_);
lean_dec_ref(v_range_1844_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_pos_1845_);
v___x_1847_ = v___x_1842_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_pos_1845_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1847_);
v___x_1849_ = v___x_1834_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1831_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1831_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_n_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1893_; 
v_n_1862_ = lean_ctor_get(v_site_1826_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_site_1826_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1864_ = v_site_1826_;
v_isShared_1865_ = v_isSharedCheck_1893_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_n_1862_);
lean_dec(v_site_1826_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1893_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v_env_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_st_ref_get(v_a_1828_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1868_ = l_Lean_getVersoModuleDoc_x3f(v_env_1867_, v_failMod_1825_);
lean_dec_ref(v_env_1867_);
if (lean_obj_tag(v___x_1868_) == 1)
{
lean_object* v_val_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1888_; 
v_val_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1888_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_val_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1888_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1873_ = lean_array_get_size(v_val_1869_);
v___x_1874_ = lean_nat_dec_lt(v_n_1862_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_del_object(v___x_1871_);
lean_dec(v_val_1869_);
lean_dec(v_n_1862_);
v___x_1875_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1875_);
v___x_1877_ = v___x_1864_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
else
{
lean_object* v___x_1879_; lean_object* v_declarationRange_1880_; lean_object* v_pos_1881_; lean_object* v___x_1883_; 
v___x_1879_ = lean_array_fget(v_val_1869_, v_n_1862_);
lean_dec(v_n_1862_);
lean_dec(v_val_1869_);
v_declarationRange_1880_ = lean_ctor_get(v___x_1879_, 2);
lean_inc_ref(v_declarationRange_1880_);
lean_dec(v___x_1879_);
v_pos_1881_ = lean_ctor_get(v_declarationRange_1880_, 0);
lean_inc_ref(v_pos_1881_);
lean_dec_ref(v_declarationRange_1880_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v_pos_1881_);
v___x_1883_ = v___x_1871_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_pos_1881_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1883_);
v___x_1885_ = v___x_1864_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
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
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec(v___x_1868_);
lean_dec(v_n_1862_);
v___x_1889_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1889_);
v___x_1891_ = v___x_1864_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1894_, lean_object* v_site_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1894_, v_site_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_failMod_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1900_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1910_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_object* v_name_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_name_1924_ = lean_ctor_get(v_x_1923_, 0);
lean_inc(v_name_1924_);
lean_dec_ref_known(v_x_1923_, 1);
v___x_1925_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1926_ = 1;
v___x_1927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1924_, v___x_1926_);
v___x_1928_ = lean_string_append(v___x_1925_, v___x_1927_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
return v___x_1930_;
}
else
{
lean_object* v_n_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_n_1931_ = lean_ctor_get(v_x_1923_, 0);
lean_inc(v_n_1931_);
lean_dec_ref_known(v_x_1923_, 1);
v___x_1932_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = lean_nat_add(v_n_1931_, v___x_1933_);
lean_dec(v_n_1931_);
v___x_1935_ = l_Nat_reprFast(v___x_1934_);
v___x_1936_ = lean_string_append(v___x_1932_, v___x_1935_);
lean_dec_ref(v___x_1935_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; lean_object* v___x_1942_; lean_object* v_toEnvExtension_1943_; lean_object* v_asyncMode_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_merged_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v___x_1940_ = lean_st_ref_get(v___y_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v___x_1942_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1943_ = lean_ctor_get(v___x_1942_, 0);
v_asyncMode_1944_ = lean_ctor_get(v_toEnvExtension_1943_, 2);
v___x_1945_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1946_ = lean_box(0);
v___x_1947_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1945_, v___x_1942_, v_env_1941_, v_asyncMode_1944_, v___x_1946_);
v_merged_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1947_, 1);
lean_dec(v_unused_1957_);
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_merged_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_merged_1948_);
lean_ctor_set(v___x_1950_, 0, v_o_1937_);
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_o_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_merged_1948_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1958_, v___y_1959_);
lean_dec(v___y_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1962_, v___y_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1971_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1972_, lean_object* v_opt_1973_){
_start:
{
lean_object* v_name_1974_; lean_object* v_defValue_1975_; lean_object* v_map_1976_; lean_object* v___x_1977_; 
v_name_1974_ = lean_ctor_get(v_opt_1973_, 0);
v_defValue_1975_ = lean_ctor_get(v_opt_1973_, 1);
v_map_1976_ = lean_ctor_get(v_opts_1972_, 0);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1976_, v_name_1974_);
if (lean_obj_tag(v___x_1977_) == 0)
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_unbox(v_defValue_1975_);
return v___x_1978_;
}
else
{
lean_object* v_val_1979_; 
v_val_1979_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v___x_1977_, 1);
if (lean_obj_tag(v_val_1979_) == 1)
{
uint8_t v_v_1980_; 
v_v_1980_ = lean_ctor_get_uint8(v_val_1979_, 0);
lean_dec_ref_known(v_val_1979_, 0);
return v_v_1980_;
}
else
{
uint8_t v___x_1981_; 
lean_dec(v_val_1979_);
v___x_1981_ = lean_unbox(v_defValue_1975_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1982_, lean_object* v_opt_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1982_, v_opt_1983_);
lean_dec_ref(v_opt_1983_);
lean_dec_ref(v_opts_1982_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1986_, lean_object* v_opt_1987_){
_start:
{
lean_object* v_name_1988_; lean_object* v_defValue_1989_; lean_object* v_map_1990_; lean_object* v___x_1991_; 
v_name_1988_ = lean_ctor_get(v_opt_1987_, 0);
v_defValue_1989_ = lean_ctor_get(v_opt_1987_, 1);
v_map_1990_ = lean_ctor_get(v_opts_1986_, 0);
v___x_1991_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1990_, v_name_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_inc(v_defValue_1989_);
return v_defValue_1989_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1991_, 1);
if (lean_obj_tag(v_val_1992_) == 3)
{
lean_object* v_v_1993_; 
v_v_1993_ = lean_ctor_get(v_val_1992_, 0);
lean_inc(v_v_1993_);
lean_dec_ref_known(v_val_1992_, 1);
return v_v_1993_;
}
else
{
lean_dec(v_val_1992_);
lean_inc(v_defValue_1989_);
return v_defValue_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1994_, lean_object* v_opt_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1994_, v_opt_1995_);
lean_dec_ref(v_opt_1995_);
lean_dec_ref(v_opts_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_options_2001_; lean_object* v___x_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
v_options_2001_ = lean_ctor_get(v_c_1997_, 6);
lean_inc_ref(v_options_2001_);
lean_dec_ref(v_c_1997_);
v___x_2002_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_2001_, v___y_1999_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2007_ = l_Lean_linter_doc_deferred;
v___x_2008_ = l_Lean_Linter_getLinterValue(v___x_2007_, v_a_2003_);
lean_dec(v_a_2003_);
v___x_2009_ = lean_box(v___x_2008_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2009_);
v___x_2011_ = v___x_2005_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2019_, lean_object* v_docCheckedModules_2020_, uint8_t v___y_2021_, lean_object* v_m_2022_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2019_, v_m_2022_);
if (v___x_2023_ == 0)
{
return v___x_2023_;
}
else
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_NameSet_contains(v_docCheckedModules_2020_, v_m_2022_);
if (v___x_2024_ == 0)
{
return v___y_2021_;
}
else
{
uint8_t v___x_2025_; 
v___x_2025_ = 0;
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2026_, lean_object* v_docCheckedModules_2027_, lean_object* v___y_2028_, lean_object* v_m_2029_){
_start:
{
uint8_t v___y_7017__boxed_2030_; uint8_t v_res_2031_; lean_object* v_r_2032_; 
v___y_7017__boxed_2030_ = lean_unbox(v___y_2028_);
v_res_2031_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2026_, v_docCheckedModules_2027_, v___y_7017__boxed_2030_, v_m_2029_);
lean_dec(v_m_2029_);
lean_dec(v_docCheckedModules_2027_);
lean_dec(v_pkgRoot_2026_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_2040_, lean_object* v_sp_2041_, lean_object* v_as_2042_, size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_a_2050_; uint8_t v_unlocated_2054_; 
v_unlocated_2054_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v_unlocated_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v_sp_2041_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v_b_2045_);
return v___x_2055_;
}
else
{
lean_object* v_a_2056_; lean_object* v_snd_2057_; lean_object* v_fst_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2187_; 
v_a_2056_ = lean_array_uget_borrowed(v_as_2042_, v_i_2044_);
v_snd_2057_ = lean_ctor_get(v_a_2056_, 1);
lean_inc(v_snd_2057_);
v_fst_2058_ = lean_ctor_get(v_snd_2057_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_snd_2057_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_snd_2057_, 1);
lean_dec(v_unused_2188_);
v___x_2060_ = v_snd_2057_;
v_isShared_2061_ = v_isSharedCheck_2187_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_fst_2058_);
lean_dec(v_snd_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2187_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_fst_2062_; lean_object* v_site_2063_; lean_object* v___x_2064_; 
v_fst_2062_ = lean_ctor_get(v_a_2056_, 0);
v_site_2063_ = lean_ctor_get(v_fst_2058_, 0);
lean_inc_ref_n(v_site_2063_, 2);
lean_dec(v_fst_2058_);
v___x_2064_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2062_, v_site_2063_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_object* v_fst_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2105_; 
v_fst_2066_ = lean_ctor_get(v_b_2045_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_b_2045_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_b_2045_, 1);
lean_dec(v_unused_2106_);
v___x_2068_ = v_b_2045_;
v_isShared_2069_ = v_isSharedCheck_2105_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_fst_2066_);
lean_dec(v_b_2045_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2105_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_name_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2070_ = l_Lean_linter_doc_deferred;
v_name_2071_ = lean_ctor_get(v___x_2070_, 0);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_2073_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2063_);
v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
lean_inc(v_fst_2062_);
v___x_2077_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2062_, v___x_2040_);
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
lean_inc(v_name_2071_);
v___x_2081_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2071_, v___x_2040_);
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
v___x_2085_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2085_, 1);
lean_del_object(v___x_2060_);
v___x_2086_ = lean_box(v_unlocated_2054_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2086_);
v___x_2088_ = v___x_2068_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_fst_2066_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v_a_2050_ = v___x_2088_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
lean_del_object(v___x_2068_);
lean_dec(v_fst_2066_);
lean_dec(v_sp_2041_);
v_a_2090_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v___x_2085_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2085_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_ref_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_ref_2094_ = lean_ctor_get(v___y_2046_, 5);
v___x_2095_ = lean_io_error_to_string(v_a_2090_);
v___x_2096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = l_Lean_MessageData_ofFormat(v___x_2096_);
lean_inc(v_ref_2094_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2097_);
lean_ctor_set(v___x_2060_, 0, v_ref_2094_);
v___x_2099_ = v___x_2060_;
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
}
else
{
lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_site_2063_);
v_fst_2107_ = lean_ctor_get(v_b_2045_, 0);
v_snd_2108_ = lean_ctor_get(v_b_2045_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_b_2045_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2110_ = v_b_2045_;
v_isShared_2111_ = v_isSharedCheck_2178_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_snd_2108_);
lean_inc(v_fst_2107_);
lean_dec(v_b_2045_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2178_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_val_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2177_; 
v_val_2112_ = lean_ctor_get(v_a_2065_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_a_2065_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2114_ = v_a_2065_;
v_isShared_2115_ = v_isSharedCheck_2177_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_val_2112_);
lean_dec(v_a_2065_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2177_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2062_);
lean_inc(v_sp_2041_);
v___x_2117_ = l_Lean_SearchPath_findWithExt(v_sp_2041_, v___x_2116_, v_fst_2062_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
if (lean_obj_tag(v_a_2118_) == 0)
{
lean_object* v___x_2119_; lean_object* v_name_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec(v_val_2112_);
lean_dec(v_snd_2108_);
v___x_2119_ = l_Lean_linter_doc_deferred;
v_name_2120_ = lean_ctor_get(v___x_2119_, 0);
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_2062_);
v___x_2122_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2062_, v___x_2040_);
v___x_2123_ = lean_string_append(v___x_2121_, v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
lean_inc(v_name_2120_);
v___x_2126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2120_, v___x_2040_);
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2129_ = lean_string_append(v___x_2127_, v___x_2128_);
v___x_2130_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec_ref_known(v___x_2130_, 1);
lean_del_object(v___x_2114_);
lean_del_object(v___x_2060_);
v___x_2131_ = lean_box(v_unlocated_2054_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v___x_2131_);
v___x_2133_ = v___x_2110_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2107_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
v_a_2050_ = v___x_2133_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2151_; 
lean_del_object(v___x_2110_);
lean_dec(v_fst_2107_);
lean_dec(v_sp_2041_);
v_a_2135_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2137_ = v___x_2130_;
v_isShared_2138_ = v_isSharedCheck_2151_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2130_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2151_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_ref_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v_ref_2139_ = lean_ctor_get(v___y_2046_, 5);
v___x_2140_ = lean_io_error_to_string(v_a_2135_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 3);
lean_ctor_set(v___x_2114_, 0, v___x_2140_);
v___x_2142_ = v___x_2114_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = l_Lean_MessageData_ofFormat(v___x_2142_);
lean_inc(v_ref_2139_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2143_);
lean_ctor_set(v___x_2060_, 0, v_ref_2139_);
v___x_2145_ = v___x_2060_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_ref_2139_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2145_);
v___x_2147_ = v___x_2137_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
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
else
{
lean_object* v_val_2152_; lean_object* v___x_2153_; lean_object* v_name_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_del_object(v___x_2114_);
lean_del_object(v___x_2060_);
v_val_2152_ = lean_ctor_get(v_a_2118_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v_a_2118_, 1);
v___x_2153_ = l_Lean_linter_doc_deferred;
v_name_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_name_2154_);
v___x_2155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2155_, 0, v_val_2152_);
lean_ctor_set(v___x_2155_, 1, v_val_2112_);
lean_ctor_set(v___x_2155_, 2, v_name_2154_);
v___x_2156_ = lean_array_push(v_fst_2107_, v___x_2155_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2156_);
v___x_2158_ = v___x_2110_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_snd_2108_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_a_2050_ = v___x_2158_;
goto v___jp_2049_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_val_2112_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_sp_2041_);
v_a_2160_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2162_ = v___x_2117_;
v_isShared_2163_ = v_isSharedCheck_2176_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2117_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2176_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_ref_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_ref_2164_ = lean_ctor_get(v___y_2046_, 5);
v___x_2165_ = lean_io_error_to_string(v_a_2160_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 3);
lean_ctor_set(v___x_2114_, 0, v___x_2165_);
v___x_2167_ = v___x_2114_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = l_Lean_MessageData_ofFormat(v___x_2167_);
lean_inc(v_ref_2164_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2168_);
lean_ctor_set(v___x_2060_, 0, v_ref_2164_);
v___x_2170_ = v___x_2060_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_ref_2164_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2170_);
v___x_2172_ = v___x_2162_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
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
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_site_2063_);
lean_del_object(v___x_2060_);
lean_dec_ref(v_b_2045_);
lean_dec(v_sp_2041_);
v_a_2179_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2064_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2064_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
v___jp_2049_:
{
size_t v___x_2051_; size_t v___x_2052_; 
v___x_2051_ = ((size_t)1ULL);
v___x_2052_ = lean_usize_add(v_i_2044_, v___x_2051_);
v_i_2044_ = v___x_2052_;
v_b_2045_ = v_a_2050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2189_, lean_object* v_sp_2190_, lean_object* v_as_2191_, lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_7041__boxed_2198_; size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v___x_7041__boxed_2198_ = lean_unbox(v___x_2189_);
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_7041__boxed_2198_, v_sp_2190_, v_as_2191_, v_sz_boxed_2199_, v_i_boxed_2200_, v_b_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v_as_2191_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_2208_, uint8_t v___y_2209_, lean_object* v_as_2210_, size_t v_sz_2211_, size_t v_i_2212_, lean_object* v_b_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_a_2217_; uint8_t v___x_2221_; 
v___x_2221_ = lean_usize_dec_lt(v_i_2212_, v_sz_2211_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_sp_2208_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_b_2213_);
return v___x_2222_;
}
else
{
lean_object* v_a_2223_; lean_object* v_snd_2224_; lean_object* v_fst_2225_; lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2322_; 
v_a_2223_ = lean_array_uget_borrowed(v_as_2210_, v_i_2212_);
v_snd_2224_ = lean_ctor_get(v_a_2223_, 1);
lean_inc(v_snd_2224_);
v_fst_2225_ = lean_ctor_get(v_snd_2224_, 0);
lean_inc(v_fst_2225_);
v_fst_2226_ = lean_ctor_get(v_a_2223_, 0);
v_snd_2227_ = lean_ctor_get(v_snd_2224_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_snd_2224_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_snd_2224_, 0);
lean_dec(v_unused_2323_);
v___x_2229_ = v_snd_2224_;
v_isShared_2230_ = v_isSharedCheck_2322_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snd_2227_);
lean_dec(v_snd_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2322_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_site_2231_; lean_object* v_sourceString_2232_; lean_object* v___x_2233_; lean_object* v___y_2235_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_site_2231_ = lean_ctor_get(v_fst_2225_, 0);
lean_inc_ref(v_site_2231_);
v_sourceString_2232_ = lean_ctor_get(v_fst_2225_, 2);
lean_inc_ref(v_sourceString_2232_);
lean_dec(v_fst_2225_);
v___x_2233_ = lean_box(0);
v___x_2314_ = lean_string_utf8_byte_size(v_sourceString_2232_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_nat_dec_eq(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2318_ = lean_string_append(v___x_2317_, v_sourceString_2232_);
lean_dec_ref(v_sourceString_2232_);
v___x_2319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2320_ = lean_string_append(v___x_2318_, v___x_2319_);
v___y_2235_ = v___x_2320_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2321_; 
lean_dec_ref(v_sourceString_2232_);
v___x_2321_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2235_ = v___x_2321_;
goto v___jp_2234_;
}
v___jp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2226_);
lean_inc(v_sp_2208_);
v___x_2237_ = l_Lean_SearchPath_findWithExt(v_sp_2208_, v___x_2236_, v_fst_2226_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
if (lean_obj_tag(v_a_2238_) == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2239_ = l_Lean_MessageData_toString(v_snd_2227_);
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2226_);
v___x_2241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2226_, v___y_2209_);
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
v___x_2245_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2231_);
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = lean_string_append(v___x_2246_, v___y_2235_);
lean_dec_ref(v___y_2235_);
v___x_2248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2249_ = lean_string_append(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_string_append(v___x_2249_, v___x_2239_);
lean_dec_ref(v___x_2239_);
v___x_2251_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2250_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_dec_ref_known(v___x_2251_, 1);
lean_del_object(v___x_2229_);
v_a_2217_ = v___x_2233_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_sp_2208_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2266_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2266_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_ref_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v_ref_2256_ = lean_ctor_get(v___y_2214_, 5);
v___x_2257_ = lean_io_error_to_string(v_a_2252_);
v___x_2258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_ofFormat(v___x_2258_);
lean_inc(v_ref_2256_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2259_);
lean_ctor_set(v___x_2229_, 0, v_ref_2256_);
v___x_2261_ = v___x_2229_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_ref_2256_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2298_; 
v_val_2267_ = lean_ctor_get(v_a_2238_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_a_2238_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2269_ = v_a_2238_;
v_isShared_2270_ = v_isSharedCheck_2298_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_dec(v_a_2238_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2298_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2271_ = l_Lean_MessageData_toString(v_snd_2227_);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2273_ = lean_string_append(v_val_2267_, v___x_2272_);
v___x_2274_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2231_);
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = lean_string_append(v___x_2275_, v___y_2235_);
lean_dec_ref(v___y_2235_);
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2278_ = lean_string_append(v___x_2276_, v___x_2277_);
v___x_2279_ = lean_string_append(v___x_2278_, v___x_2271_);
lean_dec_ref(v___x_2271_);
v___x_2280_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_dec_ref_known(v___x_2280_, 1);
lean_del_object(v___x_2269_);
lean_del_object(v___x_2229_);
v_a_2217_ = v___x_2233_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_sp_2208_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2297_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2297_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_ref_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v_ref_2285_ = lean_ctor_get(v___y_2214_, 5);
v___x_2286_ = lean_io_error_to_string(v_a_2281_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set_tag(v___x_2269_, 3);
lean_ctor_set(v___x_2269_, 0, v___x_2286_);
v___x_2288_ = v___x_2269_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = l_Lean_MessageData_ofFormat(v___x_2288_);
lean_inc(v_ref_2285_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2289_);
lean_ctor_set(v___x_2229_, 0, v_ref_2285_);
v___x_2291_ = v___x_2229_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_ref_2285_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2293_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2291_);
v___x_2293_ = v___x_2283_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
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
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_site_2231_);
lean_dec(v_snd_2227_);
lean_dec(v_sp_2208_);
v_a_2299_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2301_ = v___x_2237_;
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2237_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_ref_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v_ref_2303_ = lean_ctor_get(v___y_2214_, 5);
v___x_2304_ = lean_io_error_to_string(v_a_2299_);
v___x_2305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = l_Lean_MessageData_ofFormat(v___x_2305_);
lean_inc(v_ref_2303_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2306_);
lean_ctor_set(v___x_2229_, 0, v_ref_2303_);
v___x_2308_ = v___x_2229_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_ref_2303_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2308_);
v___x_2310_ = v___x_2301_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
}
v___jp_2216_:
{
size_t v___x_2218_; size_t v___x_2219_; 
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_add(v_i_2212_, v___x_2218_);
v_i_2212_ = v___x_2219_;
v_b_2213_ = v_a_2217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2324_, lean_object* v___y_2325_, lean_object* v_as_2326_, lean_object* v_sz_2327_, lean_object* v_i_2328_, lean_object* v_b_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v___y_7333__boxed_2332_; size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v___y_7333__boxed_2332_ = lean_unbox(v___y_2325_);
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2324_, v___y_7333__boxed_2332_, v_as_2326_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2329_, v___y_2330_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_as_2326_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2336_, lean_object* v_as_2337_, size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_b_2340_){
_start:
{
lean_object* v_a_2343_; uint8_t v___x_2347_; 
v___x_2347_ = lean_usize_dec_lt(v_i_2339_, v_sz_2338_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_b_2340_);
return v___x_2348_;
}
else
{
lean_object* v_a_2349_; uint8_t v___x_2350_; 
v_a_2349_ = lean_array_uget_borrowed(v_as_2337_, v_i_2339_);
v___x_2350_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2336_, v_a_2349_);
if (v___x_2350_ == 0)
{
v_a_2343_ = v_b_2340_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2351_; 
lean_inc(v_a_2349_);
v___x_2351_ = l_Lean_NameSet_insert(v_b_2340_, v_a_2349_);
v_a_2343_ = v___x_2351_;
goto v___jp_2342_;
}
}
v___jp_2342_:
{
size_t v___x_2344_; size_t v___x_2345_; 
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_add(v_i_2339_, v___x_2344_);
v_i_2339_ = v___x_2345_;
v_b_2340_ = v_a_2343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2352_, lean_object* v_as_2353_, lean_object* v_sz_2354_, lean_object* v_i_2355_, lean_object* v_b_2356_, lean_object* v___y_2357_){
_start:
{
size_t v_sz_boxed_2358_; size_t v_i_boxed_2359_; lean_object* v_res_2360_; 
v_sz_boxed_2358_ = lean_unbox_usize(v_sz_2354_);
lean_dec(v_sz_2354_);
v_i_boxed_2359_ = lean_unbox_usize(v_i_2355_);
lean_dec(v_i_2355_);
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2352_, v_as_2353_, v_sz_boxed_2358_, v_i_boxed_2359_, v_b_2356_);
lean_dec_ref(v_as_2353_);
lean_dec(v_pkgRoot_2352_);
return v_res_2360_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_unsigned_to_nat(32u);
v___x_2368_ = lean_mk_empty_array_with_capacity(v___x_2367_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((size_t)5ULL);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_unsigned_to_nat(32u);
v___x_2373_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2374_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2375_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2373_);
lean_ctor_set(v___x_2375_, 2, v___x_2371_);
lean_ctor_set(v___x_2375_, 3, v___x_2371_);
lean_ctor_set_usize(v___x_2375_, 4, v___x_2370_);
return v___x_2375_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = l_Lean_NameSet_empty;
v___x_2382_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
lean_ctor_set(v___x_2383_, 2, v___x_2381_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = l_Lean_firstFrontendMacroScope;
v___x_2386_ = lean_nat_add(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2397_; uint64_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2398_ = 0ULL;
v___x_2399_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set_uint64(v___x_2399_, sizeof(void*)*1, v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v_unlocated_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2401_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2402_ = 1;
v___x_2403_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
lean_ctor_set(v___x_2403_, 2, v___x_2400_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*3, v_unlocated_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = l_Lean_Options_empty;
v___x_2407_ = l_Lean_Core_getMaxHeartbeats(v___x_2406_);
return v___x_2407_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2408_ = l_Lean_diagnostics;
v___x_2409_ = l_Lean_Options_empty;
v___x_2410_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2411_, lean_object* v_linterOpts_2412_, lean_object* v_sp_2413_, lean_object* v_env_2414_, lean_object* v_pkgRoot_2415_, lean_object* v_docCheckedModules_2416_){
_start:
{
lean_object* v___y_2419_; lean_object* v_a_2420_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2449_; lean_object* v_a_2453_; uint8_t v___y_2457_; lean_object* v_a_2458_; uint8_t v_lintOnly_2474_; uint8_t v_mode_2475_; lean_object* v___f_2476_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; uint8_t v___y_2483_; uint8_t v___y_2484_; lean_object* v_fileName_2485_; lean_object* v_fileMap_2486_; lean_object* v_currRecDepth_2487_; lean_object* v_ref_2488_; lean_object* v_currNamespace_2489_; lean_object* v_openDecls_2490_; lean_object* v_initHeartbeats_2491_; lean_object* v_maxHeartbeats_2492_; lean_object* v_quotContext_2493_; lean_object* v_currMacroScope_2494_; lean_object* v_cancelTk_x3f_2495_; uint8_t v_suppressElabErrors_2496_; lean_object* v_inheritedTraceOptions_2497_; lean_object* v___y_2498_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; uint8_t v___y_2557_; uint8_t v___y_2558_; uint8_t v___y_2559_; uint8_t v___y_2580_; 
v_lintOnly_2474_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4);
v_mode_2475_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4 + 1);
v___f_2476_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2474_ == 0)
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = l_Lean_linter_doc_deferred;
v___x_2619_ = l_Lean_Linter_getLinterValue(v___x_2618_, v_linterOpts_2412_);
v___y_2580_ = v___x_2619_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2620_; lean_object* v_name_2621_; uint8_t v___x_2622_; 
v___x_2620_ = l_Lean_linter_doc_deferred;
v_name_2621_ = lean_ctor_get(v___x_2620_, 0);
v___x_2622_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2621_, v_linterOpts_2412_);
v___y_2580_ = v___x_2622_;
goto v___jp_2579_;
}
v___jp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; size_t v_sz_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2421_ = lean_st_ref_get(v___y_2419_);
lean_dec(v___y_2419_);
lean_dec(v___x_2421_);
v___x_2422_ = l_Lean_Environment_header(v_env_2414_);
lean_dec_ref(v_env_2414_);
v___x_2423_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2422_);
v_sz_2424_ = lean_array_size(v___x_2423_);
v___x_2425_ = ((size_t)0ULL);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2415_, v___x_2423_, v_sz_2424_, v___x_2425_, v_docCheckedModules_2416_);
lean_dec_ref(v___x_2423_);
lean_dec(v_pkgRoot_2415_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2420_);
lean_ctor_set(v___x_2431_, 1, v_a_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v_a_2420_);
v_a_2436_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2426_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2426_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
v___jp_2444_:
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2447_, 0, v___y_2446_);
v___y_2419_ = v___y_2445_;
v_a_2420_ = v___x_2447_;
goto v___jp_2418_;
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___y_2449_);
lean_ctor_set(v___x_2450_, 1, v_docCheckedModules_2416_);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_mk_io_user_error(v_a_2453_);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
v___jp_2456_:
{
if (lean_obj_tag(v_a_2458_) == 0)
{
lean_object* v_msg_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_msg_2459_ = lean_ctor_get(v_a_2458_, 1);
lean_inc_ref(v_msg_2459_);
lean_dec_ref_known(v_a_2458_, 2);
v___x_2460_ = l_Lean_MessageData_toString(v_msg_2459_);
v___x_2461_ = lean_mk_io_user_error(v___x_2460_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
else
{
lean_object* v_id_2463_; lean_object* v___x_2464_; 
v_id_2463_ = lean_ctor_get(v_a_2458_, 0);
lean_inc(v_id_2463_);
lean_dec_ref_known(v_a_2458_, 2);
v___x_2464_ = l_Lean_InternalExceptionId_getName(v_id_2463_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec(v_id_2463_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2467_ = l_Lean_Name_toString(v_a_2465_, v___y_2457_);
v___x_2468_ = lean_string_append(v___x_2466_, v___x_2467_);
lean_dec_ref(v___x_2467_);
v_a_2453_ = v___x_2468_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec_ref_known(v___x_2464_, 1);
v___x_2469_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2470_ = l_Nat_reprFast(v_id_2463_);
v___x_2471_ = lean_string_append(v___x_2469_, v___x_2470_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2473_ = lean_string_append(v___x_2471_, v___x_2472_);
v_a_2453_ = v___x_2473_;
goto v___jp_2452_;
}
}
}
v___jp_2477_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = l_Lean_maxRecDepth;
v___x_2500_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2479_, v___x_2499_);
lean_inc_ref(v___y_2479_);
v___x_2501_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2501_, 0, v_fileName_2485_);
lean_ctor_set(v___x_2501_, 1, v_fileMap_2486_);
lean_ctor_set(v___x_2501_, 2, v___y_2479_);
lean_ctor_set(v___x_2501_, 3, v_currRecDepth_2487_);
lean_ctor_set(v___x_2501_, 4, v___x_2500_);
lean_ctor_set(v___x_2501_, 5, v_ref_2488_);
lean_ctor_set(v___x_2501_, 6, v_currNamespace_2489_);
lean_ctor_set(v___x_2501_, 7, v_openDecls_2490_);
lean_ctor_set(v___x_2501_, 8, v_initHeartbeats_2491_);
lean_ctor_set(v___x_2501_, 9, v_maxHeartbeats_2492_);
lean_ctor_set(v___x_2501_, 10, v_quotContext_2493_);
lean_ctor_set(v___x_2501_, 11, v_currMacroScope_2494_);
lean_ctor_set(v___x_2501_, 12, v_cancelTk_x3f_2495_);
lean_ctor_set(v___x_2501_, 13, v_inheritedTraceOptions_2497_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*14, v___y_2484_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*14 + 1, v_suppressElabErrors_2496_);
v___x_2502_ = l_Lean_Doc_DeferredCheck_run(v___y_2478_, v___f_2476_, v___x_2501_, v___y_2498_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; uint8_t v___x_2504_; uint8_t v___x_2505_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2504_ = 1;
v___x_2505_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; size_t v_sz_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v___y_2498_);
v___x_2506_ = lean_box(0);
v_sz_2507_ = lean_array_size(v_a_2503_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2413_, v___y_2481_, v_a_2503_, v_sz_2507_, v___x_2508_, v___x_2506_, v___x_2501_);
lean_dec_ref_known(v___x_2501_, 14);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
lean_dec_ref_known(v___x_2509_, 1);
v___x_2510_ = lean_array_get_size(v_a_2503_);
lean_dec(v_a_2503_);
v___x_2511_ = lean_nat_dec_eq(v___x_2510_, v___y_2482_);
lean_dec(v___y_2482_);
if (v___x_2511_ == 0)
{
v___y_2445_ = v___y_2480_;
v___y_2446_ = v___y_2481_;
goto v___jp_2444_;
}
else
{
v___y_2445_ = v___y_2480_;
v___y_2446_ = v___x_2505_;
goto v___jp_2444_;
}
}
else
{
lean_object* v_a_2512_; 
lean_dec(v_a_2503_);
lean_dec(v___y_2482_);
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2512_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2512_;
goto v___jp_2456_;
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; size_t v_sz_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = lean_mk_empty_array_with_capacity(v___y_2482_);
lean_dec(v___y_2482_);
v___x_2514_ = lean_box(v___y_2483_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v_sz_2516_ = lean_array_size(v_a_2503_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2505_, v_sp_2413_, v_a_2503_, v_sz_2516_, v___x_2517_, v___x_2515_, v___x_2501_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref_known(v___x_2501_, 14);
lean_dec(v_a_2503_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v_fst_2520_ = lean_ctor_get(v_a_2519_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v_a_2519_, 1);
lean_inc(v_snd_2521_);
lean_dec(v_a_2519_);
v___x_2522_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2522_, 0, v_fst_2520_);
v___x_2523_ = lean_unbox(v_snd_2521_);
lean_dec(v_snd_2521_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*1, v___x_2523_);
v___y_2419_ = v___y_2480_;
v_a_2420_ = v___x_2522_;
goto v___jp_2418_;
}
else
{
lean_object* v_a_2524_; 
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2524_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2518_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2524_;
goto v___jp_2456_;
}
}
}
else
{
lean_object* v_a_2525_; 
lean_dec_ref_known(v___x_2501_, 14);
lean_dec(v___y_2498_);
lean_dec(v___y_2482_);
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v_a_2525_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2502_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2525_;
goto v___jp_2456_;
}
}
v___jp_2526_:
{
lean_object* v_fileName_2536_; lean_object* v_fileMap_2537_; lean_object* v_currRecDepth_2538_; lean_object* v_ref_2539_; lean_object* v_currNamespace_2540_; lean_object* v_openDecls_2541_; lean_object* v_initHeartbeats_2542_; lean_object* v_maxHeartbeats_2543_; lean_object* v_quotContext_2544_; lean_object* v_currMacroScope_2545_; lean_object* v_cancelTk_x3f_2546_; uint8_t v_suppressElabErrors_2547_; lean_object* v_inheritedTraceOptions_2548_; 
v_fileName_2536_ = lean_ctor_get(v___y_2534_, 0);
lean_inc_ref(v_fileName_2536_);
v_fileMap_2537_ = lean_ctor_get(v___y_2534_, 1);
lean_inc_ref(v_fileMap_2537_);
v_currRecDepth_2538_ = lean_ctor_get(v___y_2534_, 3);
lean_inc(v_currRecDepth_2538_);
v_ref_2539_ = lean_ctor_get(v___y_2534_, 5);
lean_inc(v_ref_2539_);
v_currNamespace_2540_ = lean_ctor_get(v___y_2534_, 6);
lean_inc(v_currNamespace_2540_);
v_openDecls_2541_ = lean_ctor_get(v___y_2534_, 7);
lean_inc(v_openDecls_2541_);
v_initHeartbeats_2542_ = lean_ctor_get(v___y_2534_, 8);
lean_inc(v_initHeartbeats_2542_);
v_maxHeartbeats_2543_ = lean_ctor_get(v___y_2534_, 9);
lean_inc(v_maxHeartbeats_2543_);
v_quotContext_2544_ = lean_ctor_get(v___y_2534_, 10);
lean_inc(v_quotContext_2544_);
v_currMacroScope_2545_ = lean_ctor_get(v___y_2534_, 11);
lean_inc(v_currMacroScope_2545_);
v_cancelTk_x3f_2546_ = lean_ctor_get(v___y_2534_, 12);
lean_inc(v_cancelTk_x3f_2546_);
v_suppressElabErrors_2547_ = lean_ctor_get_uint8(v___y_2534_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v___y_2534_, 13);
lean_inc_ref(v_inheritedTraceOptions_2548_);
lean_dec_ref(v___y_2534_);
v___y_2478_ = v___y_2527_;
v___y_2479_ = v___y_2528_;
v___y_2480_ = v___y_2529_;
v___y_2481_ = v___y_2530_;
v___y_2482_ = v___y_2531_;
v___y_2483_ = v___y_2532_;
v___y_2484_ = v___y_2533_;
v_fileName_2485_ = v_fileName_2536_;
v_fileMap_2486_ = v_fileMap_2537_;
v_currRecDepth_2487_ = v_currRecDepth_2538_;
v_ref_2488_ = v_ref_2539_;
v_currNamespace_2489_ = v_currNamespace_2540_;
v_openDecls_2490_ = v_openDecls_2541_;
v_initHeartbeats_2491_ = v_initHeartbeats_2542_;
v_maxHeartbeats_2492_ = v_maxHeartbeats_2543_;
v_quotContext_2493_ = v_quotContext_2544_;
v_currMacroScope_2494_ = v_currMacroScope_2545_;
v_cancelTk_x3f_2495_ = v_cancelTk_x3f_2546_;
v_suppressElabErrors_2496_ = v_suppressElabErrors_2547_;
v_inheritedTraceOptions_2497_ = v_inheritedTraceOptions_2548_;
v___y_2498_ = v___y_2535_;
goto v___jp_2477_;
}
v___jp_2549_:
{
if (v___y_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v_env_2561_; lean_object* v_nextMacroScope_2562_; lean_object* v_ngen_2563_; lean_object* v_auxDeclNGen_2564_; lean_object* v_traceState_2565_; lean_object* v_messages_2566_; lean_object* v_infoState_2567_; lean_object* v_snapshotTasks_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2577_; 
v___x_2560_ = lean_st_ref_take(v___y_2554_);
v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
v_nextMacroScope_2562_ = lean_ctor_get(v___x_2560_, 1);
v_ngen_2563_ = lean_ctor_get(v___x_2560_, 2);
v_auxDeclNGen_2564_ = lean_ctor_get(v___x_2560_, 3);
v_traceState_2565_ = lean_ctor_get(v___x_2560_, 4);
v_messages_2566_ = lean_ctor_get(v___x_2560_, 6);
v_infoState_2567_ = lean_ctor_get(v___x_2560_, 7);
v_snapshotTasks_2568_ = lean_ctor_get(v___x_2560_, 8);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2560_, 5);
lean_dec(v_unused_2578_);
v___x_2570_ = v___x_2560_;
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snapshotTasks_2568_);
lean_inc(v_infoState_2567_);
lean_inc(v_messages_2566_);
lean_inc(v_traceState_2565_);
lean_inc(v_auxDeclNGen_2564_);
lean_inc(v_ngen_2563_);
lean_inc(v_nextMacroScope_2562_);
lean_inc(v_env_2561_);
lean_dec(v___x_2560_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = l_Lean_Kernel_enableDiag(v_env_2561_, v___y_2558_);
lean_inc_ref(v___y_2552_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 5, v___y_2552_);
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_nextMacroScope_2562_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_ngen_2563_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_auxDeclNGen_2564_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_traceState_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 5, v___y_2552_);
lean_ctor_set(v_reuseFailAlloc_2576_, 6, v_messages_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 7, v_infoState_2567_);
lean_ctor_set(v_reuseFailAlloc_2576_, 8, v_snapshotTasks_2568_);
v___x_2574_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_st_ref_put(v___y_2554_, v___x_2574_);
lean_inc(v___y_2554_);
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2551_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2556_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v___y_2558_;
v___y_2534_ = v___y_2553_;
v___y_2535_ = v___y_2554_;
goto v___jp_2526_;
}
}
}
else
{
lean_inc(v___y_2554_);
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2551_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2556_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v___y_2558_;
v___y_2534_ = v___y_2553_;
v___y_2535_ = v___y_2554_;
goto v___jp_2526_;
}
}
v___jp_2579_:
{
if (v___y_2580_ == 0)
{
uint8_t v___x_2581_; uint8_t v___x_2582_; 
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v___x_2581_ = 1;
v___x_2582_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2583_, 0, v___x_2582_);
v___y_2449_ = v___x_2583_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2585_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*1, v___y_2580_);
v___y_2449_ = v___x_2585_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_env_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; uint8_t v___x_2616_; uint8_t v___x_2617_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2588_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2589_ = lean_io_get_num_heartbeats();
v___x_2590_ = l_Lean_firstFrontendMacroScope;
v___x_2591_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2592_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2596_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2597_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2598_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2414_);
v___x_2599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2599_, 0, v_env_2414_);
lean_ctor_set(v___x_2599_, 1, v___x_2591_);
lean_ctor_set(v___x_2599_, 2, v___x_2592_);
lean_ctor_set(v___x_2599_, 3, v___x_2595_);
lean_ctor_set(v___x_2599_, 4, v___x_2596_);
lean_ctor_set(v___x_2599_, 5, v___x_2587_);
lean_ctor_set(v___x_2599_, 6, v___x_2588_);
lean_ctor_set(v___x_2599_, 7, v___x_2597_);
lean_ctor_set(v___x_2599_, 8, v___x_2598_);
v___x_2600_ = lean_st_mk_ref(v___x_2599_);
v___x_2601_ = l_Lean_inheritedTraceOptions;
v___x_2602_ = lean_st_ref_get(v___x_2601_);
v___x_2603_ = lean_st_ref_get(v___x_2600_);
v___x_2604_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2605_ = l_Lean_instInhabitedFileMap_default;
v___x_2606_ = l_Lean_Options_empty;
v___x_2607_ = lean_unsigned_to_nat(1000u);
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2610_ = 0;
v___x_2611_ = lean_box(0);
lean_inc(v___x_2602_);
lean_inc(v___x_2589_);
v___x_2612_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2612_, 0, v___x_2604_);
lean_ctor_set(v___x_2612_, 1, v___x_2605_);
lean_ctor_set(v___x_2612_, 2, v___x_2606_);
lean_ctor_set(v___x_2612_, 3, v___x_2586_);
lean_ctor_set(v___x_2612_, 4, v___x_2607_);
lean_ctor_set(v___x_2612_, 5, v___x_2608_);
lean_ctor_set(v___x_2612_, 6, v___x_2593_);
lean_ctor_set(v___x_2612_, 7, v___x_2594_);
lean_ctor_set(v___x_2612_, 8, v___x_2589_);
lean_ctor_set(v___x_2612_, 9, v___x_2609_);
lean_ctor_set(v___x_2612_, 10, v___x_2593_);
lean_ctor_set(v___x_2612_, 11, v___x_2590_);
lean_ctor_set(v___x_2612_, 12, v___x_2611_);
lean_ctor_set(v___x_2612_, 13, v___x_2602_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*14, v___x_2610_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*14 + 1, v___x_2610_);
v_env_2613_ = lean_ctor_get(v___x_2603_, 0);
lean_inc_ref(v_env_2613_);
lean_dec(v___x_2603_);
v___x_2614_ = lean_box(v___y_2580_);
lean_inc(v_docCheckedModules_2416_);
lean_inc(v_pkgRoot_2415_);
v___f_2615_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2615_, 0, v_pkgRoot_2415_);
lean_closure_set(v___f_2615_, 1, v_docCheckedModules_2416_);
lean_closure_set(v___f_2615_, 2, v___x_2614_);
v___x_2616_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2617_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2613_);
lean_dec_ref(v_env_2613_);
if (v___x_2616_ == 0)
{
if (v___x_2617_ == 0)
{
lean_dec_ref_known(v___x_2612_, 14);
lean_inc(v___x_2600_);
v___y_2478_ = v___f_2615_;
v___y_2479_ = v___x_2606_;
v___y_2480_ = v___x_2600_;
v___y_2481_ = v___y_2580_;
v___y_2482_ = v___x_2586_;
v___y_2483_ = v___x_2610_;
v___y_2484_ = v___x_2616_;
v_fileName_2485_ = v___x_2604_;
v_fileMap_2486_ = v___x_2605_;
v_currRecDepth_2487_ = v___x_2586_;
v_ref_2488_ = v___x_2608_;
v_currNamespace_2489_ = v___x_2593_;
v_openDecls_2490_ = v___x_2594_;
v_initHeartbeats_2491_ = v___x_2589_;
v_maxHeartbeats_2492_ = v___x_2609_;
v_quotContext_2493_ = v___x_2593_;
v_currMacroScope_2494_ = v___x_2590_;
v_cancelTk_x3f_2495_ = v___x_2611_;
v_suppressElabErrors_2496_ = v___x_2610_;
v_inheritedTraceOptions_2497_ = v___x_2602_;
v___y_2498_ = v___x_2600_;
goto v___jp_2477_;
}
else
{
lean_dec(v___x_2602_);
lean_dec(v___x_2589_);
v___y_2550_ = v___f_2615_;
v___y_2551_ = v___x_2606_;
v___y_2552_ = v___x_2587_;
v___y_2553_ = v___x_2612_;
v___y_2554_ = v___x_2600_;
v___y_2555_ = v___y_2580_;
v___y_2556_ = v___x_2586_;
v___y_2557_ = v___x_2610_;
v___y_2558_ = v___x_2616_;
v___y_2559_ = v___x_2616_;
goto v___jp_2549_;
}
}
else
{
lean_dec(v___x_2602_);
lean_dec(v___x_2589_);
v___y_2550_ = v___f_2615_;
v___y_2551_ = v___x_2606_;
v___y_2552_ = v___x_2587_;
v___y_2553_ = v___x_2612_;
v___y_2554_ = v___x_2600_;
v___y_2555_ = v___y_2580_;
v___y_2556_ = v___x_2586_;
v___y_2557_ = v___x_2610_;
v___y_2558_ = v___x_2616_;
v___y_2559_ = v___x_2617_;
goto v___jp_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2623_, lean_object* v_linterOpts_2624_, lean_object* v_sp_2625_, lean_object* v_env_2626_, lean_object* v_pkgRoot_2627_, lean_object* v_docCheckedModules_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2623_, v_linterOpts_2624_, v_sp_2625_, v_env_2626_, v_pkgRoot_2627_, v_docCheckedModules_2628_);
lean_dec_ref(v_linterOpts_2624_);
lean_dec_ref(v_args_2623_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2631_, uint8_t v___y_2632_, lean_object* v_as_2633_, size_t v_sz_2634_, size_t v_i_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2631_, v___y_2632_, v_as_2633_, v_sz_2634_, v_i_2635_, v_b_2636_, v___y_2637_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2641_, lean_object* v___y_2642_, lean_object* v_as_2643_, lean_object* v_sz_2644_, lean_object* v_i_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v___y_8062__boxed_2650_; size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v___y_8062__boxed_2650_ = lean_unbox(v___y_2642_);
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2644_);
lean_dec(v_sz_2644_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2645_);
lean_dec(v_i_2645_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2641_, v___y_8062__boxed_2650_, v_as_2643_, v_sz_boxed_2651_, v_i_boxed_2652_, v_b_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec_ref(v_as_2643_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2654_, lean_object* v_as_2655_, size_t v_i_2656_, size_t v_stop_2657_, lean_object* v_b_2658_){
_start:
{
lean_object* v___y_2660_; uint8_t v___x_2664_; 
v___x_2664_ = lean_usize_dec_eq(v_i_2656_, v_stop_2657_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v_linter_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_array_uget_borrowed(v_as_2655_, v_i_2656_);
v_linter_2666_ = lean_ctor_get(v___x_2665_, 0);
v___x_2667_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2666_, v_linterOpts_2654_);
if (v___x_2667_ == 0)
{
v___y_2660_ = v_b_2658_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2668_; 
lean_inc(v___x_2665_);
v___x_2668_ = lean_array_push(v_b_2658_, v___x_2665_);
v___y_2660_ = v___x_2668_;
goto v___jp_2659_;
}
}
else
{
return v_b_2658_;
}
v___jp_2659_:
{
size_t v___x_2661_; size_t v___x_2662_; 
v___x_2661_ = ((size_t)1ULL);
v___x_2662_ = lean_usize_add(v_i_2656_, v___x_2661_);
v_i_2656_ = v___x_2662_;
v_b_2658_ = v___y_2660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2669_, lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_stop_2672_, lean_object* v_b_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2672_);
lean_dec(v_stop_2672_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2669_, v_as_2670_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2673_);
lean_dec_ref(v_as_2670_);
lean_dec_ref(v_linterOpts_2669_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2679_, lean_object* v_as_2680_, size_t v_i_2681_, size_t v_stop_2682_, lean_object* v_b_2683_){
_start:
{
lean_object* v___y_2685_; uint8_t v___x_2689_; 
v___x_2689_ = lean_usize_dec_eq(v_i_2681_, v_stop_2682_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v_fst_2691_; lean_object* v_snd_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2716_; 
v___x_2690_ = lean_array_uget(v_as_2680_, v_i_2681_);
v_fst_2691_ = lean_ctor_get(v___x_2690_, 0);
v_snd_2692_ = lean_ctor_get(v___x_2690_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2694_ = v___x_2690_;
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_snd_2692_);
lean_inc(v_fst_2691_);
lean_dec(v___x_2690_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___y_2697_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v_snd_2692_);
v___x_2707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2708_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2708_ == 0)
{
lean_dec(v_snd_2692_);
v___y_2697_ = v___x_2707_;
goto v___jp_2696_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_le(v___x_2706_, v___x_2706_);
if (v___x_2709_ == 0)
{
if (v___x_2708_ == 0)
{
lean_dec(v_snd_2692_);
v___y_2697_ = v___x_2707_;
goto v___jp_2696_;
}
else
{
size_t v___x_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = ((size_t)0ULL);
v___x_2711_ = lean_usize_of_nat(v___x_2706_);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2679_, v_snd_2692_, v___x_2710_, v___x_2711_, v___x_2707_);
lean_dec(v_snd_2692_);
v___y_2697_ = v___x_2712_;
goto v___jp_2696_;
}
}
else
{
size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((size_t)0ULL);
v___x_2714_ = lean_usize_of_nat(v___x_2706_);
v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2679_, v_snd_2692_, v___x_2713_, v___x_2714_, v___x_2707_);
lean_dec(v_snd_2692_);
v___y_2697_ = v___x_2715_;
goto v___jp_2696_;
}
}
v___jp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = lean_array_get_size(v___y_2697_);
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = lean_nat_dec_eq(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2702_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___y_2697_);
v___x_2702_ = v___x_2694_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_fst_2691_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___y_2697_);
v___x_2702_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_array_push(v_b_2683_, v___x_2702_);
v___y_2685_ = v___x_2703_;
goto v___jp_2684_;
}
}
else
{
lean_dec_ref(v___y_2697_);
lean_del_object(v___x_2694_);
lean_dec(v_fst_2691_);
v___y_2685_ = v_b_2683_;
goto v___jp_2684_;
}
}
}
}
else
{
return v_b_2683_;
}
v___jp_2684_:
{
size_t v___x_2686_; size_t v___x_2687_; 
v___x_2686_ = ((size_t)1ULL);
v___x_2687_ = lean_usize_add(v_i_2681_, v___x_2686_);
v_i_2681_ = v___x_2687_;
v_b_2683_ = v___y_2685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2717_, lean_object* v_as_2718_, lean_object* v_i_2719_, lean_object* v_stop_2720_, lean_object* v_b_2721_){
_start:
{
size_t v_i_boxed_2722_; size_t v_stop_boxed_2723_; lean_object* v_res_2724_; 
v_i_boxed_2722_ = lean_unbox_usize(v_i_2719_);
lean_dec(v_i_2719_);
v_stop_boxed_2723_ = lean_unbox_usize(v_stop_2720_);
lean_dec(v_stop_2720_);
v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2717_, v_as_2718_, v_i_boxed_2722_, v_stop_boxed_2723_, v_b_2721_);
lean_dec_ref(v_as_2718_);
lean_dec_ref(v_linterOpts_2717_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2725_, lean_object* v_as_2726_, lean_object* v_start_2727_, lean_object* v_stop_2728_){
_start:
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2730_ = lean_nat_dec_lt(v_start_2727_, v_stop_2728_);
if (v___x_2730_ == 0)
{
return v___x_2729_;
}
else
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_array_get_size(v_as_2726_);
v___x_2732_ = lean_nat_dec_le(v_stop_2728_, v___x_2731_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_nat_dec_lt(v_start_2727_, v___x_2731_);
if (v___x_2733_ == 0)
{
return v___x_2729_;
}
else
{
size_t v___x_2734_; size_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_usize_of_nat(v_start_2727_);
v___x_2735_ = lean_usize_of_nat(v___x_2731_);
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2725_, v_as_2726_, v___x_2734_, v___x_2735_, v___x_2729_);
return v___x_2736_;
}
}
else
{
size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_usize_of_nat(v_start_2727_);
v___x_2738_ = lean_usize_of_nat(v_stop_2728_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2725_, v_as_2726_, v___x_2737_, v___x_2738_, v___x_2729_);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2740_, lean_object* v_as_2741_, lean_object* v_start_2742_, lean_object* v_stop_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2740_, v_as_2741_, v_start_2742_, v_stop_2743_);
lean_dec(v_stop_2743_);
lean_dec(v_start_2742_);
lean_dec_ref(v_as_2741_);
lean_dec_ref(v_linterOpts_2740_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2745_, lean_object* v_init_2746_, lean_object* v_x_2747_){
_start:
{
if (lean_obj_tag(v_x_2747_) == 0)
{
lean_object* v_k_2749_; lean_object* v_v_2750_; lean_object* v_l_2751_; lean_object* v_r_2752_; lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2769_; 
v_k_2749_ = lean_ctor_get(v_x_2747_, 1);
lean_inc(v_k_2749_);
v_v_2750_ = lean_ctor_get(v_x_2747_, 2);
lean_inc(v_v_2750_);
v_l_2751_ = lean_ctor_get(v_x_2747_, 3);
lean_inc(v_l_2751_);
v_r_2752_ = lean_ctor_get(v_x_2747_, 4);
lean_inc(v_r_2752_);
lean_dec_ref_known(v_x_2747_, 5);
lean_inc(v_fst_2745_);
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2745_, v_init_2746_, v_l_2751_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v___x_2753_);
v_a_2755_ = lean_ctor_get(v_a_2754_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2754_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2757_ = v_a_2754_;
v_isShared_2758_ = v_isSharedCheck_2769_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v_a_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2769_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
uint8_t v_anyUnlocated_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v_anyUnlocated_2759_ = 1;
v___x_2760_ = l_Lean_Name_toString(v_k_2749_, v_anyUnlocated_2759_);
lean_inc(v_fst_2745_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 0);
lean_ctor_set(v___x_2757_, 0, v_fst_2745_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2745_);
v___x_2762_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
double v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = lean_float_of_nat(v_v_2750_);
v___x_2764_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2764_, 0, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2760_);
lean_ctor_set(v___x_2765_, 1, v___x_2762_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
v___x_2766_ = lean_array_push(v_a_2755_, v___x_2765_);
v_init_2746_ = v___x_2766_;
v_x_2747_ = v_r_2752_;
goto _start;
}
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v_fst_2745_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_init_2746_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2772_, lean_object* v_init_2773_, lean_object* v_x_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2772_, v_init_2773_, v_x_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2777_, lean_object* v_k_2778_, lean_object* v_fallback_2779_){
_start:
{
if (lean_obj_tag(v_t_2777_) == 0)
{
lean_object* v_k_2780_; lean_object* v_v_2781_; lean_object* v_l_2782_; lean_object* v_r_2783_; uint8_t v___x_2784_; 
v_k_2780_ = lean_ctor_get(v_t_2777_, 1);
v_v_2781_ = lean_ctor_get(v_t_2777_, 2);
v_l_2782_ = lean_ctor_get(v_t_2777_, 3);
v_r_2783_ = lean_ctor_get(v_t_2777_, 4);
v___x_2784_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2778_, v_k_2780_);
switch(v___x_2784_)
{
case 0:
{
v_t_2777_ = v_l_2782_;
goto _start;
}
case 1:
{
lean_inc(v_v_2781_);
return v_v_2781_;
}
default: 
{
v_t_2777_ = v_r_2783_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2779_);
return v_fallback_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2787_, lean_object* v_k_2788_, lean_object* v_fallback_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2787_, v_k_2788_, v_fallback_2789_);
lean_dec(v_fallback_2789_);
lean_dec(v_k_2788_);
lean_dec(v_t_2787_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2791_, size_t v_i_2792_, size_t v_stop_2793_, lean_object* v_b_2794_){
_start:
{
uint8_t v___x_2795_; 
v___x_2795_ = lean_usize_dec_eq(v_i_2792_, v_stop_2793_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v_linter_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; 
v___x_2796_ = lean_array_uget_borrowed(v_as_2791_, v_i_2792_);
v_linter_2797_ = lean_ctor_get(v___x_2796_, 0);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2794_, v_linter_2797_, v___x_2798_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_add(v___x_2799_, v___x_2800_);
lean_dec(v___x_2799_);
lean_inc(v_linter_2797_);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2797_, v___x_2801_, v_b_2794_);
v___x_2803_ = ((size_t)1ULL);
v___x_2804_ = lean_usize_add(v_i_2792_, v___x_2803_);
v_i_2792_ = v___x_2804_;
v_b_2794_ = v___x_2802_;
goto _start;
}
else
{
return v_b_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2806_, lean_object* v_i_2807_, lean_object* v_stop_2808_, lean_object* v_b_2809_){
_start:
{
size_t v_i_boxed_2810_; size_t v_stop_boxed_2811_; lean_object* v_res_2812_; 
v_i_boxed_2810_ = lean_unbox_usize(v_i_2807_);
lean_dec(v_i_2807_);
v_stop_boxed_2811_ = lean_unbox_usize(v_stop_2808_);
lean_dec(v_stop_2808_);
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2806_, v_i_boxed_2810_, v_stop_boxed_2811_, v_b_2809_);
lean_dec_ref(v_as_2806_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2813_, size_t v_sz_2814_, size_t v_i_2815_, lean_object* v_b_2816_){
_start:
{
lean_object* v_a_2819_; uint8_t v___x_2823_; 
v___x_2823_ = lean_usize_dec_lt(v_i_2815_, v_sz_2814_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_b_2816_);
return v___x_2824_;
}
else
{
lean_object* v_a_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___y_2829_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_a_2825_ = lean_array_uget_borrowed(v_as_2813_, v_i_2815_);
v_fst_2826_ = lean_ctor_get(v_a_2825_, 0);
v_snd_2827_ = lean_ctor_get(v_a_2825_, 1);
v___x_2851_ = lean_box(1);
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = lean_array_get_size(v_snd_2827_);
v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
v___y_2829_ = v___x_2851_;
goto v___jp_2828_;
}
else
{
uint8_t v___x_2855_; 
v___x_2855_ = lean_nat_dec_le(v___x_2853_, v___x_2853_);
if (v___x_2855_ == 0)
{
if (v___x_2854_ == 0)
{
v___y_2829_ = v___x_2851_;
goto v___jp_2828_;
}
else
{
size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = lean_usize_of_nat(v___x_2853_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2827_, v___x_2856_, v___x_2857_, v___x_2851_);
v___y_2829_ = v___x_2858_;
goto v___jp_2828_;
}
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = lean_usize_of_nat(v___x_2853_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2827_, v___x_2859_, v___x_2860_, v___x_2851_);
v___y_2829_ = v___x_2861_;
goto v___jp_2828_;
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; 
lean_inc(v_fst_2826_);
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2826_, v_b_2816_, v___y_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v_a_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v_a_2832_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_a_2832_);
lean_dec(v_a_2831_);
v_a_2819_ = v_a_2832_;
goto v___jp_2818_;
}
else
{
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2842_; 
v_a_2833_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2835_ = v___x_2830_;
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2830_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
if (lean_obj_tag(v_a_2833_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; 
v_a_2837_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v_a_2833_, 1);
if (v_isShared_2836_ == 0)
{
lean_ctor_set_tag(v___x_2835_, 0);
lean_ctor_set(v___x_2835_, 0, v_a_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
lean_object* v_a_2841_; 
lean_del_object(v___x_2835_);
v_a_2841_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v_a_2833_, 1);
v_a_2819_ = v_a_2841_;
goto v___jp_2818_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2830_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2830_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
v___jp_2818_:
{
size_t v___x_2820_; size_t v___x_2821_; 
v___x_2820_ = ((size_t)1ULL);
v___x_2821_ = lean_usize_add(v_i_2815_, v___x_2820_);
v_i_2815_ = v___x_2821_;
v_b_2816_ = v_a_2819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_){
_start:
{
size_t v_sz_boxed_2867_; size_t v_i_boxed_2868_; lean_object* v_res_2869_; 
v_sz_boxed_2867_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2868_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2862_, v_sz_boxed_2867_, v_i_boxed_2868_, v_b_2865_);
lean_dec_ref(v_as_2862_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2873_, lean_object* v_as_2874_, size_t v_sz_2875_, size_t v_i_2876_, lean_object* v_b_2877_){
_start:
{
lean_object* v_a_2880_; uint8_t v_anyUnlocated_2884_; 
v_anyUnlocated_2884_ = lean_usize_dec_lt(v_i_2876_, v_sz_2875_);
if (v_anyUnlocated_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec(v_fst_2873_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_b_2877_);
return v___x_2885_;
}
else
{
lean_object* v_fst_2886_; lean_object* v_snd_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2924_; 
v_fst_2886_ = lean_ctor_get(v_b_2877_, 0);
v_snd_2887_ = lean_ctor_get(v_b_2877_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_b_2877_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2889_ = v_b_2877_;
v_isShared_2890_ = v_isSharedCheck_2924_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snd_2887_);
lean_inc(v_fst_2886_);
lean_dec(v_b_2877_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2924_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v_a_2891_; lean_object* v_position_x3f_2892_; 
v_a_2891_ = lean_array_uget_borrowed(v_as_2874_, v_i_2876_);
v_position_x3f_2892_ = lean_ctor_get(v_a_2891_, 2);
if (lean_obj_tag(v_position_x3f_2892_) == 0)
{
lean_object* v_linter_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_dec(v_snd_2887_);
v_linter_2893_ = lean_ctor_get(v_a_2891_, 0);
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2893_);
v___x_2895_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2893_, v_anyUnlocated_2884_);
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
lean_inc(v_fst_2873_);
v___x_2899_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2873_, v_anyUnlocated_2884_);
v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
v___x_2903_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_dec_ref_known(v___x_2903_, 1);
v___x_2904_ = lean_box(v_anyUnlocated_2884_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v___x_2904_);
v___x_2906_ = v___x_2889_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_fst_2886_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
v_a_2880_ = v___x_2906_;
goto v___jp_2879_;
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2889_);
lean_dec(v_fst_2886_);
lean_dec(v_fst_2873_);
v_a_2908_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2903_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2903_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_linter_2916_; lean_object* v_file_2917_; lean_object* v_val_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v_linter_2916_ = lean_ctor_get(v_a_2891_, 0);
v_file_2917_ = lean_ctor_get(v_a_2891_, 3);
v_val_2918_ = lean_ctor_get(v_position_x3f_2892_, 0);
lean_inc(v_linter_2916_);
lean_inc(v_val_2918_);
lean_inc_ref(v_file_2917_);
v___x_2919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2919_, 0, v_file_2917_);
lean_ctor_set(v___x_2919_, 1, v_val_2918_);
lean_ctor_set(v___x_2919_, 2, v_linter_2916_);
v___x_2920_ = lean_array_push(v_fst_2886_, v___x_2919_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v___x_2920_);
v___x_2922_ = v___x_2889_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_snd_2887_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
v_a_2880_ = v___x_2922_;
goto v___jp_2879_;
}
}
}
}
v___jp_2879_:
{
size_t v___x_2881_; size_t v___x_2882_; 
v___x_2881_ = ((size_t)1ULL);
v___x_2882_ = lean_usize_add(v_i_2876_, v___x_2881_);
v_i_2876_ = v___x_2882_;
v_b_2877_ = v_a_2880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2925_, lean_object* v_as_2926_, lean_object* v_sz_2927_, lean_object* v_i_2928_, lean_object* v_b_2929_, lean_object* v___y_2930_){
_start:
{
size_t v_sz_boxed_2931_; size_t v_i_boxed_2932_; lean_object* v_res_2933_; 
v_sz_boxed_2931_ = lean_unbox_usize(v_sz_2927_);
lean_dec(v_sz_2927_);
v_i_boxed_2932_ = lean_unbox_usize(v_i_2928_);
lean_dec(v_i_2928_);
v_res_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2925_, v_as_2926_, v_sz_boxed_2931_, v_i_boxed_2932_, v_b_2929_);
lean_dec_ref(v_as_2926_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2934_, size_t v_sz_2935_, size_t v_i_2936_, lean_object* v_b_2937_){
_start:
{
uint8_t v___x_2939_; 
v___x_2939_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_b_2937_);
return v___x_2940_;
}
else
{
lean_object* v_a_2941_; lean_object* v_fst_2942_; lean_object* v_snd_2943_; lean_object* v_fst_2944_; lean_object* v_snd_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2968_; 
v_a_2941_ = lean_array_uget_borrowed(v_as_2934_, v_i_2936_);
v_fst_2942_ = lean_ctor_get(v_a_2941_, 0);
v_snd_2943_ = lean_ctor_get(v_a_2941_, 1);
v_fst_2944_ = lean_ctor_get(v_b_2937_, 0);
v_snd_2945_ = lean_ctor_get(v_b_2937_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_b_2937_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2947_ = v_b_2937_;
v_isShared_2948_ = v_isSharedCheck_2968_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snd_2945_);
lean_inc(v_fst_2944_);
lean_dec(v_b_2937_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2968_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_fst_2944_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_snd_2945_);
v___x_2950_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
size_t v_sz_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v_sz_2951_ = lean_array_size(v_snd_2943_);
v___x_2952_ = ((size_t)0ULL);
lean_inc(v_fst_2942_);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2942_, v_snd_2943_, v_sz_2951_, v___x_2952_, v___x_2950_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2966_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v_fst_2955_ = lean_ctor_get(v_a_2954_, 0);
v_snd_2956_ = lean_ctor_get(v_a_2954_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2954_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2958_ = v_a_2954_;
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snd_2956_);
lean_inc(v_fst_2955_);
lean_dec(v_a_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2966_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_fst_2955_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2956_);
v___x_2961_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
size_t v___x_2962_; size_t v___x_2963_; 
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2936_, v___x_2962_);
v_i_2936_ = v___x_2963_;
v_b_2937_ = v___x_2961_;
goto _start;
}
}
}
else
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2969_, lean_object* v_sz_2970_, lean_object* v_i_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_){
_start:
{
size_t v_sz_boxed_2974_; size_t v_i_boxed_2975_; lean_object* v_res_2976_; 
v_sz_boxed_2974_ = lean_unbox_usize(v_sz_2970_);
lean_dec(v_sz_2970_);
v_i_boxed_2975_ = lean_unbox_usize(v_i_2971_);
lean_dec(v_i_2971_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2969_, v_sz_boxed_2974_, v_i_boxed_2975_, v_b_2972_);
lean_dec_ref(v_as_2969_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2977_, size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_b_2980_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_b_2980_);
return v___x_2983_;
}
else
{
lean_object* v_a_2984_; lean_object* v_message_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_a_2984_ = lean_array_uget_borrowed(v_as_2977_, v_i_2979_);
v_message_2985_ = lean_ctor_get(v_a_2984_, 1);
v___x_2986_ = 0;
lean_inc_ref(v_message_2985_);
v___x_2987_ = l_Lean_SerialMessage_toString(v_message_2985_, v___x_2986_);
v___x_2988_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; 
lean_dec_ref_known(v___x_2988_, 1);
v___x_2989_ = lean_box(0);
v___x_2990_ = ((size_t)1ULL);
v___x_2991_ = lean_usize_add(v_i_2979_, v___x_2990_);
v_i_2979_ = v___x_2991_;
v_b_2980_ = v___x_2989_;
goto _start;
}
else
{
return v___x_2988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2993_, lean_object* v_sz_2994_, lean_object* v_i_2995_, lean_object* v_b_2996_, lean_object* v___y_2997_){
_start:
{
size_t v_sz_boxed_2998_; size_t v_i_boxed_2999_; lean_object* v_res_3000_; 
v_sz_boxed_2998_ = lean_unbox_usize(v_sz_2994_);
lean_dec(v_sz_2994_);
v_i_boxed_2999_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2993_, v_sz_boxed_2998_, v_i_boxed_2999_, v_b_2996_);
lean_dec_ref(v_as_2993_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3003_, size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_b_3006_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_b_3006_);
return v___x_3009_;
}
else
{
lean_object* v_a_3010_; lean_object* v_fst_3011_; lean_object* v_snd_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3010_ = lean_array_uget_borrowed(v_as_3003_, v_i_3005_);
v_fst_3011_ = lean_ctor_get(v_a_3010_, 0);
v_snd_3012_ = lean_ctor_get(v_a_3010_, 1);
v___x_3013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3011_);
v___x_3014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3011_, v___x_3008_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
v___x_3018_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; size_t v_sz_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = lean_box(0);
v_sz_3020_ = lean_array_size(v_snd_3012_);
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3012_, v_sz_3020_, v___x_3021_, v___x_3019_);
if (lean_obj_tag(v___x_3022_) == 0)
{
size_t v___x_3023_; size_t v___x_3024_; 
lean_dec_ref_known(v___x_3022_, 1);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_add(v_i_3005_, v___x_3023_);
v_i_3005_ = v___x_3024_;
v_b_3006_ = v___x_3019_;
goto _start;
}
else
{
return v___x_3022_;
}
}
else
{
return v___x_3018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3026_, lean_object* v_sz_3027_, lean_object* v_i_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_){
_start:
{
size_t v_sz_boxed_3031_; size_t v_i_boxed_3032_; lean_object* v_res_3033_; 
v_sz_boxed_3031_ = lean_unbox_usize(v_sz_3027_);
lean_dec(v_sz_3027_);
v_i_boxed_3032_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_res_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3026_, v_sz_boxed_3031_, v_i_boxed_3032_, v_b_3029_);
lean_dec_ref(v_as_3026_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3038_, lean_object* v_linterOpts_3039_, lean_object* v_env_3040_, lean_object* v_mod_3041_){
_start:
{
uint8_t v_lintOnly_3043_; uint8_t v_mode_3044_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3115_; lean_object* v___x_3121_; lean_object* v_textGroups_3122_; 
v_lintOnly_3043_ = lean_ctor_get_uint8(v_args_3038_, sizeof(void*)*4);
v_mode_3044_ = lean_ctor_get_uint8(v_args_3038_, sizeof(void*)*4 + 1);
v___x_3121_ = l_Lean_Name_getRoot(v_mod_3041_);
v_textGroups_3122_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3040_, v___x_3121_);
lean_dec(v___x_3121_);
if (v_lintOnly_3043_ == 0)
{
v___y_3115_ = v_textGroups_3122_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_array_get_size(v_textGroups_3122_);
v___x_3125_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3039_, v_textGroups_3122_, v___x_3123_, v___x_3124_);
lean_dec_ref(v_textGroups_3122_);
v___y_3115_ = v___x_3125_;
goto v___jp_3114_;
}
v___jp_3045_:
{
switch(v_mode_3044_)
{
case 0:
{
lean_object* v___x_3048_; size_t v_sz_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3048_ = lean_box(0);
v_sz_3049_ = lean_array_size(v___y_3046_);
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3046_, v_sz_3049_, v___x_3050_, v___x_3048_);
lean_dec_ref(v___y_3046_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3051_, 0);
lean_dec(v_unused_3060_);
v___x_3053_ = v___x_3051_;
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v___x_3051_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3055_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3055_, 0, v___y_3047_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3055_);
v___x_3057_ = v___x_3053_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3051_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3051_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
case 1:
{
lean_object* v___x_3069_; size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3069_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3070_ = lean_array_size(v___y_3046_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3046_, v_sz_3070_, v___x_3071_, v___x_3069_);
lean_dec_ref(v___y_3046_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3084_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3084_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3084_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v_fst_3077_; lean_object* v_snd_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3082_; 
v_fst_3077_ = lean_ctor_get(v_a_3073_, 0);
lean_inc(v_fst_3077_);
v_snd_3078_ = lean_ctor_get(v_a_3073_, 1);
lean_inc(v_snd_3078_);
lean_dec(v_a_3073_);
v___x_3079_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3079_, 0, v_fst_3077_);
v___x_3080_ = lean_unbox(v_snd_3078_);
lean_dec(v_snd_3078_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*1, v___x_3080_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3079_);
v___x_3082_ = v___x_3075_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3079_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3072_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3072_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3093_; size_t v_sz_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v_codeQualityEntries_3093_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3094_ = lean_array_size(v___y_3046_);
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3046_, v_sz_3094_, v___x_3095_, v_codeQualityEntries_3093_);
lean_dec_ref(v___y_3046_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3105_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3105_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3105_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3101_);
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
v_a_3106_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3096_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3096_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3116_ = lean_array_get_size(v___y_3115_);
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_nat_dec_eq(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
uint8_t v___x_3119_; 
v___x_3119_ = 1;
v___y_3046_ = v___y_3115_;
v___y_3047_ = v___x_3119_;
goto v___jp_3045_;
}
else
{
uint8_t v___x_3120_; 
v___x_3120_ = 0;
v___y_3046_ = v___y_3115_;
v___y_3047_ = v___x_3120_;
goto v___jp_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3126_, lean_object* v_linterOpts_3127_, lean_object* v_env_3128_, lean_object* v_mod_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3126_, v_linterOpts_3127_, v_env_3128_, v_mod_3129_);
lean_dec(v_mod_3129_);
lean_dec_ref(v_env_3128_);
lean_dec_ref(v_linterOpts_3127_);
lean_dec_ref(v_args_3126_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3132_, lean_object* v_t_3133_, lean_object* v_k_3134_, lean_object* v_fallback_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3133_, v_k_3134_, v_fallback_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3137_, lean_object* v_t_3138_, lean_object* v_k_3139_, lean_object* v_fallback_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3137_, v_t_3138_, v_k_3139_, v_fallback_3140_);
lean_dec(v_fallback_3140_);
lean_dec(v_k_3139_);
lean_dec(v_t_3138_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3142_, lean_object* v_____r_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3147_, 0, v___y_3142_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3149_, lean_object* v_____r_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
uint8_t v___y_15714__boxed_3154_; lean_object* v_res_3155_; 
v___y_15714__boxed_3154_ = lean_unbox(v___y_3149_);
v_res_3155_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15714__boxed_3154_, v_____r_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3160_ = lean_unsigned_to_nat(0u);
v___x_3161_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
lean_ctor_set(v___x_3161_, 2, v___x_3160_);
lean_ctor_set(v___x_3161_, 3, v___x_3160_);
lean_ctor_set(v___x_3161_, 4, v___x_3159_);
lean_ctor_set(v___x_3161_, 5, v___x_3159_);
lean_ctor_set(v___x_3161_, 6, v___x_3159_);
lean_ctor_set(v___x_3161_, 7, v___x_3159_);
lean_ctor_set(v___x_3161_, 8, v___x_3159_);
lean_ctor_set(v___x_3161_, 9, v___x_3159_);
lean_ctor_set(v___x_3161_, 10, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_unsigned_to_nat(32u);
v___x_3163_ = lean_mk_empty_array_with_capacity(v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3165_ = ((size_t)5ULL);
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = lean_unsigned_to_nat(32u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3170_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3166_);
lean_ctor_set(v___x_3170_, 3, v___x_3166_);
lean_ctor_set_usize(v___x_3170_, 4, v___x_3165_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3171_ = lean_box(1);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
lean_ctor_set(v___x_3174_, 2, v___x_3171_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___x_3179_; lean_object* v_env_3180_; lean_object* v_options_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3179_ = lean_st_ref_get(v___y_3177_);
v_env_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc_ref(v_env_3180_);
lean_dec(v___x_3179_);
v_options_3181_ = lean_ctor_get(v___y_3176_, 2);
v___x_3182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3181_);
v___x_3184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3184_, 0, v_env_3180_);
lean_ctor_set(v___x_3184_, 1, v___x_3182_);
lean_ctor_set(v___x_3184_, 2, v___x_3183_);
lean_ctor_set(v___x_3184_, 3, v_options_3181_);
v___x_3185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v_msgData_3175_);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_ref_3196_; lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3206_; 
v_ref_3196_ = lean_ctor_get(v___y_3193_, 5);
v___x_3197_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3192_, v___y_3193_, v___y_3194_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_inc(v_ref_3196_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_ref_3196_);
lean_ctor_set(v___x_3202_, 1, v_a_3198_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 1);
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3204_ = v___x_3200_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3212_, lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_fileName_3217_; lean_object* v_fileMap_3218_; lean_object* v_options_3219_; lean_object* v_currRecDepth_3220_; lean_object* v_maxRecDepth_3221_; lean_object* v_ref_3222_; lean_object* v_currNamespace_3223_; lean_object* v_openDecls_3224_; lean_object* v_initHeartbeats_3225_; lean_object* v_maxHeartbeats_3226_; lean_object* v_quotContext_3227_; lean_object* v_currMacroScope_3228_; uint8_t v_diag_3229_; lean_object* v_cancelTk_x3f_3230_; uint8_t v_suppressElabErrors_3231_; lean_object* v_inheritedTraceOptions_3232_; lean_object* v_ref_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_fileName_3217_ = lean_ctor_get(v___y_3214_, 0);
v_fileMap_3218_ = lean_ctor_get(v___y_3214_, 1);
v_options_3219_ = lean_ctor_get(v___y_3214_, 2);
v_currRecDepth_3220_ = lean_ctor_get(v___y_3214_, 3);
v_maxRecDepth_3221_ = lean_ctor_get(v___y_3214_, 4);
v_ref_3222_ = lean_ctor_get(v___y_3214_, 5);
v_currNamespace_3223_ = lean_ctor_get(v___y_3214_, 6);
v_openDecls_3224_ = lean_ctor_get(v___y_3214_, 7);
v_initHeartbeats_3225_ = lean_ctor_get(v___y_3214_, 8);
v_maxHeartbeats_3226_ = lean_ctor_get(v___y_3214_, 9);
v_quotContext_3227_ = lean_ctor_get(v___y_3214_, 10);
v_currMacroScope_3228_ = lean_ctor_get(v___y_3214_, 11);
v_diag_3229_ = lean_ctor_get_uint8(v___y_3214_, sizeof(void*)*14);
v_cancelTk_x3f_3230_ = lean_ctor_get(v___y_3214_, 12);
v_suppressElabErrors_3231_ = lean_ctor_get_uint8(v___y_3214_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3232_ = lean_ctor_get(v___y_3214_, 13);
v_ref_3233_ = l_Lean_replaceRef(v_ref_3212_, v_ref_3222_);
lean_inc_ref(v_inheritedTraceOptions_3232_);
lean_inc(v_cancelTk_x3f_3230_);
lean_inc(v_currMacroScope_3228_);
lean_inc(v_quotContext_3227_);
lean_inc(v_maxHeartbeats_3226_);
lean_inc(v_initHeartbeats_3225_);
lean_inc(v_openDecls_3224_);
lean_inc(v_currNamespace_3223_);
lean_inc(v_maxRecDepth_3221_);
lean_inc(v_currRecDepth_3220_);
lean_inc_ref(v_options_3219_);
lean_inc_ref(v_fileMap_3218_);
lean_inc_ref(v_fileName_3217_);
v___x_3234_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3234_, 0, v_fileName_3217_);
lean_ctor_set(v___x_3234_, 1, v_fileMap_3218_);
lean_ctor_set(v___x_3234_, 2, v_options_3219_);
lean_ctor_set(v___x_3234_, 3, v_currRecDepth_3220_);
lean_ctor_set(v___x_3234_, 4, v_maxRecDepth_3221_);
lean_ctor_set(v___x_3234_, 5, v_ref_3233_);
lean_ctor_set(v___x_3234_, 6, v_currNamespace_3223_);
lean_ctor_set(v___x_3234_, 7, v_openDecls_3224_);
lean_ctor_set(v___x_3234_, 8, v_initHeartbeats_3225_);
lean_ctor_set(v___x_3234_, 9, v_maxHeartbeats_3226_);
lean_ctor_set(v___x_3234_, 10, v_quotContext_3227_);
lean_ctor_set(v___x_3234_, 11, v_currMacroScope_3228_);
lean_ctor_set(v___x_3234_, 12, v_cancelTk_x3f_3230_);
lean_ctor_set(v___x_3234_, 13, v_inheritedTraceOptions_3232_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*14, v_diag_3229_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*14 + 1, v_suppressElabErrors_3231_);
v___x_3235_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3213_, v___x_3234_, v___y_3215_);
lean_dec_ref_known(v___x_3234_, 14);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3236_, lean_object* v_msg_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3236_, v_msg_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v_ref_3236_);
return v_res_3241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3247_ = l_Lean_stringToMessageData(v___x_3246_);
return v___x_3247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3250_ = l_Lean_stringToMessageData(v___x_3249_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3253_ = l_Lean_stringToMessageData(v___x_3252_);
return v___x_3253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3256_ = l_Lean_stringToMessageData(v___x_3255_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3259_ = l_Lean_stringToMessageData(v___x_3258_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3262_ = l_Lean_stringToMessageData(v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3263_, lean_object* v_declHint_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; lean_object* v_env_3268_; uint8_t v___x_3269_; 
v___x_3267_ = lean_st_ref_get(v___y_3265_);
v_env_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc_ref(v_env_3268_);
lean_dec(v___x_3267_);
v___x_3269_ = l_Lean_Name_isAnonymous(v_declHint_3264_);
if (v___x_3269_ == 0)
{
uint8_t v_isExporting_3270_; 
v_isExporting_3270_ = lean_ctor_get_uint8(v_env_3268_, sizeof(void*)*8);
if (v_isExporting_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3264_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_msg_3263_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
lean_inc_ref(v_env_3268_);
v___x_3272_ = l_Lean_Environment_setExporting(v_env_3268_, v___x_3269_);
lean_inc(v_declHint_3264_);
lean_inc_ref(v___x_3272_);
v___x_3273_ = l_Lean_Environment_contains(v___x_3272_, v_declHint_3264_, v_isExporting_3270_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3264_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_msg_3263_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v_c_3280_; lean_object* v___x_3281_; 
v___x_3275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3276_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3277_ = l_Lean_Options_empty;
v___x_3278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3272_);
lean_ctor_set(v___x_3278_, 1, v___x_3275_);
lean_ctor_set(v___x_3278_, 2, v___x_3276_);
lean_ctor_set(v___x_3278_, 3, v___x_3277_);
lean_inc(v_declHint_3264_);
v___x_3279_ = l_Lean_MessageData_ofConstName(v_declHint_3264_, v___x_3269_);
v_c_3280_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3280_, 0, v___x_3278_);
lean_ctor_set(v_c_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3268_, v_declHint_3264_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3264_);
v___x_3282_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_c_3280_);
v___x_3284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_MessageData_note(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_msg_3263_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
return v___x_3288_;
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3324_; 
v_val_3289_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3291_ = v___x_3281_;
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_val_3289_);
lean_dec(v___x_3281_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v_mod_3296_; uint8_t v___x_3297_; 
v___x_3293_ = lean_box(0);
v___x_3294_ = l_Lean_Environment_header(v_env_3268_);
lean_dec_ref(v_env_3268_);
v___x_3295_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3294_);
v_mod_3296_ = lean_array_get(v___x_3293_, v___x_3295_, v_val_3289_);
lean_dec(v_val_3289_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = l_Lean_isPrivateName(v_declHint_3264_);
lean_dec(v_declHint_3264_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v_c_3280_);
v___x_3300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_MessageData_ofName(v_mod_3296_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = l_Lean_MessageData_note(v___x_3305_);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_msg_3263_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3307_);
v___x_3309_ = v___x_3291_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v_c_3280_);
v___x_3313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_MessageData_ofName(v_mod_3296_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = l_Lean_MessageData_note(v___x_3318_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v_msg_3263_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3320_);
v___x_3322_ = v___x_3291_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3325_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3264_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_msg_3263_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3326_, lean_object* v_declHint_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3326_, v_declHint_3327_, v___y_3328_);
lean_dec(v___y_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3331_, lean_object* v_declHint_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3346_; 
v___x_3336_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3331_, v_declHint_3332_, v___y_3334_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = l_Lean_unknownIdentifierMessageTag;
v___x_3342_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v_a_3337_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3342_);
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3347_, lean_object* v_declHint_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3347_, v_declHint_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3353_, lean_object* v_msg_3354_, lean_object* v_declHint_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v_a_3360_; lean_object* v___x_3361_; 
v___x_3359_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3354_, v_declHint_3355_, v___y_3356_, v___y_3357_);
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3353_, v_a_3360_, v___y_3356_, v___y_3357_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3362_, lean_object* v_msg_3363_, lean_object* v_declHint_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3362_, v_msg_3363_, v_declHint_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v_ref_3362_);
return v_res_3368_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3371_ = l_Lean_stringToMessageData(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3374_, lean_object* v_constName_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3379_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3380_ = 0;
lean_inc(v_constName_3375_);
v___x_3381_ = l_Lean_MessageData_ofConstName(v_constName_3375_, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3379_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3374_, v___x_3384_, v_constName_3375_, v___y_3376_, v___y_3377_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3386_, lean_object* v_constName_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3386_, v_constName_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v_ref_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_ref_3396_; lean_object* v___x_3397_; 
v_ref_3396_ = lean_ctor_get(v___y_3393_, 5);
v___x_3397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3396_, v_constName_3392_, v___y_3393_, v___y_3394_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; lean_object* v_env_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_st_ref_get(v___y_3405_);
v_env_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc_ref(v_env_3408_);
lean_dec(v___x_3407_);
v___x_3409_ = 0;
lean_inc(v_constName_3403_);
v___x_3410_ = l_Lean_Environment_find_x3f(v_env_3408_, v_constName_3403_, v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3403_, v___y_3404_, v___y_3405_);
return v___x_3411_;
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_constName_3403_);
v_val_3412_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3410_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v___x_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set_tag(v___x_3414_, 0);
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_val_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
lean_inc(v_declName_3425_);
v___x_3429_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3456_; 
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v___x_3429_, 0);
lean_dec(v_unused_3457_);
v___x_3431_ = v___x_3429_;
v_isShared_3432_ = v_isSharedCheck_3456_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v___x_3429_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3456_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v_env_3434_; lean_object* v___x_3435_; 
v___x_3433_ = lean_st_ref_get(v___y_3427_);
v_env_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3434_);
lean_dec(v___x_3433_);
v___x_3435_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3434_, v_declName_3425_);
lean_dec(v_declName_3425_);
lean_dec_ref(v_env_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_box(0);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3436_);
v___x_3438_ = v___x_3431_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
else
{
lean_object* v_val_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3455_; 
v_val_3440_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3442_ = v___x_3435_;
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_val_3440_);
lean_dec(v___x_3435_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v_env_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3444_ = lean_st_ref_get(v___y_3427_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3446_ = lean_box(0);
v___x_3447_ = l_Lean_Environment_allImportedModuleNames(v_env_3445_);
lean_dec_ref(v_env_3445_);
v___x_3448_ = lean_array_get(v___x_3446_, v___x_3447_, v_val_3440_);
lean_dec(v_val_3440_);
lean_dec_ref(v___x_3447_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3448_);
v___x_3450_ = v___x_3442_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3450_);
v___x_3452_ = v___x_3431_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_declName_3425_);
v_a_3458_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3429_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3429_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3472_, lean_object* v_sp_3473_, lean_object* v___x_3474_, lean_object* v_as_3475_, size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_a_3483_; uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3478_);
return v___x_3488_;
}
else
{
lean_object* v_a_3489_; lean_object* v_fst_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3625_; 
v_a_3489_ = lean_array_uget(v_as_3475_, v_i_3477_);
v_fst_3490_ = lean_ctor_get(v_a_3489_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; 
v_unused_3626_ = lean_ctor_get(v_a_3489_, 1);
lean_dec(v_unused_3626_);
v___x_3492_ = v_a_3489_;
v_isShared_3493_ = v_isSharedCheck_3625_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_fst_3490_);
lean_dec(v_a_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3625_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; 
lean_inc(v_fst_3490_);
v___x_3494_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3490_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
if (lean_obj_tag(v_a_3495_) == 0)
{
lean_object* v_fst_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3530_; 
v_fst_3496_ = lean_ctor_get(v_b_3478_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_b_3478_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v_b_3478_, 1);
lean_dec(v_unused_3531_);
v___x_3498_ = v_b_3478_;
v_isShared_3499_ = v_isSharedCheck_3530_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_fst_3496_);
lean_dec(v_b_3478_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3530_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_optName_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_optName_3500_ = lean_ctor_get(v_fst_3472_, 1);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3490_, v___x_3487_);
v___x_3503_ = lean_string_append(v___x_3501_, v___x_3502_);
lean_dec_ref(v___x_3502_);
v___x_3504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3505_ = lean_string_append(v___x_3503_, v___x_3504_);
lean_inc(v_optName_3500_);
v___x_3506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3500_, v___x_3487_);
v___x_3507_ = lean_string_append(v___x_3505_, v___x_3506_);
lean_dec_ref(v___x_3506_);
v___x_3508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3509_ = lean_string_append(v___x_3507_, v___x_3508_);
v___x_3510_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec_ref_known(v___x_3510_, 1);
lean_del_object(v___x_3492_);
v___x_3511_ = lean_box(v___x_3487_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v___x_3511_);
v___x_3513_ = v___x_3498_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_fst_3496_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
v_a_3483_ = v___x_3513_;
goto v___jp_3482_;
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3529_; 
lean_del_object(v___x_3498_);
lean_dec(v_fst_3496_);
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v_a_3515_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3517_ = v___x_3510_;
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3510_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_ref_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_ref_3519_ = lean_ctor_get(v___y_3479_, 5);
v___x_3520_ = lean_io_error_to_string(v_a_3515_);
v___x_3521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v___x_3522_ = l_Lean_MessageData_ofFormat(v___x_3521_);
lean_inc(v_ref_3519_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3522_);
lean_ctor_set(v___x_3492_, 0, v_ref_3519_);
v___x_3524_ = v___x_3492_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_ref_3519_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3526_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3524_);
v___x_3526_ = v___x_3517_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3532_; lean_object* v_snd_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3616_; 
v_fst_3532_ = lean_ctor_get(v_b_3478_, 0);
v_snd_3533_ = lean_ctor_get(v_b_3478_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_b_3478_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3535_ = v_b_3478_;
v_isShared_3536_ = v_isSharedCheck_3616_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3533_);
lean_inc(v_fst_3532_);
lean_dec(v_b_3478_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3616_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_val_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3615_; 
v_val_3537_ = lean_ctor_get(v_a_3495_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3539_ = v_a_3495_;
v_isShared_3540_ = v_isSharedCheck_3615_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_val_3537_);
lean_dec(v_a_3495_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3615_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3490_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___y_3544_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
if (lean_obj_tag(v_a_3542_) == 0)
{
lean_inc(v___x_3474_);
v___y_3544_ = v___x_3474_;
goto v___jp_3543_;
}
else
{
lean_object* v_val_3606_; 
v_val_3606_ = lean_ctor_get(v_a_3542_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v_a_3542_, 1);
v___y_3544_ = v_val_3606_;
goto v___jp_3543_;
}
v___jp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3544_);
lean_inc(v_sp_3473_);
v___x_3546_ = l_Lean_SearchPath_findWithExt(v_sp_3473_, v___x_3545_, v___y_3544_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
if (lean_obj_tag(v_a_3547_) == 0)
{
lean_object* v_optName_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v_val_3537_);
lean_dec(v_snd_3533_);
v_optName_3548_ = lean_ctor_get(v_fst_3472_, 1);
v___x_3549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3544_, v___x_3487_);
v___x_3551_ = lean_string_append(v___x_3549_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3553_ = lean_string_append(v___x_3551_, v___x_3552_);
lean_inc(v_optName_3548_);
v___x_3554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3548_, v___x_3487_);
v___x_3555_ = lean_string_append(v___x_3553_, v___x_3554_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3557_ = lean_string_append(v___x_3555_, v___x_3556_);
v___x_3558_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_dec_ref_known(v___x_3558_, 1);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3492_);
v___x_3559_ = lean_box(v___x_3487_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v___x_3559_);
v___x_3561_ = v___x_3535_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_fst_3532_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
v_a_3483_ = v___x_3561_;
goto v___jp_3482_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3579_; 
lean_del_object(v___x_3535_);
lean_dec(v_fst_3532_);
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v_a_3563_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3565_ = v___x_3558_;
v_isShared_3566_ = v_isSharedCheck_3579_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3558_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3579_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v_ref_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v_ref_3567_ = lean_ctor_get(v___y_3479_, 5);
v___x_3568_ = lean_io_error_to_string(v_a_3563_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 3);
lean_ctor_set(v___x_3539_, 0, v___x_3568_);
v___x_3570_ = v___x_3539_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = l_Lean_MessageData_ofFormat(v___x_3570_);
lean_inc(v_ref_3567_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3571_);
lean_ctor_set(v___x_3492_, 0, v_ref_3567_);
v___x_3573_ = v___x_3492_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_ref_3567_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3575_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3573_);
v___x_3575_ = v___x_3565_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
}
else
{
lean_object* v_range_3580_; lean_object* v_val_3581_; lean_object* v_pos_3582_; lean_object* v_optName_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
lean_dec(v___y_3544_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3492_);
v_range_3580_ = lean_ctor_get(v_val_3537_, 0);
lean_inc_ref(v_range_3580_);
lean_dec(v_val_3537_);
v_val_3581_ = lean_ctor_get(v_a_3547_, 0);
lean_inc(v_val_3581_);
lean_dec_ref_known(v_a_3547_, 1);
v_pos_3582_ = lean_ctor_get(v_range_3580_, 0);
lean_inc_ref(v_pos_3582_);
lean_dec_ref(v_range_3580_);
v_optName_3583_ = lean_ctor_get(v_fst_3472_, 1);
lean_inc(v_optName_3583_);
v___x_3584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3584_, 0, v_val_3581_);
lean_ctor_set(v___x_3584_, 1, v_pos_3582_);
lean_ctor_set(v___x_3584_, 2, v_optName_3583_);
v___x_3585_ = lean_array_push(v_fst_3532_, v___x_3584_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3585_);
v___x_3587_ = v___x_3535_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_snd_3533_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
v_a_3483_ = v___x_3587_;
goto v___jp_3482_;
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3605_; 
lean_dec(v___y_3544_);
lean_dec(v_val_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_snd_3533_);
lean_dec(v_fst_3532_);
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v_a_3589_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3591_ = v___x_3546_;
v_isShared_3592_ = v_isSharedCheck_3605_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3546_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3605_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_ref_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v_ref_3593_ = lean_ctor_get(v___y_3479_, 5);
v___x_3594_ = lean_io_error_to_string(v_a_3589_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 3);
lean_ctor_set(v___x_3539_, 0, v___x_3594_);
v___x_3596_ = v___x_3539_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3597_ = l_Lean_MessageData_ofFormat(v___x_3596_);
lean_inc(v_ref_3593_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3597_);
lean_ctor_set(v___x_3492_, 0, v_ref_3593_);
v___x_3599_ = v___x_3492_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_ref_3593_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3599_);
v___x_3601_ = v___x_3591_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_del_object(v___x_3539_);
lean_dec(v_val_3537_);
lean_del_object(v___x_3535_);
lean_dec(v_snd_3533_);
lean_dec(v_fst_3532_);
lean_del_object(v___x_3492_);
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v_a_3607_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3541_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3541_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_del_object(v___x_3492_);
lean_dec(v_fst_3490_);
lean_dec_ref(v_b_3478_);
lean_dec(v___x_3474_);
lean_dec(v_sp_3473_);
lean_dec_ref(v_fst_3472_);
v_a_3617_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3494_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3494_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
v___jp_3482_:
{
size_t v___x_3484_; size_t v___x_3485_; 
v___x_3484_ = ((size_t)1ULL);
v___x_3485_ = lean_usize_add(v_i_3477_, v___x_3484_);
v_i_3477_ = v___x_3485_;
v_b_3478_ = v_a_3483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3627_, lean_object* v_sp_3628_, lean_object* v___x_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3627_, v_sp_3628_, v___x_3629_, v_as_3630_, v_sz_boxed_3637_, v_i_boxed_3638_, v_b_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v_as_3630_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3640_, lean_object* v_x_3641_){
_start:
{
if (lean_obj_tag(v_x_3641_) == 0)
{
return v_x_3640_;
}
else
{
lean_object* v_key_3642_; lean_object* v_value_3643_; lean_object* v_tail_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_key_3642_ = lean_ctor_get(v_x_3641_, 0);
v_value_3643_ = lean_ctor_get(v_x_3641_, 1);
v_tail_3644_ = lean_ctor_get(v_x_3641_, 2);
lean_inc(v_value_3643_);
lean_inc(v_key_3642_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_key_3642_);
lean_ctor_set(v___x_3645_, 1, v_value_3643_);
v___x_3646_ = lean_array_push(v_x_3640_, v___x_3645_);
v_x_3640_ = v___x_3646_;
v_x_3641_ = v_tail_3644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3648_, v_x_3649_);
lean_dec(v_x_3649_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3651_, size_t v_i_3652_, size_t v_stop_3653_, lean_object* v_b_3654_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_usize_dec_eq(v_i_3652_, v_stop_3653_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; size_t v___x_3658_; size_t v___x_3659_; 
v___x_3656_ = lean_array_uget_borrowed(v_as_3651_, v_i_3652_);
v___x_3657_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3654_, v___x_3656_);
v___x_3658_ = ((size_t)1ULL);
v___x_3659_ = lean_usize_add(v_i_3652_, v___x_3658_);
v_i_3652_ = v___x_3659_;
v_b_3654_ = v___x_3657_;
goto _start;
}
else
{
return v_b_3654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3661_, lean_object* v_i_3662_, lean_object* v_stop_3663_, lean_object* v_b_3664_){
_start:
{
size_t v_i_boxed_3665_; size_t v_stop_boxed_3666_; lean_object* v_res_3667_; 
v_i_boxed_3665_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_stop_boxed_3666_ = lean_unbox_usize(v_stop_3663_);
lean_dec(v_stop_3663_);
v_res_3667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3661_, v_i_boxed_3665_, v_stop_boxed_3666_, v_b_3664_);
lean_dec_ref(v_as_3661_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3668_, lean_object* v___x_3669_, lean_object* v_as_3670_, size_t v_sz_3671_, size_t v_i_3672_, lean_object* v_b_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v___x_3677_; 
v___x_3677_ = lean_usize_dec_lt(v_i_3672_, v_sz_3671_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
lean_dec(v___x_3669_);
lean_dec(v_sp_3668_);
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v_b_3673_);
return v___x_3678_;
}
else
{
lean_object* v_a_3679_; lean_object* v_fst_3680_; lean_object* v_snd_3681_; lean_object* v_fst_3682_; lean_object* v_snd_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3717_; 
v_a_3679_ = lean_array_uget_borrowed(v_as_3670_, v_i_3672_);
v_fst_3680_ = lean_ctor_get(v_a_3679_, 0);
v_snd_3681_ = lean_ctor_get(v_a_3679_, 1);
v_fst_3682_ = lean_ctor_get(v_b_3673_, 0);
v_snd_3683_ = lean_ctor_get(v_b_3673_, 1);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_b_3673_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3685_ = v_b_3673_;
v_isShared_3686_ = v_isSharedCheck_3717_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_snd_3683_);
lean_inc(v_fst_3682_);
lean_dec(v_b_3673_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3717_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___y_3688_; lean_object* v_size_3708_; lean_object* v_buckets_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v_size_3708_ = lean_ctor_get(v_snd_3681_, 0);
v_buckets_3709_ = lean_ctor_get(v_snd_3681_, 1);
v___x_3710_ = lean_mk_empty_array_with_capacity(v_size_3708_);
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v_buckets_3709_);
v___x_3713_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
v___y_3688_ = v___x_3710_;
goto v___jp_3687_;
}
else
{
size_t v___x_3714_; size_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = lean_usize_of_nat(v___x_3712_);
v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3709_, v___x_3714_, v___x_3715_, v___x_3710_);
v___y_3688_ = v___x_3716_;
goto v___jp_3687_;
}
v___jp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3686_ == 0)
{
v___x_3690_ = v___x_3685_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_fst_3682_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_snd_3683_);
v___x_3690_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
size_t v_sz_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v_sz_3691_ = lean_array_size(v___y_3688_);
v___x_3692_ = ((size_t)0ULL);
lean_inc(v___x_3669_);
lean_inc(v_sp_3668_);
lean_inc(v_fst_3680_);
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3680_, v_sp_3668_, v___x_3669_, v___y_3688_, v_sz_3691_, v___x_3692_, v___x_3690_, v___y_3674_, v___y_3675_);
lean_dec_ref(v___y_3688_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_fst_3695_; lean_object* v_snd_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3706_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_fst_3695_ = lean_ctor_get(v_a_3694_, 0);
v_snd_3696_ = lean_ctor_get(v_a_3694_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3698_ = v_a_3694_;
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_snd_3696_);
lean_inc(v_fst_3695_);
lean_dec(v_a_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_fst_3695_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_snd_3696_);
v___x_3701_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
size_t v___x_3702_; size_t v___x_3703_; 
v___x_3702_ = ((size_t)1ULL);
v___x_3703_ = lean_usize_add(v_i_3672_, v___x_3702_);
v_i_3672_ = v___x_3703_;
v_b_3673_ = v___x_3701_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3669_);
lean_dec(v_sp_3668_);
return v___x_3693_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3718_, lean_object* v___x_3719_, lean_object* v_as_3720_, lean_object* v_sz_3721_, lean_object* v_i_3722_, lean_object* v_b_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
size_t v_sz_boxed_3727_; size_t v_i_boxed_3728_; lean_object* v_res_3729_; 
v_sz_boxed_3727_ = lean_unbox_usize(v_sz_3721_);
lean_dec(v_sz_3721_);
v_i_boxed_3728_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3718_, v___x_3719_, v_as_3720_, v_sz_boxed_3727_, v_i_boxed_3728_, v_b_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec_ref(v_as_3720_);
return v_res_3729_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3730_, lean_object* v_as_3731_, size_t v_i_3732_, size_t v_stop_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_usize_dec_eq(v_i_3732_, v_stop_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; lean_object* v_snd_3736_; lean_object* v_size_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3735_ = lean_array_uget_borrowed(v_as_3731_, v_i_3732_);
v_snd_3736_ = lean_ctor_get(v___x_3735_, 1);
v_size_3737_ = lean_ctor_get(v_snd_3736_, 0);
v___x_3738_ = 1;
v___x_3739_ = lean_unsigned_to_nat(0u);
v___x_3740_ = lean_nat_dec_eq(v_size_3737_, v___x_3739_);
if (v___x_3740_ == 0)
{
return v___x_3738_;
}
else
{
if (v___y_3730_ == 0)
{
size_t v___x_3741_; size_t v___x_3742_; 
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3732_, v___x_3741_);
v_i_3732_ = v___x_3742_;
goto _start;
}
else
{
return v___x_3738_;
}
}
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = 0;
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3745_, lean_object* v_as_3746_, lean_object* v_i_3747_, lean_object* v_stop_3748_){
_start:
{
uint8_t v___y_16698__boxed_3749_; size_t v_i_boxed_3750_; size_t v_stop_boxed_3751_; uint8_t v_res_3752_; lean_object* v_r_3753_; 
v___y_16698__boxed_3749_ = lean_unbox(v___y_3745_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3747_);
lean_dec(v_i_3747_);
v_stop_boxed_3751_ = lean_unbox_usize(v_stop_3748_);
lean_dec(v_stop_3748_);
v_res_3752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16698__boxed_3749_, v_as_3746_, v_i_boxed_3750_, v_stop_boxed_3751_);
lean_dec_ref(v_as_3746_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3754_, lean_object* v_v_3755_, lean_object* v_t_3756_){
_start:
{
lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; 
if (lean_obj_tag(v_t_3756_) == 0)
{
lean_object* v_size_3771_; lean_object* v_k_3772_; lean_object* v_v_3773_; lean_object* v_l_3774_; lean_object* v_r_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_4035_; 
v_size_3771_ = lean_ctor_get(v_t_3756_, 0);
v_k_3772_ = lean_ctor_get(v_t_3756_, 1);
v_v_3773_ = lean_ctor_get(v_t_3756_, 2);
v_l_3774_ = lean_ctor_get(v_t_3756_, 3);
v_r_3775_ = lean_ctor_get(v_t_3756_, 4);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_t_3756_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_3777_ = v_t_3756_;
v_isShared_3778_ = v_isSharedCheck_4035_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_r_3775_);
lean_inc(v_l_3774_);
lean_inc(v_v_3773_);
lean_inc(v_k_3772_);
lean_inc(v_size_3771_);
lean_dec(v_t_3756_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_4035_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; uint8_t v___y_3829_; lean_object* v_fst_4029_; lean_object* v_snd_4030_; lean_object* v_fst_4031_; lean_object* v_snd_4032_; uint8_t v___x_4033_; 
v_fst_4029_ = lean_ctor_get(v_k_3754_, 0);
v_snd_4030_ = lean_ctor_get(v_k_3754_, 1);
v_fst_4031_ = lean_ctor_get(v_k_3772_, 0);
v_snd_4032_ = lean_ctor_get(v_k_3772_, 1);
v___x_4033_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4029_, v_fst_4031_);
if (v___x_4033_ == 1)
{
uint8_t v___x_4034_; 
v___x_4034_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4030_, v_snd_4032_);
v___y_3829_ = v___x_4034_;
goto v___jp_3828_;
}
else
{
v___y_3829_ = v___x_4033_;
goto v___jp_3828_;
}
v___jp_3779_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_nat_add(v___y_3784_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec(v___y_3784_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 3, v___y_3785_);
lean_ctor_set(v___x_3777_, 0, v___x_3787_);
v___x_3789_ = v___x_3777_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3791_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3791_, 3, v___y_3785_);
lean_ctor_set(v_reuseFailAlloc_3791_, 4, v_r_3775_);
v___x_3789_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3790_, 0, v___y_3780_);
lean_ctor_set(v___x_3790_, 1, v___y_3783_);
lean_ctor_set(v___x_3790_, 2, v___y_3781_);
lean_ctor_set(v___x_3790_, 3, v___y_3782_);
lean_ctor_set(v___x_3790_, 4, v___x_3789_);
return v___x_3790_;
}
}
v___jp_3792_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = lean_nat_add(v___y_3796_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec(v___y_3796_);
v___x_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___y_3798_);
lean_ctor_set(v___x_3806_, 2, v___y_3795_);
lean_ctor_set(v___x_3806_, 3, v___y_3803_);
lean_ctor_set(v___x_3806_, 4, v___y_3799_);
v___x_3807_ = lean_nat_add(v___y_3802_, v___y_3801_);
lean_dec(v___y_3801_);
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_object* v_size_3808_; 
v_size_3808_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_size_3808_);
v___y_3780_ = v___y_3793_;
v___y_3781_ = v___y_3794_;
v___y_3782_ = v___x_3806_;
v___y_3783_ = v___y_3797_;
v___y_3784_ = v___x_3807_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v_size_3808_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_unsigned_to_nat(0u);
v___y_3780_ = v___y_3793_;
v___y_3781_ = v___y_3794_;
v___y_3782_ = v___x_3806_;
v___y_3783_ = v___y_3797_;
v___y_3784_ = v___x_3807_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v___x_3809_;
goto v___jp_3779_;
}
}
v___jp_3810_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = lean_nat_add(v___y_3813_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec(v___y_3813_);
v___x_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v_k_3772_);
lean_ctor_set(v___x_3824_, 2, v_v_3773_);
lean_ctor_set(v___x_3824_, 3, v_l_3774_);
lean_ctor_set(v___x_3824_, 4, v___y_3815_);
v___x_3825_ = lean_nat_add(v___y_3820_, v___y_3816_);
lean_dec(v___y_3816_);
if (lean_obj_tag(v___y_3821_) == 0)
{
lean_object* v_size_3826_; 
v_size_3826_ = lean_ctor_get(v___y_3821_, 0);
lean_inc(v_size_3826_);
v___y_3758_ = v___y_3811_;
v___y_3759_ = v___y_3812_;
v___y_3760_ = v___y_3814_;
v___y_3761_ = v___y_3817_;
v___y_3762_ = v___y_3819_;
v___y_3763_ = v___y_3818_;
v___y_3764_ = v___x_3825_;
v___y_3765_ = v___y_3821_;
v___y_3766_ = v___x_3824_;
v___y_3767_ = v_size_3826_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_unsigned_to_nat(0u);
v___y_3758_ = v___y_3811_;
v___y_3759_ = v___y_3812_;
v___y_3760_ = v___y_3814_;
v___y_3761_ = v___y_3817_;
v___y_3762_ = v___y_3819_;
v___y_3763_ = v___y_3818_;
v___y_3764_ = v___x_3825_;
v___y_3765_ = v___y_3821_;
v___y_3766_ = v___x_3824_;
v___y_3767_ = v___x_3827_;
goto v___jp_3757_;
}
}
v___jp_3828_:
{
switch(v___y_3829_)
{
case 0:
{
lean_object* v_impl_3830_; lean_object* v___x_3831_; 
lean_dec(v_size_3771_);
v_impl_3830_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3754_, v_v_3755_, v_l_3774_);
v___x_3831_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3775_) == 0)
{
lean_object* v_size_3832_; lean_object* v_size_3833_; lean_object* v_k_3834_; lean_object* v_v_3835_; lean_object* v_l_3836_; lean_object* v_r_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_size_3832_ = lean_ctor_get(v_r_3775_, 0);
v_size_3833_ = lean_ctor_get(v_impl_3830_, 0);
lean_inc(v_size_3833_);
v_k_3834_ = lean_ctor_get(v_impl_3830_, 1);
lean_inc(v_k_3834_);
v_v_3835_ = lean_ctor_get(v_impl_3830_, 2);
lean_inc(v_v_3835_);
v_l_3836_ = lean_ctor_get(v_impl_3830_, 3);
lean_inc(v_l_3836_);
v_r_3837_ = lean_ctor_get(v_impl_3830_, 4);
lean_inc(v_r_3837_);
v___x_3838_ = lean_unsigned_to_nat(3u);
v___x_3839_ = lean_nat_mul(v___x_3838_, v_size_3832_);
v___x_3840_ = lean_nat_dec_lt(v___x_3839_, v_size_3833_);
lean_dec(v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec(v_r_3837_);
lean_dec(v_l_3836_);
lean_dec(v_v_3835_);
lean_dec(v_k_3834_);
lean_del_object(v___x_3777_);
v___x_3841_ = lean_nat_add(v___x_3831_, v_size_3833_);
lean_dec(v_size_3833_);
v___x_3842_ = lean_nat_add(v___x_3841_, v_size_3832_);
lean_dec(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set(v___x_3843_, 1, v_k_3772_);
lean_ctor_set(v___x_3843_, 2, v_v_3773_);
lean_ctor_set(v___x_3843_, 3, v_impl_3830_);
lean_ctor_set(v___x_3843_, 4, v_r_3775_);
return v___x_3843_;
}
else
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3880_; 
v_isSharedCheck_3880_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3880_ == 0)
{
lean_object* v_unused_3881_; lean_object* v_unused_3882_; lean_object* v_unused_3883_; lean_object* v_unused_3884_; lean_object* v_unused_3885_; 
v_unused_3881_ = lean_ctor_get(v_impl_3830_, 4);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_impl_3830_, 2);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_impl_3830_, 1);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3885_);
v___x_3845_ = v_impl_3830_;
v_isShared_3846_ = v_isSharedCheck_3880_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v_impl_3830_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3880_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_size_3847_; lean_object* v_size_3848_; lean_object* v_k_3849_; lean_object* v_v_3850_; lean_object* v_l_3851_; lean_object* v_r_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_size_3847_ = lean_ctor_get(v_l_3836_, 0);
v_size_3848_ = lean_ctor_get(v_r_3837_, 0);
v_k_3849_ = lean_ctor_get(v_r_3837_, 1);
v_v_3850_ = lean_ctor_get(v_r_3837_, 2);
v_l_3851_ = lean_ctor_get(v_r_3837_, 3);
v_r_3852_ = lean_ctor_get(v_r_3837_, 4);
v___x_3853_ = lean_unsigned_to_nat(2u);
v___x_3854_ = lean_nat_mul(v___x_3853_, v_size_3847_);
v___x_3855_ = lean_nat_dec_lt(v_size_3848_, v___x_3854_);
lean_dec(v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_inc(v_r_3852_);
lean_inc(v_l_3851_);
lean_inc(v_v_3850_);
lean_inc(v_k_3849_);
lean_del_object(v___x_3845_);
lean_dec(v_r_3837_);
v___x_3856_ = lean_nat_add(v___x_3831_, v_size_3833_);
lean_dec(v_size_3833_);
v___x_3857_ = lean_nat_add(v___x_3856_, v_size_3832_);
lean_dec(v___x_3856_);
v___x_3858_ = lean_nat_add(v___x_3831_, v_size_3847_);
if (lean_obj_tag(v_l_3851_) == 0)
{
lean_object* v_size_3859_; 
v_size_3859_ = lean_ctor_get(v_l_3851_, 0);
lean_inc(v_size_3859_);
lean_inc(v_size_3832_);
v___y_3793_ = v___x_3857_;
v___y_3794_ = v_v_3850_;
v___y_3795_ = v_v_3835_;
v___y_3796_ = v___x_3858_;
v___y_3797_ = v_k_3849_;
v___y_3798_ = v_k_3834_;
v___y_3799_ = v_l_3851_;
v___y_3800_ = v_r_3852_;
v___y_3801_ = v_size_3832_;
v___y_3802_ = v___x_3831_;
v___y_3803_ = v_l_3836_;
v___y_3804_ = v_size_3859_;
goto v___jp_3792_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3832_);
v___y_3793_ = v___x_3857_;
v___y_3794_ = v_v_3850_;
v___y_3795_ = v_v_3835_;
v___y_3796_ = v___x_3858_;
v___y_3797_ = v_k_3849_;
v___y_3798_ = v_k_3834_;
v___y_3799_ = v_l_3851_;
v___y_3800_ = v_r_3852_;
v___y_3801_ = v_size_3832_;
v___y_3802_ = v___x_3831_;
v___y_3803_ = v_l_3836_;
v___y_3804_ = v___x_3860_;
goto v___jp_3792_;
}
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_del_object(v___x_3777_);
v___x_3861_ = lean_nat_add(v___x_3831_, v_size_3833_);
lean_dec(v_size_3833_);
v___x_3862_ = lean_nat_add(v___x_3861_, v_size_3832_);
lean_dec(v___x_3861_);
v___x_3863_ = lean_nat_add(v___x_3831_, v_size_3832_);
v___x_3864_ = lean_nat_add(v___x_3863_, v_size_3848_);
lean_dec(v___x_3863_);
lean_inc_ref(v_r_3775_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 4, v_r_3775_);
lean_ctor_set(v___x_3845_, 3, v_r_3837_);
lean_ctor_set(v___x_3845_, 2, v_v_3773_);
lean_ctor_set(v___x_3845_, 1, v_k_3772_);
lean_ctor_set(v___x_3845_, 0, v___x_3864_);
v___x_3866_ = v___x_3845_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_r_3837_);
lean_ctor_set(v_reuseFailAlloc_3879_, 4, v_r_3775_);
v___x_3866_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
v_isSharedCheck_3873_ = !lean_is_exclusive(v_r_3775_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; 
v_unused_3874_ = lean_ctor_get(v_r_3775_, 4);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_r_3775_, 3);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_r_3775_, 2);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_r_3775_, 1);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_r_3775_, 0);
lean_dec(v_unused_3878_);
v___x_3868_ = v_r_3775_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_dec(v_r_3775_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 4, v___x_3866_);
lean_ctor_set(v___x_3868_, 3, v_l_3836_);
lean_ctor_set(v___x_3868_, 2, v_v_3835_);
lean_ctor_set(v___x_3868_, 1, v_k_3834_);
lean_ctor_set(v___x_3868_, 0, v___x_3862_);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3834_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3835_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_l_3836_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v___x_3866_);
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
}
}
}
else
{
lean_object* v_l_3886_; 
lean_del_object(v___x_3777_);
v_l_3886_ = lean_ctor_get(v_impl_3830_, 3);
lean_inc(v_l_3886_);
if (lean_obj_tag(v_l_3886_) == 0)
{
lean_object* v_r_3887_; lean_object* v_k_3888_; lean_object* v_v_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3898_; 
v_r_3887_ = lean_ctor_get(v_impl_3830_, 4);
v_k_3888_ = lean_ctor_get(v_impl_3830_, 1);
v_v_3889_ = lean_ctor_get(v_impl_3830_, 2);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3898_ == 0)
{
lean_object* v_unused_3899_; lean_object* v_unused_3900_; 
v_unused_3899_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3899_);
v_unused_3900_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3900_);
v___x_3891_ = v_impl_3830_;
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_r_3887_);
lean_inc(v_v_3889_);
lean_inc(v_k_3888_);
lean_dec(v_impl_3830_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3898_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3887_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 3, v_r_3887_);
lean_ctor_set(v___x_3891_, 2, v_v_3773_);
lean_ctor_set(v___x_3891_, 1, v_k_3772_);
lean_ctor_set(v___x_3891_, 0, v___x_3831_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3897_, 3, v_r_3887_);
lean_ctor_set(v_reuseFailAlloc_3897_, 4, v_r_3887_);
v___x_3895_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3893_);
lean_ctor_set(v___x_3896_, 1, v_k_3888_);
lean_ctor_set(v___x_3896_, 2, v_v_3889_);
lean_ctor_set(v___x_3896_, 3, v_l_3886_);
lean_ctor_set(v___x_3896_, 4, v___x_3895_);
return v___x_3896_;
}
}
}
else
{
lean_object* v_r_3901_; 
v_r_3901_ = lean_ctor_get(v_impl_3830_, 4);
lean_inc(v_r_3901_);
if (lean_obj_tag(v_r_3901_) == 0)
{
lean_object* v_k_3902_; lean_object* v_v_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3924_; 
v_k_3902_ = lean_ctor_get(v_impl_3830_, 1);
v_v_3903_ = lean_ctor_get(v_impl_3830_, 2);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; 
v_unused_3925_ = lean_ctor_get(v_impl_3830_, 4);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3927_);
v___x_3905_ = v_impl_3830_;
v_isShared_3906_ = v_isSharedCheck_3924_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_v_3903_);
lean_inc(v_k_3902_);
lean_dec(v_impl_3830_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3924_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v_k_3907_; lean_object* v_v_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3920_; 
v_k_3907_ = lean_ctor_get(v_r_3901_, 1);
v_v_3908_ = lean_ctor_get(v_r_3901_, 2);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_r_3901_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3921_ = lean_ctor_get(v_r_3901_, 4);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_r_3901_, 3);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_r_3901_, 0);
lean_dec(v_unused_3923_);
v___x_3910_ = v_r_3901_;
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_v_3908_);
lean_inc(v_k_3907_);
lean_dec(v_r_3901_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3920_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3912_ = lean_unsigned_to_nat(3u);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 4, v_l_3886_);
lean_ctor_set(v___x_3910_, 3, v_l_3886_);
lean_ctor_set(v___x_3910_, 2, v_v_3903_);
lean_ctor_set(v___x_3910_, 1, v_k_3902_);
lean_ctor_set(v___x_3910_, 0, v___x_3831_);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3902_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3903_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v_l_3886_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v_l_3886_);
v___x_3914_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 4, v_l_3886_);
lean_ctor_set(v___x_3905_, 2, v_v_3773_);
lean_ctor_set(v___x_3905_, 1, v_k_3772_);
lean_ctor_set(v___x_3905_, 0, v___x_3831_);
v___x_3916_ = v___x_3905_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v_l_3886_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v_l_3886_);
v___x_3916_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3912_);
lean_ctor_set(v___x_3917_, 1, v_k_3907_);
lean_ctor_set(v___x_3917_, 2, v_v_3908_);
lean_ctor_set(v___x_3917_, 3, v___x_3914_);
lean_ctor_set(v___x_3917_, 4, v___x_3916_);
return v___x_3917_;
}
}
}
}
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_unsigned_to_nat(2u);
v___x_3929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v_k_3772_);
lean_ctor_set(v___x_3929_, 2, v_v_3773_);
lean_ctor_set(v___x_3929_, 3, v_impl_3830_);
lean_ctor_set(v___x_3929_, 4, v_r_3901_);
return v___x_3929_;
}
}
}
}
case 1:
{
lean_object* v___x_3930_; 
lean_del_object(v___x_3777_);
lean_dec(v_v_3773_);
lean_dec(v_k_3772_);
v___x_3930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3930_, 0, v_size_3771_);
lean_ctor_set(v___x_3930_, 1, v_k_3754_);
lean_ctor_set(v___x_3930_, 2, v_v_3755_);
lean_ctor_set(v___x_3930_, 3, v_l_3774_);
lean_ctor_set(v___x_3930_, 4, v_r_3775_);
return v___x_3930_;
}
default: 
{
lean_object* v_impl_3931_; lean_object* v___x_3932_; 
lean_del_object(v___x_3777_);
lean_dec(v_size_3771_);
v_impl_3931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3754_, v_v_3755_, v_r_3775_);
v___x_3932_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3774_) == 0)
{
lean_object* v_size_3933_; lean_object* v_size_3934_; lean_object* v_k_3935_; lean_object* v_v_3936_; lean_object* v_l_3937_; lean_object* v_r_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_size_3933_ = lean_ctor_get(v_l_3774_, 0);
v_size_3934_ = lean_ctor_get(v_impl_3931_, 0);
lean_inc(v_size_3934_);
v_k_3935_ = lean_ctor_get(v_impl_3931_, 1);
lean_inc(v_k_3935_);
v_v_3936_ = lean_ctor_get(v_impl_3931_, 2);
lean_inc(v_v_3936_);
v_l_3937_ = lean_ctor_get(v_impl_3931_, 3);
lean_inc(v_l_3937_);
v_r_3938_ = lean_ctor_get(v_impl_3931_, 4);
lean_inc(v_r_3938_);
v___x_3939_ = lean_unsigned_to_nat(3u);
v___x_3940_ = lean_nat_mul(v___x_3939_, v_size_3933_);
v___x_3941_ = lean_nat_dec_lt(v___x_3940_, v_size_3934_);
lean_dec(v___x_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec(v_r_3938_);
lean_dec(v_l_3937_);
lean_dec(v_v_3936_);
lean_dec(v_k_3935_);
v___x_3942_ = lean_nat_add(v___x_3932_, v_size_3933_);
v___x_3943_ = lean_nat_add(v___x_3942_, v_size_3934_);
lean_dec(v_size_3934_);
lean_dec(v___x_3942_);
v___x_3944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
lean_ctor_set(v___x_3944_, 1, v_k_3772_);
lean_ctor_set(v___x_3944_, 2, v_v_3773_);
lean_ctor_set(v___x_3944_, 3, v_l_3774_);
lean_ctor_set(v___x_3944_, 4, v_impl_3931_);
return v___x_3944_;
}
else
{
lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3979_; 
v_isSharedCheck_3979_ = !lean_is_exclusive(v_impl_3931_);
if (v_isSharedCheck_3979_ == 0)
{
lean_object* v_unused_3980_; lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; 
v_unused_3980_ = lean_ctor_get(v_impl_3931_, 4);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_impl_3931_, 3);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_impl_3931_, 2);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_impl_3931_, 1);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_impl_3931_, 0);
lean_dec(v_unused_3984_);
v___x_3946_ = v_impl_3931_;
v_isShared_3947_ = v_isSharedCheck_3979_;
goto v_resetjp_3945_;
}
else
{
lean_dec(v_impl_3931_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3979_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v_size_3948_; lean_object* v_k_3949_; lean_object* v_v_3950_; lean_object* v_l_3951_; lean_object* v_r_3952_; lean_object* v_size_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v_size_3948_ = lean_ctor_get(v_l_3937_, 0);
v_k_3949_ = lean_ctor_get(v_l_3937_, 1);
v_v_3950_ = lean_ctor_get(v_l_3937_, 2);
v_l_3951_ = lean_ctor_get(v_l_3937_, 3);
v_r_3952_ = lean_ctor_get(v_l_3937_, 4);
v_size_3953_ = lean_ctor_get(v_r_3938_, 0);
v___x_3954_ = lean_unsigned_to_nat(2u);
v___x_3955_ = lean_nat_mul(v___x_3954_, v_size_3953_);
v___x_3956_ = lean_nat_dec_lt(v_size_3948_, v___x_3955_);
lean_dec(v___x_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_inc(v_size_3953_);
lean_inc(v_r_3952_);
lean_inc(v_l_3951_);
lean_inc(v_v_3950_);
lean_inc(v_k_3949_);
lean_del_object(v___x_3946_);
lean_dec(v_l_3937_);
v___x_3957_ = lean_nat_add(v___x_3932_, v_size_3933_);
v___x_3958_ = lean_nat_add(v___x_3957_, v_size_3934_);
lean_dec(v_size_3934_);
if (lean_obj_tag(v_l_3951_) == 0)
{
lean_object* v_size_3959_; 
v_size_3959_ = lean_ctor_get(v_l_3951_, 0);
lean_inc(v_size_3959_);
v___y_3811_ = v_r_3938_;
v___y_3812_ = v_v_3936_;
v___y_3813_ = v___x_3957_;
v___y_3814_ = v_v_3950_;
v___y_3815_ = v_l_3951_;
v___y_3816_ = v_size_3953_;
v___y_3817_ = v_k_3949_;
v___y_3818_ = v_k_3935_;
v___y_3819_ = v___x_3958_;
v___y_3820_ = v___x_3932_;
v___y_3821_ = v_r_3952_;
v___y_3822_ = v_size_3959_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_unsigned_to_nat(0u);
v___y_3811_ = v_r_3938_;
v___y_3812_ = v_v_3936_;
v___y_3813_ = v___x_3957_;
v___y_3814_ = v_v_3950_;
v___y_3815_ = v_l_3951_;
v___y_3816_ = v_size_3953_;
v___y_3817_ = v_k_3949_;
v___y_3818_ = v_k_3935_;
v___y_3819_ = v___x_3958_;
v___y_3820_ = v___x_3932_;
v___y_3821_ = v_r_3952_;
v___y_3822_ = v___x_3960_;
goto v___jp_3810_;
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3961_ = lean_nat_add(v___x_3932_, v_size_3933_);
v___x_3962_ = lean_nat_add(v___x_3961_, v_size_3934_);
lean_dec(v_size_3934_);
v___x_3963_ = lean_nat_add(v___x_3961_, v_size_3948_);
lean_dec(v___x_3961_);
lean_inc_ref(v_l_3774_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 4, v_l_3937_);
lean_ctor_set(v___x_3946_, 3, v_l_3774_);
lean_ctor_set(v___x_3946_, 2, v_v_3773_);
lean_ctor_set(v___x_3946_, 1, v_k_3772_);
lean_ctor_set(v___x_3946_, 0, v___x_3963_);
v___x_3965_ = v___x_3946_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3963_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_l_3774_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v_l_3937_);
v___x_3965_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_isSharedCheck_3972_ = !lean_is_exclusive(v_l_3774_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; lean_object* v_unused_3974_; lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; 
v_unused_3973_ = lean_ctor_get(v_l_3774_, 4);
lean_dec(v_unused_3973_);
v_unused_3974_ = lean_ctor_get(v_l_3774_, 3);
lean_dec(v_unused_3974_);
v_unused_3975_ = lean_ctor_get(v_l_3774_, 2);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_l_3774_, 1);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_l_3774_, 0);
lean_dec(v_unused_3977_);
v___x_3967_ = v_l_3774_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_dec(v_l_3774_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 4, v_r_3938_);
lean_ctor_set(v___x_3967_, 3, v___x_3965_);
lean_ctor_set(v___x_3967_, 2, v_v_3936_);
lean_ctor_set(v___x_3967_, 1, v_k_3935_);
lean_ctor_set(v___x_3967_, 0, v___x_3962_);
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_k_3935_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_v_3936_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_r_3938_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3985_; 
v_l_3985_ = lean_ctor_get(v_impl_3931_, 3);
lean_inc(v_l_3985_);
if (lean_obj_tag(v_l_3985_) == 0)
{
lean_object* v_r_3986_; lean_object* v_k_3987_; lean_object* v_v_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4009_; 
v_r_3986_ = lean_ctor_get(v_impl_3931_, 4);
v_k_3987_ = lean_ctor_get(v_impl_3931_, 1);
v_v_3988_ = lean_ctor_get(v_impl_3931_, 2);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_impl_3931_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; lean_object* v_unused_4011_; 
v_unused_4010_ = lean_ctor_get(v_impl_3931_, 3);
lean_dec(v_unused_4010_);
v_unused_4011_ = lean_ctor_get(v_impl_3931_, 0);
lean_dec(v_unused_4011_);
v___x_3990_ = v_impl_3931_;
v_isShared_3991_ = v_isSharedCheck_4009_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_r_3986_);
lean_inc(v_v_3988_);
lean_inc(v_k_3987_);
lean_dec(v_impl_3931_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4009_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v_k_3992_; lean_object* v_v_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4005_; 
v_k_3992_ = lean_ctor_get(v_l_3985_, 1);
v_v_3993_ = lean_ctor_get(v_l_3985_, 2);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_l_3985_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; lean_object* v_unused_4007_; lean_object* v_unused_4008_; 
v_unused_4006_ = lean_ctor_get(v_l_3985_, 4);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_l_3985_, 3);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v_l_3985_, 0);
lean_dec(v_unused_4008_);
v___x_3995_ = v_l_3985_;
v_isShared_3996_ = v_isSharedCheck_4005_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_v_3993_);
lean_inc(v_k_3992_);
lean_dec(v_l_3985_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4005_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3986_, 2);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 4, v_r_3986_);
lean_ctor_set(v___x_3995_, 3, v_r_3986_);
lean_ctor_set(v___x_3995_, 2, v_v_3773_);
lean_ctor_set(v___x_3995_, 1, v_k_3772_);
lean_ctor_set(v___x_3995_, 0, v___x_3932_);
v___x_3999_ = v___x_3995_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_r_3986_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_r_3986_);
v___x_3999_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4001_; 
lean_inc(v_r_3986_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 3, v_r_3986_);
lean_ctor_set(v___x_3990_, 0, v___x_3932_);
v___x_4001_ = v___x_3990_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_k_3987_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_v_3988_);
lean_ctor_set(v_reuseFailAlloc_4003_, 3, v_r_3986_);
lean_ctor_set(v_reuseFailAlloc_4003_, 4, v_r_3986_);
v___x_4001_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4002_, 0, v___x_3997_);
lean_ctor_set(v___x_4002_, 1, v_k_3992_);
lean_ctor_set(v___x_4002_, 2, v_v_3993_);
lean_ctor_set(v___x_4002_, 3, v___x_3999_);
lean_ctor_set(v___x_4002_, 4, v___x_4001_);
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v_r_4012_; 
v_r_4012_ = lean_ctor_get(v_impl_3931_, 4);
lean_inc(v_r_4012_);
if (lean_obj_tag(v_r_4012_) == 0)
{
lean_object* v_k_4013_; lean_object* v_v_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4023_; 
v_k_4013_ = lean_ctor_get(v_impl_3931_, 1);
v_v_4014_ = lean_ctor_get(v_impl_3931_, 2);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_impl_3931_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; lean_object* v_unused_4025_; lean_object* v_unused_4026_; 
v_unused_4024_ = lean_ctor_get(v_impl_3931_, 4);
lean_dec(v_unused_4024_);
v_unused_4025_ = lean_ctor_get(v_impl_3931_, 3);
lean_dec(v_unused_4025_);
v_unused_4026_ = lean_ctor_get(v_impl_3931_, 0);
lean_dec(v_unused_4026_);
v___x_4016_ = v_impl_3931_;
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_v_4014_);
lean_inc(v_k_4013_);
lean_dec(v_impl_3931_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4018_ = lean_unsigned_to_nat(3u);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 4, v_l_3985_);
lean_ctor_set(v___x_4016_, 2, v_v_3773_);
lean_ctor_set(v___x_4016_, 1, v_k_3772_);
lean_ctor_set(v___x_4016_, 0, v___x_3932_);
v___x_4020_ = v___x_4016_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_4022_, 3, v_l_3985_);
lean_ctor_set(v_reuseFailAlloc_4022_, 4, v_l_3985_);
v___x_4020_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4018_);
lean_ctor_set(v___x_4021_, 1, v_k_4013_);
lean_ctor_set(v___x_4021_, 2, v_v_4014_);
lean_ctor_set(v___x_4021_, 3, v___x_4020_);
lean_ctor_set(v___x_4021_, 4, v_r_4012_);
return v___x_4021_;
}
}
}
else
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = lean_unsigned_to_nat(2u);
v___x_4028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v_k_3772_);
lean_ctor_set(v___x_4028_, 2, v_v_3773_);
lean_ctor_set(v___x_4028_, 3, v_r_4012_);
lean_ctor_set(v___x_4028_, 4, v_impl_3931_);
return v___x_4028_;
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
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_unsigned_to_nat(1u);
v___x_4037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
lean_ctor_set(v___x_4037_, 1, v_k_3754_);
lean_ctor_set(v___x_4037_, 2, v_v_3755_);
lean_ctor_set(v___x_4037_, 3, v_t_3756_);
lean_ctor_set(v___x_4037_, 4, v_t_3756_);
return v___x_4037_;
}
v___jp_3757_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_nat_add(v___y_3764_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec(v___y_3764_);
v___x_3769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___y_3763_);
lean_ctor_set(v___x_3769_, 2, v___y_3759_);
lean_ctor_set(v___x_3769_, 3, v___y_3765_);
lean_ctor_set(v___x_3769_, 4, v___y_3758_);
v___x_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3770_, 0, v___y_3762_);
lean_ctor_set(v___x_3770_, 1, v___y_3761_);
lean_ctor_set(v___x_3770_, 2, v___y_3760_);
lean_ctor_set(v___x_3770_, 3, v___y_3766_);
lean_ctor_set(v___x_3770_, 4, v___x_3769_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4038_, lean_object* v_k_4039_, lean_object* v_fallback_4040_){
_start:
{
if (lean_obj_tag(v_t_4038_) == 0)
{
lean_object* v_k_4041_; lean_object* v_v_4042_; lean_object* v_l_4043_; lean_object* v_r_4044_; uint8_t v___y_4046_; lean_object* v_fst_4049_; lean_object* v_snd_4050_; lean_object* v_fst_4051_; lean_object* v_snd_4052_; uint8_t v___x_4053_; 
v_k_4041_ = lean_ctor_get(v_t_4038_, 1);
v_v_4042_ = lean_ctor_get(v_t_4038_, 2);
v_l_4043_ = lean_ctor_get(v_t_4038_, 3);
v_r_4044_ = lean_ctor_get(v_t_4038_, 4);
v_fst_4049_ = lean_ctor_get(v_k_4039_, 0);
v_snd_4050_ = lean_ctor_get(v_k_4039_, 1);
v_fst_4051_ = lean_ctor_get(v_k_4041_, 0);
v_snd_4052_ = lean_ctor_get(v_k_4041_, 1);
v___x_4053_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4049_, v_fst_4051_);
if (v___x_4053_ == 1)
{
uint8_t v___x_4054_; 
v___x_4054_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4050_, v_snd_4052_);
v___y_4046_ = v___x_4054_;
goto v___jp_4045_;
}
else
{
v___y_4046_ = v___x_4053_;
goto v___jp_4045_;
}
v___jp_4045_:
{
switch(v___y_4046_)
{
case 0:
{
v_t_4038_ = v_l_4043_;
goto _start;
}
case 1:
{
lean_inc(v_v_4042_);
return v_v_4042_;
}
default: 
{
v_t_4038_ = v_r_4044_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4040_);
return v_fallback_4040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4055_, lean_object* v_k_4056_, lean_object* v_fallback_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4055_, v_k_4056_, v_fallback_4057_);
lean_dec(v_fallback_4057_);
lean_dec_ref(v_k_4056_);
lean_dec(v_t_4055_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4059_, lean_object* v_as_4060_, size_t v_sz_4061_, size_t v_i_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
uint8_t v___x_4067_; 
v___x_4067_ = lean_usize_dec_lt(v_i_4062_, v_sz_4061_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
lean_dec(v___x_4059_);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_b_4063_);
return v___x_4068_;
}
else
{
lean_object* v_a_4069_; lean_object* v_fst_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4098_; 
v_a_4069_ = lean_array_uget(v_as_4060_, v_i_4062_);
v_fst_4070_ = lean_ctor_get(v_a_4069_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_a_4069_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; 
v_unused_4099_ = lean_ctor_get(v_a_4069_, 1);
lean_dec(v_unused_4099_);
v___x_4072_ = v_a_4069_;
v_isShared_4073_ = v_isSharedCheck_4098_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_fst_4070_);
lean_dec(v_a_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4098_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; 
lean_inc(v_fst_4070_);
v___x_4074_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4070_, v___y_4064_, v___y_4065_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; lean_object* v___y_4078_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4076_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_4075_) == 0)
{
lean_inc(v___x_4059_);
v___y_4078_ = v___x_4059_;
goto v___jp_4077_;
}
else
{
lean_object* v_val_4089_; 
v_val_4089_ = lean_ctor_get(v_a_4075_, 0);
lean_inc(v_val_4089_);
lean_dec_ref_known(v_a_4075_, 1);
v___y_4078_ = v_val_4089_;
goto v___jp_4077_;
}
v___jp_4077_:
{
lean_object* v___x_4080_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v_fst_4070_);
lean_ctor_set(v___x_4072_, 0, v___y_4078_);
v___x_4080_ = v___x_4072_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___y_4078_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_fst_4070_);
v___x_4080_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; size_t v___x_4085_; size_t v___x_4086_; 
v___x_4081_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4063_, v___x_4080_, v___x_4076_);
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_nat_add(v___x_4081_, v___x_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4080_, v___x_4083_, v_b_4063_);
v___x_4085_ = ((size_t)1ULL);
v___x_4086_ = lean_usize_add(v_i_4062_, v___x_4085_);
v_i_4062_ = v___x_4086_;
v_b_4063_ = v___x_4084_;
goto _start;
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_del_object(v___x_4072_);
lean_dec(v_fst_4070_);
lean_dec(v_b_4063_);
lean_dec(v___x_4059_);
v_a_4090_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4074_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4074_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4100_, lean_object* v_as_4101_, lean_object* v_sz_4102_, lean_object* v_i_4103_, lean_object* v_b_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
size_t v_sz_boxed_4108_; size_t v_i_boxed_4109_; lean_object* v_res_4110_; 
v_sz_boxed_4108_ = lean_unbox_usize(v_sz_4102_);
lean_dec(v_sz_4102_);
v_i_boxed_4109_ = lean_unbox_usize(v_i_4103_);
lean_dec(v_i_4103_);
v_res_4110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4100_, v_as_4101_, v_sz_boxed_4108_, v_i_boxed_4109_, v_b_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec_ref(v_as_4101_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4111_, lean_object* v_init_4112_, lean_object* v_x_4113_){
_start:
{
if (lean_obj_tag(v_x_4113_) == 0)
{
lean_object* v_k_4115_; lean_object* v_v_4116_; lean_object* v_l_4117_; lean_object* v_r_4118_; lean_object* v___x_4119_; lean_object* v_a_4120_; lean_object* v_a_4121_; lean_object* v_fst_4122_; lean_object* v_snd_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4138_; 
v_k_4115_ = lean_ctor_get(v_x_4113_, 1);
lean_inc(v_k_4115_);
v_v_4116_ = lean_ctor_get(v_x_4113_, 2);
lean_inc(v_v_4116_);
v_l_4117_ = lean_ctor_get(v_x_4113_, 3);
lean_inc(v_l_4117_);
v_r_4118_ = lean_ctor_get(v_x_4113_, 4);
lean_inc(v_r_4118_);
lean_dec_ref_known(v_x_4113_, 5);
lean_inc_ref(v_fst_4111_);
v___x_4119_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4111_, v_init_4112_, v_l_4117_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
v_a_4121_ = lean_ctor_get(v_a_4120_, 0);
lean_inc(v_a_4121_);
lean_dec(v_a_4120_);
v_fst_4122_ = lean_ctor_get(v_k_4115_, 0);
v_snd_4123_ = lean_ctor_get(v_k_4115_, 1);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_k_4115_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4125_ = v_k_4115_;
v_isShared_4126_ = v_isSharedCheck_4138_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_snd_4123_);
lean_inc(v_fst_4122_);
lean_dec(v_k_4115_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4138_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v_optName_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v_optName_4127_ = lean_ctor_get(v_fst_4111_, 1);
v___x_4128_ = 1;
lean_inc(v_optName_4127_);
v___x_4129_ = l_Lean_Name_toString(v_optName_4127_, v___x_4128_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set_tag(v___x_4125_, 1);
v___x_4131_ = v___x_4125_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_fst_4122_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_snd_4123_);
v___x_4131_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
double v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4132_ = lean_float_of_nat(v_v_4116_);
v___x_4133_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4133_, 0, v___x_4132_);
v___x_4134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4129_);
lean_ctor_set(v___x_4134_, 1, v___x_4131_);
lean_ctor_set(v___x_4134_, 2, v___x_4133_);
v___x_4135_ = lean_array_push(v_a_4121_, v___x_4134_);
v_init_4112_ = v___x_4135_;
v_x_4113_ = v_r_4118_;
goto _start;
}
}
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_dec_ref(v_fst_4111_);
v___x_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4139_, 0, v_init_4112_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4141_, lean_object* v_init_4142_, lean_object* v_x_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4141_, v_init_4142_, v_x_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4146_, lean_object* v_as_4147_, size_t v_sz_4148_, size_t v_i_4149_, lean_object* v_b_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_a_4155_; uint8_t v___x_4159_; 
v___x_4159_ = lean_usize_dec_lt(v_i_4149_, v_sz_4148_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; 
lean_dec(v___x_4146_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_b_4150_);
return v___x_4160_;
}
else
{
lean_object* v_a_4161_; lean_object* v_snd_4162_; lean_object* v_fst_4163_; lean_object* v_size_4164_; lean_object* v_buckets_4165_; lean_object* v___x_4166_; lean_object* v___y_4168_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v_a_4161_ = lean_array_uget_borrowed(v_as_4147_, v_i_4149_);
v_snd_4162_ = lean_ctor_get(v_a_4161_, 1);
v_fst_4163_ = lean_ctor_get(v_a_4161_, 0);
v_size_4164_ = lean_ctor_get(v_snd_4162_, 0);
v_buckets_4165_ = lean_ctor_get(v_snd_4162_, 1);
v___x_4166_ = lean_box(1);
v___x_4202_ = lean_mk_empty_array_with_capacity(v_size_4164_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_array_get_size(v_buckets_4165_);
v___x_4205_ = lean_nat_dec_lt(v___x_4203_, v___x_4204_);
if (v___x_4205_ == 0)
{
v___y_4168_ = v___x_4202_;
goto v___jp_4167_;
}
else
{
size_t v___x_4206_; size_t v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = ((size_t)0ULL);
v___x_4207_ = lean_usize_of_nat(v___x_4204_);
v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4165_, v___x_4206_, v___x_4207_, v___x_4202_);
v___y_4168_ = v___x_4208_;
goto v___jp_4167_;
}
v___jp_4167_:
{
size_t v_sz_4169_; size_t v___x_4170_; lean_object* v___x_4171_; 
v_sz_4169_ = lean_array_size(v___y_4168_);
v___x_4170_ = ((size_t)0ULL);
lean_inc(v___x_4146_);
v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4146_, v___y_4168_, v_sz_4169_, v___x_4170_, v___x_4166_, v___y_4151_, v___y_4152_);
lean_dec_ref(v___y_4168_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4173_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
lean_inc(v_fst_4163_);
v___x_4173_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4163_, v_b_4150_, v_a_4172_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v_a_4175_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v_a_4175_ = lean_ctor_get(v_a_4174_, 0);
lean_inc(v_a_4175_);
lean_dec(v_a_4174_);
v_a_4155_ = v_a_4175_;
goto v___jp_4154_;
}
else
{
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4185_; 
v_a_4176_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4178_ = v___x_4173_;
v_isShared_4179_ = v_isSharedCheck_4185_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4173_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4185_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
if (lean_obj_tag(v_a_4176_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; 
lean_dec(v___x_4146_);
v_a_4180_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v_a_4176_, 1);
if (v_isShared_4179_ == 0)
{
lean_ctor_set_tag(v___x_4178_, 0);
lean_ctor_set(v___x_4178_, 0, v_a_4180_);
v___x_4182_ = v___x_4178_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
else
{
lean_object* v_a_4184_; 
lean_del_object(v___x_4178_);
v_a_4184_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v_a_4176_, 1);
v_a_4155_ = v_a_4184_;
goto v___jp_4154_;
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v___x_4146_);
v_a_4186_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4173_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4173_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v_b_4150_);
lean_dec(v___x_4146_);
v_a_4194_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4171_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4171_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
v___jp_4154_:
{
size_t v___x_4156_; size_t v___x_4157_; 
v___x_4156_ = ((size_t)1ULL);
v___x_4157_ = lean_usize_add(v_i_4149_, v___x_4156_);
v_i_4149_ = v___x_4157_;
v_b_4150_ = v_a_4155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4209_, lean_object* v_as_4210_, lean_object* v_sz_4211_, lean_object* v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4211_);
lean_dec(v_sz_4211_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4209_, v_as_4210_, v_sz_boxed_4217_, v_i_boxed_4218_, v_b_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_as_4210_);
return v_res_4219_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = l_Lean_maxRecDepth;
v___x_4227_ = l_Lean_Options_empty;
v___x_4228_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4227_, v___x_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4229_, lean_object* v_linterOpts_4230_, lean_object* v_sp_4231_, lean_object* v_env_4232_, lean_object* v_mod_4233_){
_start:
{
lean_object* v_msg_4236_; lean_object* v_a_4241_; lean_object* v_a_4245_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v_a_4276_; lean_object* v___y_4280_; lean_object* v___y_4283_; uint8_t v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; uint8_t v___y_4289_; uint8_t v___y_4290_; uint8_t v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; uint8_t v___y_4365_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_env_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; uint8_t v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; lean_object* v_fileName_4418_; lean_object* v_fileMap_4419_; lean_object* v_currRecDepth_4420_; lean_object* v_ref_4421_; lean_object* v_currNamespace_4422_; lean_object* v_openDecls_4423_; lean_object* v_initHeartbeats_4424_; lean_object* v_maxHeartbeats_4425_; lean_object* v_quotContext_4426_; lean_object* v_currMacroScope_4427_; lean_object* v_cancelTk_x3f_4428_; uint8_t v_suppressElabErrors_4429_; lean_object* v_inheritedTraceOptions_4430_; lean_object* v___y_4431_; uint8_t v___y_4447_; uint8_t v___x_4467_; 
v___x_4259_ = lean_unsigned_to_nat(0u);
v___x_4260_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4261_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4262_ = lean_io_get_num_heartbeats();
v___x_4263_ = l_Lean_firstFrontendMacroScope;
v___x_4264_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4265_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4266_ = lean_box(0);
v___x_4267_ = lean_box(0);
v___x_4268_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4269_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4270_ = 1;
v___x_4271_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4272_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4273_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4273_, 0, v_env_4232_);
lean_ctor_set(v___x_4273_, 1, v___x_4264_);
lean_ctor_set(v___x_4273_, 2, v___x_4265_);
lean_ctor_set(v___x_4273_, 3, v___x_4268_);
lean_ctor_set(v___x_4273_, 4, v___x_4269_);
lean_ctor_set(v___x_4273_, 5, v___x_4260_);
lean_ctor_set(v___x_4273_, 6, v___x_4261_);
lean_ctor_set(v___x_4273_, 7, v___x_4271_);
lean_ctor_set(v___x_4273_, 8, v___x_4272_);
v___x_4274_ = lean_st_mk_ref(v___x_4273_);
v___x_4374_ = l_Lean_inheritedTraceOptions;
v___x_4375_ = lean_st_ref_get(v___x_4374_);
v___x_4376_ = lean_st_ref_get(v___x_4274_);
v_env_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc_ref(v_env_4377_);
lean_dec(v___x_4376_);
v___x_4378_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4379_ = l_Lean_instInhabitedFileMap_default;
v___x_4380_ = l_Lean_Options_empty;
v___x_4381_ = lean_box(0);
v___x_4382_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4383_ = 0;
v___x_4414_ = lean_box(0);
v___x_4415_ = l_Lean_Name_getRoot(v_mod_4233_);
v___x_4416_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4467_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4377_);
lean_dec_ref(v_env_4377_);
if (v___x_4416_ == 0)
{
if (v___x_4467_ == 0)
{
lean_inc(v___x_4274_);
v_fileName_4418_ = v___x_4378_;
v_fileMap_4419_ = v___x_4379_;
v_currRecDepth_4420_ = v___x_4259_;
v_ref_4421_ = v___x_4381_;
v_currNamespace_4422_ = v___x_4266_;
v_openDecls_4423_ = v___x_4267_;
v_initHeartbeats_4424_ = v___x_4262_;
v_maxHeartbeats_4425_ = v___x_4382_;
v_quotContext_4426_ = v___x_4266_;
v_currMacroScope_4427_ = v___x_4263_;
v_cancelTk_x3f_4428_ = v___x_4414_;
v_suppressElabErrors_4429_ = v___x_4383_;
v_inheritedTraceOptions_4430_ = v___x_4375_;
v___y_4431_ = v___x_4274_;
goto v___jp_4417_;
}
else
{
v___y_4447_ = v___x_4416_;
goto v___jp_4446_;
}
}
else
{
v___y_4447_ = v___x_4467_;
goto v___jp_4446_;
}
v___jp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4237_ = l_Lean_MessageData_toString(v_msg_4236_);
v___x_4238_ = lean_mk_io_user_error(v___x_4237_);
v___x_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
return v___x_4239_;
}
v___jp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_mk_io_user_error(v_a_4241_);
v___x_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
return v___x_4243_;
}
v___jp_4244_:
{
if (lean_obj_tag(v_a_4245_) == 0)
{
lean_object* v_msg_4246_; 
v_msg_4246_ = lean_ctor_get(v_a_4245_, 1);
lean_inc_ref(v_msg_4246_);
lean_dec_ref_known(v_a_4245_, 2);
v_msg_4236_ = v_msg_4246_;
goto v___jp_4235_;
}
else
{
lean_object* v_id_4247_; lean_object* v___x_4248_; 
v_id_4247_ = lean_ctor_get(v_a_4245_, 0);
lean_inc(v_id_4247_);
lean_dec_ref_known(v_a_4245_, 2);
v___x_4248_ = l_Lean_InternalExceptionId_getName(v_id_4247_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec(v_id_4247_);
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
v___x_4250_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4251_ = 1;
v___x_4252_ = l_Lean_Name_toString(v_a_4249_, v___x_4251_);
v___x_4253_ = lean_string_append(v___x_4250_, v___x_4252_);
lean_dec_ref(v___x_4252_);
v_a_4241_ = v___x_4253_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec_ref_known(v___x_4248_, 1);
v___x_4254_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4255_ = l_Nat_reprFast(v_id_4247_);
v___x_4256_ = lean_string_append(v___x_4254_, v___x_4255_);
lean_dec_ref(v___x_4255_);
v___x_4257_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4258_ = lean_string_append(v___x_4256_, v___x_4257_);
v_a_4241_ = v___x_4258_;
goto v___jp_4240_;
}
}
}
v___jp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = lean_st_ref_get(v___x_4274_);
lean_dec(v___x_4274_);
lean_dec(v___x_4277_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v_a_4276_);
return v___x_4278_;
}
v___jp_4279_:
{
lean_object* v_a_4281_; 
v_a_4281_ = lean_ctor_get(v___y_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___y_4280_);
v_a_4276_ = v_a_4281_;
goto v___jp_4275_;
}
v___jp_4282_:
{
switch(v___y_4284_)
{
case 0:
{
lean_dec(v_sp_4231_);
if (v___y_4290_ == 0)
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec_ref(v___y_4283_);
v___x_4291_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4233_, v___x_4270_);
v___x_4293_ = lean_string_append(v___x_4291_, v___x_4292_);
lean_dec_ref(v___x_4292_);
v___x_4294_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4295_ = lean_string_append(v___x_4293_, v___x_4294_);
v___x_4296_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4295_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v___x_4298_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4290_, v_a_4297_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
v___y_4280_ = v___x_4298_;
goto v___jp_4279_;
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___x_4274_);
v_a_4299_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4301_ = v___x_4296_;
v_isShared_4302_ = v_isSharedCheck_4308_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4296_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4308_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4303_ = lean_io_error_to_string(v_a_4299_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set_tag(v___x_4301_, 3);
lean_ctor_set(v___x_4301_, 0, v___x_4303_);
v___x_4305_ = v___x_4301_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_MessageData_ofFormat(v___x_4305_);
v_msg_4236_ = v___x_4306_;
goto v___jp_4235_;
}
}
}
}
else
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4309_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4233_, v___y_4290_);
v___x_4311_ = lean_string_append(v___x_4309_, v___x_4310_);
lean_dec_ref(v___x_4310_);
v___x_4312_ = lean_array_get_size(v___y_4283_);
lean_dec_ref(v___y_4283_);
v___x_4313_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4285_, v___y_4286_, v___x_4270_, v___x_4311_, v___x_4312_, v___x_4270_, v___y_4287_, v___y_4288_);
lean_dec_ref(v___y_4286_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = l_Lean_MessageData_toString(v_a_4314_);
v___x_4316_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4315_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4290_, v_a_4317_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
v___y_4280_ = v___x_4318_;
goto v___jp_4279_;
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___x_4274_);
v_a_4319_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4321_ = v___x_4316_;
v_isShared_4322_ = v_isSharedCheck_4328_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4316_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4328_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___x_4325_; 
v___x_4323_ = lean_io_error_to_string(v_a_4319_);
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 3);
lean_ctor_set(v___x_4321_, 0, v___x_4323_);
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4323_);
v___x_4325_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_MessageData_ofFormat(v___x_4325_);
v_msg_4236_ = v___x_4326_;
goto v___jp_4235_;
}
}
}
}
else
{
lean_object* v_a_4329_; 
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___x_4274_);
v_a_4329_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4313_, 1);
v_a_4245_ = v_a_4329_;
goto v___jp_4244_;
}
}
}
case 1:
{
lean_object* v___x_4330_; lean_object* v_env_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; size_t v_sz_4335_; size_t v___x_4336_; lean_object* v___x_4337_; 
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4283_);
lean_dec(v_mod_4233_);
v___x_4330_ = lean_st_ref_get(v___y_4288_);
v_env_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc_ref(v_env_4331_);
lean_dec(v___x_4330_);
v___x_4332_ = l_Lean_Environment_mainModule(v_env_4331_);
lean_dec_ref(v_env_4331_);
v___x_4333_ = lean_box(v___y_4289_);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4272_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v_sz_4335_ = lean_array_size(v___y_4285_);
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4231_, v___x_4332_, v___y_4285_, v_sz_4335_, v___x_4336_, v___x_4334_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4285_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v_fst_4339_; lean_object* v_snd_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4337_, 1);
v_fst_4339_ = lean_ctor_get(v_a_4338_, 0);
lean_inc(v_fst_4339_);
v_snd_4340_ = lean_ctor_get(v_a_4338_, 1);
lean_inc(v_snd_4340_);
lean_dec(v_a_4338_);
v___x_4341_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4341_, 0, v_fst_4339_);
v___x_4342_ = lean_unbox(v_snd_4340_);
lean_dec(v_snd_4340_);
lean_ctor_set_uint8(v___x_4341_, sizeof(void*)*1, v___x_4342_);
v_a_4276_ = v___x_4341_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4343_; 
lean_dec(v___x_4274_);
v_a_4343_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4337_, 1);
v_a_4245_ = v_a_4343_;
goto v___jp_4244_;
}
}
default: 
{
lean_object* v___x_4344_; lean_object* v_env_4345_; lean_object* v___x_4346_; size_t v_sz_4347_; size_t v___x_4348_; lean_object* v___x_4349_; 
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4283_);
lean_dec(v_mod_4233_);
lean_dec(v_sp_4231_);
v___x_4344_ = lean_st_ref_get(v___y_4288_);
v_env_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_ref(v_env_4345_);
lean_dec(v___x_4344_);
v___x_4346_ = l_Lean_Environment_mainModule(v_env_4345_);
lean_dec_ref(v_env_4345_);
v_sz_4347_ = lean_array_size(v___y_4285_);
v___x_4348_ = ((size_t)0ULL);
v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4346_, v___y_4285_, v_sz_4347_, v___x_4348_, v___x_4272_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4285_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
lean_ctor_set_tag(v___x_4352_, 2);
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
v_a_4276_ = v___x_4355_;
goto v___jp_4275_;
}
}
}
else
{
lean_object* v_a_4358_; 
lean_dec(v___x_4274_);
v_a_4358_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4349_, 1);
v_a_4245_ = v_a_4358_;
goto v___jp_4244_;
}
}
}
}
v___jp_4359_:
{
lean_object* v___x_4366_; 
lean_inc_ref(v___y_4361_);
v___x_4366_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4362_, v___y_4361_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4367_);
lean_dec_ref_known(v___x_4366_, 1);
v___x_4368_ = lean_array_get_size(v_a_4367_);
v___x_4369_ = lean_nat_dec_lt(v___x_4259_, v___x_4368_);
if (v___x_4369_ == 0)
{
v___y_4283_ = v___y_4361_;
v___y_4284_ = v___y_4360_;
v___y_4285_ = v_a_4367_;
v___y_4286_ = v___y_4362_;
v___y_4287_ = v___y_4363_;
v___y_4288_ = v___y_4364_;
v___y_4289_ = v___y_4365_;
v___y_4290_ = v___x_4369_;
goto v___jp_4282_;
}
else
{
if (v___x_4369_ == 0)
{
v___y_4283_ = v___y_4361_;
v___y_4284_ = v___y_4360_;
v___y_4285_ = v_a_4367_;
v___y_4286_ = v___y_4362_;
v___y_4287_ = v___y_4363_;
v___y_4288_ = v___y_4364_;
v___y_4289_ = v___y_4365_;
v___y_4290_ = v___x_4369_;
goto v___jp_4282_;
}
else
{
size_t v___x_4370_; size_t v___x_4371_; uint8_t v___x_4372_; 
v___x_4370_ = ((size_t)0ULL);
v___x_4371_ = lean_usize_of_nat(v___x_4368_);
v___x_4372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4365_, v_a_4367_, v___x_4370_, v___x_4371_);
v___y_4283_ = v___y_4361_;
v___y_4284_ = v___y_4360_;
v___y_4285_ = v_a_4367_;
v___y_4286_ = v___y_4362_;
v___y_4287_ = v___y_4363_;
v___y_4288_ = v___y_4364_;
v___y_4289_ = v___y_4365_;
v___y_4290_ = v___x_4372_;
goto v___jp_4282_;
}
}
}
else
{
lean_object* v_a_4373_; 
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___x_4274_);
lean_dec(v_mod_4233_);
lean_dec(v_sp_4231_);
v_a_4373_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4366_, 1);
v_a_4245_ = v_a_4373_;
goto v___jp_4244_;
}
}
v___jp_4384_:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4389_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4389_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
v___x_4392_ = lean_array_get_size(v_a_4391_);
v___x_4393_ = lean_nat_dec_eq(v___x_4392_, v___x_4259_);
if (v___x_4393_ == 0)
{
v___y_4360_ = v___y_4385_;
v___y_4361_ = v_a_4391_;
v___y_4362_ = v___y_4386_;
v___y_4363_ = v___y_4387_;
v___y_4364_ = v___y_4388_;
v___y_4365_ = v___x_4393_;
goto v___jp_4359_;
}
else
{
uint8_t v___x_4394_; uint8_t v___x_4395_; 
v___x_4394_ = 0;
v___x_4395_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4385_, v___x_4394_);
if (v___x_4395_ == 0)
{
v___y_4360_ = v___y_4385_;
v___y_4361_ = v_a_4391_;
v___y_4362_ = v___y_4386_;
v___y_4363_ = v___y_4387_;
v___y_4364_ = v___y_4388_;
v___y_4365_ = v___x_4395_;
goto v___jp_4359_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_dec(v_a_4391_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v_sp_4231_);
v___x_4396_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4233_, v___x_4395_);
v___x_4398_ = lean_string_append(v___x_4396_, v___x_4397_);
lean_dec_ref(v___x_4397_);
v___x_4399_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4400_ = lean_string_append(v___x_4398_, v___x_4399_);
v___x_4401_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4400_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4402_; 
lean_dec_ref_known(v___x_4401_, 1);
v___x_4402_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4276_ = v___x_4402_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4412_; 
lean_dec(v___x_4274_);
v_a_4403_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4405_ = v___x_4401_;
v_isShared_4406_ = v_isSharedCheck_4412_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4401_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4412_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4407_ = lean_io_error_to_string(v_a_4403_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set_tag(v___x_4405_, 3);
lean_ctor_set(v___x_4405_, 0, v___x_4407_);
v___x_4409_ = v___x_4405_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_MessageData_ofFormat(v___x_4409_);
v_msg_4236_ = v___x_4410_;
goto v___jp_4235_;
}
}
}
}
}
}
else
{
lean_object* v_a_4413_; 
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___x_4274_);
lean_dec(v_mod_4233_);
lean_dec(v_sp_4231_);
v_a_4413_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4390_, 1);
v_a_4245_ = v_a_4413_;
goto v___jp_4244_;
}
}
v___jp_4417_:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4415_, v___y_4431_);
lean_dec(v___x_4415_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4444_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4444_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4444_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
uint8_t v_lintOnly_4437_; uint8_t v_mode_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_lintOnly_4437_ = lean_ctor_get_uint8(v_args_4229_, sizeof(void*)*4);
v_mode_4438_ = lean_ctor_get_uint8(v_args_4229_, sizeof(void*)*4 + 1);
v___x_4439_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4427_);
lean_inc(v_quotContext_4426_);
lean_inc(v_maxHeartbeats_4425_);
lean_inc(v_openDecls_4423_);
lean_inc(v_currNamespace_4422_);
lean_inc(v_ref_4421_);
lean_inc_ref(v_fileMap_4419_);
lean_inc_ref(v_fileName_4418_);
v___x_4440_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4440_, 0, v_fileName_4418_);
lean_ctor_set(v___x_4440_, 1, v_fileMap_4419_);
lean_ctor_set(v___x_4440_, 2, v___x_4380_);
lean_ctor_set(v___x_4440_, 3, v_currRecDepth_4420_);
lean_ctor_set(v___x_4440_, 4, v___x_4439_);
lean_ctor_set(v___x_4440_, 5, v_ref_4421_);
lean_ctor_set(v___x_4440_, 6, v_currNamespace_4422_);
lean_ctor_set(v___x_4440_, 7, v_openDecls_4423_);
lean_ctor_set(v___x_4440_, 8, v_initHeartbeats_4424_);
lean_ctor_set(v___x_4440_, 9, v_maxHeartbeats_4425_);
lean_ctor_set(v___x_4440_, 10, v_quotContext_4426_);
lean_ctor_set(v___x_4440_, 11, v_currMacroScope_4427_);
lean_ctor_set(v___x_4440_, 12, v_cancelTk_x3f_4428_);
lean_ctor_set(v___x_4440_, 13, v_inheritedTraceOptions_4430_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*14, v___x_4416_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*14 + 1, v_suppressElabErrors_4429_);
if (v_lintOnly_4437_ == 0)
{
lean_del_object(v___x_4435_);
lean_dec_ref(v_linterOpts_4230_);
v___y_4385_ = v_mode_4438_;
v___y_4386_ = v_a_4433_;
v___y_4387_ = v___x_4440_;
v___y_4388_ = v___y_4431_;
v___y_4389_ = v___x_4414_;
goto v___jp_4384_;
}
else
{
lean_object* v___x_4442_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set_tag(v___x_4435_, 1);
lean_ctor_set(v___x_4435_, 0, v_linterOpts_4230_);
v___x_4442_ = v___x_4435_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_linterOpts_4230_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
v___y_4385_ = v_mode_4438_;
v___y_4386_ = v_a_4433_;
v___y_4387_ = v___x_4440_;
v___y_4388_ = v___y_4431_;
v___y_4389_ = v___x_4442_;
goto v___jp_4384_;
}
}
}
}
else
{
lean_object* v_a_4445_; 
lean_dec(v___y_4431_);
lean_dec_ref(v_inheritedTraceOptions_4430_);
lean_dec(v_cancelTk_x3f_4428_);
lean_dec(v_initHeartbeats_4424_);
lean_dec(v_currRecDepth_4420_);
lean_dec(v___x_4274_);
lean_dec(v_mod_4233_);
lean_dec(v_sp_4231_);
lean_dec_ref(v_linterOpts_4230_);
v_a_4445_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4445_);
lean_dec_ref_known(v___x_4432_, 1);
v_a_4245_ = v_a_4445_;
goto v___jp_4244_;
}
}
v___jp_4446_:
{
if (v___y_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v_env_4449_; lean_object* v_nextMacroScope_4450_; lean_object* v_ngen_4451_; lean_object* v_auxDeclNGen_4452_; lean_object* v_traceState_4453_; lean_object* v_messages_4454_; lean_object* v_infoState_4455_; lean_object* v_snapshotTasks_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4465_; 
v___x_4448_ = lean_st_ref_take(v___x_4274_);
v_env_4449_ = lean_ctor_get(v___x_4448_, 0);
v_nextMacroScope_4450_ = lean_ctor_get(v___x_4448_, 1);
v_ngen_4451_ = lean_ctor_get(v___x_4448_, 2);
v_auxDeclNGen_4452_ = lean_ctor_get(v___x_4448_, 3);
v_traceState_4453_ = lean_ctor_get(v___x_4448_, 4);
v_messages_4454_ = lean_ctor_get(v___x_4448_, 6);
v_infoState_4455_ = lean_ctor_get(v___x_4448_, 7);
v_snapshotTasks_4456_ = lean_ctor_get(v___x_4448_, 8);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4465_ == 0)
{
lean_object* v_unused_4466_; 
v_unused_4466_ = lean_ctor_get(v___x_4448_, 5);
lean_dec(v_unused_4466_);
v___x_4458_ = v___x_4448_;
v_isShared_4459_ = v_isSharedCheck_4465_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_snapshotTasks_4456_);
lean_inc(v_infoState_4455_);
lean_inc(v_messages_4454_);
lean_inc(v_traceState_4453_);
lean_inc(v_auxDeclNGen_4452_);
lean_inc(v_ngen_4451_);
lean_inc(v_nextMacroScope_4450_);
lean_inc(v_env_4449_);
lean_dec(v___x_4448_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4465_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = l_Lean_Kernel_enableDiag(v_env_4449_, v___x_4416_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 5, v___x_4260_);
lean_ctor_set(v___x_4458_, 0, v___x_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_nextMacroScope_4450_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v_ngen_4451_);
lean_ctor_set(v_reuseFailAlloc_4464_, 3, v_auxDeclNGen_4452_);
lean_ctor_set(v_reuseFailAlloc_4464_, 4, v_traceState_4453_);
lean_ctor_set(v_reuseFailAlloc_4464_, 5, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4464_, 6, v_messages_4454_);
lean_ctor_set(v_reuseFailAlloc_4464_, 7, v_infoState_4455_);
lean_ctor_set(v_reuseFailAlloc_4464_, 8, v_snapshotTasks_4456_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_st_ref_put(v___x_4274_, v___x_4462_);
lean_inc(v___x_4274_);
v_fileName_4418_ = v___x_4378_;
v_fileMap_4419_ = v___x_4379_;
v_currRecDepth_4420_ = v___x_4259_;
v_ref_4421_ = v___x_4381_;
v_currNamespace_4422_ = v___x_4266_;
v_openDecls_4423_ = v___x_4267_;
v_initHeartbeats_4424_ = v___x_4262_;
v_maxHeartbeats_4425_ = v___x_4382_;
v_quotContext_4426_ = v___x_4266_;
v_currMacroScope_4427_ = v___x_4263_;
v_cancelTk_x3f_4428_ = v___x_4414_;
v_suppressElabErrors_4429_ = v___x_4383_;
v_inheritedTraceOptions_4430_ = v___x_4375_;
v___y_4431_ = v___x_4274_;
goto v___jp_4417_;
}
}
}
else
{
lean_inc(v___x_4274_);
v_fileName_4418_ = v___x_4378_;
v_fileMap_4419_ = v___x_4379_;
v_currRecDepth_4420_ = v___x_4259_;
v_ref_4421_ = v___x_4381_;
v_currNamespace_4422_ = v___x_4266_;
v_openDecls_4423_ = v___x_4267_;
v_initHeartbeats_4424_ = v___x_4262_;
v_maxHeartbeats_4425_ = v___x_4382_;
v_quotContext_4426_ = v___x_4266_;
v_currMacroScope_4427_ = v___x_4263_;
v_cancelTk_x3f_4428_ = v___x_4414_;
v_suppressElabErrors_4429_ = v___x_4383_;
v_inheritedTraceOptions_4430_ = v___x_4375_;
v___y_4431_ = v___x_4274_;
goto v___jp_4417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4468_, lean_object* v_linterOpts_4469_, lean_object* v_sp_4470_, lean_object* v_env_4471_, lean_object* v_mod_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4468_, v_linterOpts_4469_, v_sp_4470_, v_env_4471_, v_mod_4472_);
lean_dec_ref(v_args_4468_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4475_, lean_object* v_t_4476_, lean_object* v_k_4477_, lean_object* v_fallback_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4476_, v_k_4477_, v_fallback_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4480_, lean_object* v_t_4481_, lean_object* v_k_4482_, lean_object* v_fallback_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4480_, v_t_4481_, v_k_4482_, v_fallback_4483_);
lean_dec(v_fallback_4483_);
lean_dec_ref(v_k_4482_);
lean_dec(v_t_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4485_, lean_object* v_k_4486_, lean_object* v_v_4487_, lean_object* v_t_4488_, lean_object* v_hl_4489_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4486_, v_v_4487_, v_t_4488_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4491_, lean_object* v_init_4492_, lean_object* v_x_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4491_, v_init_4492_, v_x_4493_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4498_, lean_object* v_init_4499_, lean_object* v_x_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4498_, v_init_4499_, v_x_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4505_, lean_object* v_constName_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4506_, v___y_4507_, v___y_4508_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4511_, lean_object* v_constName_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4511_, v_constName_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4517_, lean_object* v_ref_4518_, lean_object* v_constName_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4518_, v_constName_4519_, v___y_4520_, v___y_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4524_, lean_object* v_ref_4525_, lean_object* v_constName_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4524_, v_ref_4525_, v_constName_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v_ref_4525_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4531_, lean_object* v_ref_4532_, lean_object* v_msg_4533_, lean_object* v_declHint_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4532_, v_msg_4533_, v_declHint_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4539_, lean_object* v_ref_4540_, lean_object* v_msg_4541_, lean_object* v_declHint_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4539_, v_ref_4540_, v_msg_4541_, v_declHint_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v_ref_4540_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4547_, lean_object* v_declHint_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4547_, v_declHint_4548_, v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4553_, lean_object* v_declHint_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4553_, v_declHint_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4559_, lean_object* v_ref_4560_, lean_object* v_msg_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4560_, v_msg_4561_, v___y_4562_, v___y_4563_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4566_, lean_object* v_ref_4567_, lean_object* v_msg_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4566_, v_ref_4567_, v_msg_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v_ref_4567_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4573_, lean_object* v_msg_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4574_, v___y_4575_, v___y_4576_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4579_, lean_object* v_msg_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4579_, v_msg_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4585_){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; uint32_t v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4587_ = l_Std_Format_defWidth;
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = l_Std_Format_pretty(v_s_4585_, v___x_4587_, v___x_4588_, v___x_4588_);
v___x_4590_ = 10;
v___x_4591_ = lean_string_push(v___x_4589_, v___x_4590_);
v___x_4592_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4591_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4593_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4596_, size_t v_sz_4597_, size_t v_i_4598_, lean_object* v_b_4599_, lean_object* v___y_4600_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_lt(v_i_4598_, v_sz_4597_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_b_4599_);
return v___x_4603_;
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v_a_4604_ = lean_array_uget_borrowed(v_as_4596_, v_i_4598_);
v___x_4605_ = lean_box(0);
lean_inc(v_a_4604_);
v___x_4606_ = l_Lean_MessageData_format(v_a_4604_, v___x_4605_);
v___x_4607_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4606_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v___x_4608_; size_t v___x_4609_; size_t v___x_4610_; 
lean_dec_ref_known(v___x_4607_, 1);
v___x_4608_ = lean_box(0);
v___x_4609_ = ((size_t)1ULL);
v___x_4610_ = lean_usize_add(v_i_4598_, v___x_4609_);
v_i_4598_ = v___x_4610_;
v_b_4599_ = v___x_4608_;
goto _start;
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4624_; 
v_a_4612_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4614_ = v___x_4607_;
v_isShared_4615_ = v_isSharedCheck_4624_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4607_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4624_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_ref_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v_ref_4616_ = lean_ctor_get(v___y_4600_, 5);
v___x_4617_ = lean_io_error_to_string(v_a_4612_);
v___x_4618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
v___x_4619_ = l_Lean_MessageData_ofFormat(v___x_4618_);
lean_inc(v_ref_4616_);
v___x_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4620_, 0, v_ref_4616_);
lean_ctor_set(v___x_4620_, 1, v___x_4619_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4620_);
v___x_4622_ = v___x_4614_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4625_, lean_object* v_sz_4626_, lean_object* v_i_4627_, lean_object* v_b_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
size_t v_sz_boxed_4631_; size_t v_i_boxed_4632_; lean_object* v_res_4633_; 
v_sz_boxed_4631_ = lean_unbox_usize(v_sz_4626_);
lean_dec(v_sz_4626_);
v_i_boxed_4632_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4625_, v_sz_boxed_4631_, v_i_boxed_4632_, v_b_4628_, v___y_4629_);
lean_dec_ref(v___y_4629_);
lean_dec_ref(v_as_4625_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4634_, lean_object* v_entries_4635_, lean_object* v_____r_4636_, uint8_t v_anyFailed_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v___x_4641_; size_t v_sz_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_box(0);
v_sz_4642_ = lean_array_size(v_errors_4634_);
v___x_4643_ = ((size_t)0ULL);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4634_, v_sz_4642_, v___x_4643_, v___x_4641_, v___y_4638_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4653_; 
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; 
v_unused_4654_ = lean_ctor_get(v___x_4644_, 0);
lean_dec(v_unused_4654_);
v___x_4646_ = v___x_4644_;
v_isShared_4647_ = v_isSharedCheck_4653_;
goto v_resetjp_4645_;
}
else
{
lean_dec(v___x_4644_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4653_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4648_ = lean_box(v_anyFailed_4637_);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v_entries_4635_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v___x_4649_);
v___x_4651_ = v___x_4646_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec_ref(v_entries_4635_);
v_a_4655_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4644_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4644_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4663_, lean_object* v_entries_4664_, lean_object* v_____r_4665_, lean_object* v_anyFailed_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
uint8_t v_anyFailed_boxed_4670_; lean_object* v_res_4671_; 
v_anyFailed_boxed_4670_ = lean_unbox(v_anyFailed_4666_);
v_res_4671_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4663_, v_entries_4664_, v_____r_4665_, v_anyFailed_boxed_4670_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec_ref(v_errors_4663_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4672_, lean_object* v_env_4673_, lean_object* v_mod_4674_){
_start:
{
lean_object* v_a_4677_; lean_object* v_a_4681_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___y_4717_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v_env_4735_; uint8_t v_anyFailed_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; lean_object* v_fileName_4745_; lean_object* v_fileMap_4746_; lean_object* v_currRecDepth_4747_; lean_object* v_ref_4748_; lean_object* v_currNamespace_4749_; lean_object* v_openDecls_4750_; lean_object* v_initHeartbeats_4751_; lean_object* v_maxHeartbeats_4752_; lean_object* v_quotContext_4753_; lean_object* v_currMacroScope_4754_; lean_object* v_cancelTk_x3f_4755_; uint8_t v_suppressElabErrors_4756_; lean_object* v_inheritedTraceOptions_4757_; lean_object* v___y_4758_; uint8_t v___y_4777_; uint8_t v___x_4797_; 
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_unsigned_to_nat(32u);
v___x_4700_ = lean_mk_empty_array_with_capacity(v___x_4699_);
lean_dec_ref(v___x_4700_);
v___x_4701_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4702_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4703_ = lean_io_get_num_heartbeats();
v___x_4704_ = l_Lean_firstFrontendMacroScope;
v___x_4705_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4706_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4707_ = lean_box(0);
v___x_4708_ = lean_box(0);
v___x_4709_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4710_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4711_ = 1;
v___x_4712_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4713_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4714_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4714_, 0, v_env_4673_);
lean_ctor_set(v___x_4714_, 1, v___x_4705_);
lean_ctor_set(v___x_4714_, 2, v___x_4706_);
lean_ctor_set(v___x_4714_, 3, v___x_4709_);
lean_ctor_set(v___x_4714_, 4, v___x_4710_);
lean_ctor_set(v___x_4714_, 5, v___x_4701_);
lean_ctor_set(v___x_4714_, 6, v___x_4702_);
lean_ctor_set(v___x_4714_, 7, v___x_4712_);
lean_ctor_set(v___x_4714_, 8, v___x_4713_);
v___x_4715_ = lean_st_mk_ref(v___x_4714_);
v___x_4732_ = l_Lean_inheritedTraceOptions;
v___x_4733_ = lean_st_ref_get(v___x_4732_);
v___x_4734_ = lean_st_ref_get(v___x_4715_);
v_env_4735_ = lean_ctor_get(v___x_4734_, 0);
lean_inc_ref(v_env_4735_);
lean_dec(v___x_4734_);
v_anyFailed_4736_ = 0;
v___x_4737_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4738_ = l_Lean_instInhabitedFileMap_default;
v___x_4739_ = l_Lean_Options_empty;
v___x_4740_ = lean_box(0);
v___x_4741_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4742_ = lean_box(0);
v___x_4743_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4797_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4735_);
lean_dec_ref(v_env_4735_);
if (v___x_4743_ == 0)
{
if (v___x_4797_ == 0)
{
lean_inc(v___x_4715_);
v_fileName_4745_ = v___x_4737_;
v_fileMap_4746_ = v___x_4738_;
v_currRecDepth_4747_ = v___x_4698_;
v_ref_4748_ = v___x_4740_;
v_currNamespace_4749_ = v___x_4707_;
v_openDecls_4750_ = v___x_4708_;
v_initHeartbeats_4751_ = v___x_4703_;
v_maxHeartbeats_4752_ = v___x_4741_;
v_quotContext_4753_ = v___x_4707_;
v_currMacroScope_4754_ = v___x_4704_;
v_cancelTk_x3f_4755_ = v___x_4742_;
v_suppressElabErrors_4756_ = v_anyFailed_4736_;
v_inheritedTraceOptions_4757_ = v___x_4733_;
v___y_4758_ = v___x_4715_;
goto v___jp_4744_;
}
else
{
v___y_4777_ = v___x_4743_;
goto v___jp_4776_;
}
}
else
{
v___y_4777_ = v___x_4797_;
goto v___jp_4776_;
}
v___jp_4676_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_mk_io_user_error(v_a_4677_);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
v___jp_4680_:
{
if (lean_obj_tag(v_a_4681_) == 0)
{
lean_object* v_msg_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v_msg_4682_ = lean_ctor_get(v_a_4681_, 1);
lean_inc_ref(v_msg_4682_);
lean_dec_ref_known(v_a_4681_, 2);
v___x_4683_ = l_Lean_MessageData_toString(v_msg_4682_);
v___x_4684_ = lean_mk_io_user_error(v___x_4683_);
v___x_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
return v___x_4685_;
}
else
{
lean_object* v_id_4686_; lean_object* v___x_4687_; 
v_id_4686_ = lean_ctor_get(v_a_4681_, 0);
lean_inc(v_id_4686_);
lean_dec_ref_known(v_a_4681_, 2);
v___x_4687_ = l_Lean_InternalExceptionId_getName(v_id_4686_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
lean_dec(v_id_4686_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
v___x_4689_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4690_ = 1;
v___x_4691_ = l_Lean_Name_toString(v_a_4688_, v___x_4690_);
v___x_4692_ = lean_string_append(v___x_4689_, v___x_4691_);
lean_dec_ref(v___x_4691_);
v_a_4677_ = v___x_4692_;
goto v___jp_4676_;
}
else
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
lean_dec_ref_known(v___x_4687_, 1);
v___x_4693_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4694_ = l_Nat_reprFast(v_id_4686_);
v___x_4695_ = lean_string_append(v___x_4693_, v___x_4694_);
lean_dec_ref(v___x_4694_);
v___x_4696_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4697_ = lean_string_append(v___x_4695_, v___x_4696_);
v_a_4677_ = v___x_4697_;
goto v___jp_4676_;
}
}
}
v___jp_4716_:
{
if (lean_obj_tag(v___y_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4730_; 
v_a_4718_ = lean_ctor_get(v___y_4717_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___y_4717_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4720_ = v___y_4717_;
v_isShared_4721_ = v_isSharedCheck_4730_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___y_4717_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4730_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4722_; lean_object* v_fst_4723_; lean_object* v_snd_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; lean_object* v___x_4728_; 
v___x_4722_ = lean_st_ref_get(v___x_4715_);
lean_dec(v___x_4715_);
lean_dec(v___x_4722_);
v_fst_4723_ = lean_ctor_get(v_a_4718_, 0);
lean_inc(v_fst_4723_);
v_snd_4724_ = lean_ctor_get(v_a_4718_, 1);
lean_inc(v_snd_4724_);
lean_dec(v_a_4718_);
v___x_4725_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4725_, 0, v_fst_4723_);
v___x_4726_ = lean_unbox(v_snd_4724_);
lean_dec(v_snd_4724_);
lean_ctor_set_uint8(v___x_4725_, sizeof(void*)*1, v___x_4726_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 0, v___x_4725_);
v___x_4728_ = v___x_4720_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4725_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
}
else
{
lean_object* v_a_4731_; 
lean_dec(v___x_4715_);
v_a_4731_ = lean_ctor_get(v___y_4717_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___y_4717_, 1);
v_a_4681_ = v_a_4731_;
goto v___jp_4680_;
}
}
v___jp_4744_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4759_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4755_);
lean_inc(v_currMacroScope_4754_);
lean_inc(v_quotContext_4753_);
lean_inc(v_maxHeartbeats_4752_);
lean_inc(v_openDecls_4750_);
lean_inc(v_currNamespace_4749_);
lean_inc(v_ref_4748_);
lean_inc_ref(v_fileMap_4746_);
lean_inc_ref(v_fileName_4745_);
v___x_4760_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4760_, 0, v_fileName_4745_);
lean_ctor_set(v___x_4760_, 1, v_fileMap_4746_);
lean_ctor_set(v___x_4760_, 2, v___x_4739_);
lean_ctor_set(v___x_4760_, 3, v_currRecDepth_4747_);
lean_ctor_set(v___x_4760_, 4, v___x_4759_);
lean_ctor_set(v___x_4760_, 5, v_ref_4748_);
lean_ctor_set(v___x_4760_, 6, v_currNamespace_4749_);
lean_ctor_set(v___x_4760_, 7, v_openDecls_4750_);
lean_ctor_set(v___x_4760_, 8, v_initHeartbeats_4751_);
lean_ctor_set(v___x_4760_, 9, v_maxHeartbeats_4752_);
lean_ctor_set(v___x_4760_, 10, v_quotContext_4753_);
lean_ctor_set(v___x_4760_, 11, v_currMacroScope_4754_);
lean_ctor_set(v___x_4760_, 12, v_cancelTk_x3f_4755_);
lean_ctor_set(v___x_4760_, 13, v_inheritedTraceOptions_4757_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*14, v___x_4743_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*14 + 1, v_suppressElabErrors_4756_);
v___x_4761_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4760_, v___y_4758_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v_sp_4672_);
lean_ctor_set(v___x_4763_, 1, v_mod_4674_);
v___x_4764_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4762_, v___x_4763_, v___x_4760_, v___y_4758_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v_entries_4766_; lean_object* v_errors_4767_; lean_object* v___x_4768_; uint8_t v___x_4769_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v_entries_4766_ = lean_ctor_get(v_a_4765_, 0);
lean_inc_ref(v_entries_4766_);
v_errors_4767_ = lean_ctor_get(v_a_4765_, 1);
lean_inc_ref(v_errors_4767_);
lean_dec(v_a_4765_);
v___x_4768_ = lean_array_get_size(v_errors_4767_);
v___x_4769_ = lean_nat_dec_eq(v___x_4768_, v___x_4698_);
if (v___x_4769_ == 0)
{
lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4770_ = lean_box(0);
v___x_4771_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4767_, v_entries_4766_, v___x_4770_, v___x_4711_, v___x_4760_, v___y_4758_);
lean_dec(v___y_4758_);
lean_dec_ref_known(v___x_4760_, 14);
lean_dec_ref(v_errors_4767_);
v___y_4717_ = v___x_4771_;
goto v___jp_4716_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = lean_box(0);
v___x_4773_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4767_, v_entries_4766_, v___x_4772_, v_anyFailed_4736_, v___x_4760_, v___y_4758_);
lean_dec(v___y_4758_);
lean_dec_ref_known(v___x_4760_, 14);
lean_dec_ref(v_errors_4767_);
v___y_4717_ = v___x_4773_;
goto v___jp_4716_;
}
}
else
{
lean_object* v_a_4774_; 
lean_dec_ref_known(v___x_4760_, 14);
lean_dec(v___y_4758_);
lean_dec(v___x_4715_);
v_a_4774_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4764_, 1);
v_a_4681_ = v_a_4774_;
goto v___jp_4680_;
}
}
else
{
lean_object* v_a_4775_; 
lean_dec_ref_known(v___x_4760_, 14);
lean_dec(v___y_4758_);
lean_dec(v___x_4715_);
lean_dec(v_mod_4674_);
lean_dec(v_sp_4672_);
v_a_4775_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v___x_4761_, 1);
v_a_4681_ = v_a_4775_;
goto v___jp_4680_;
}
}
v___jp_4776_:
{
if (v___y_4777_ == 0)
{
lean_object* v___x_4778_; lean_object* v_env_4779_; lean_object* v_nextMacroScope_4780_; lean_object* v_ngen_4781_; lean_object* v_auxDeclNGen_4782_; lean_object* v_traceState_4783_; lean_object* v_messages_4784_; lean_object* v_infoState_4785_; lean_object* v_snapshotTasks_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4795_; 
v___x_4778_ = lean_st_ref_take(v___x_4715_);
v_env_4779_ = lean_ctor_get(v___x_4778_, 0);
v_nextMacroScope_4780_ = lean_ctor_get(v___x_4778_, 1);
v_ngen_4781_ = lean_ctor_get(v___x_4778_, 2);
v_auxDeclNGen_4782_ = lean_ctor_get(v___x_4778_, 3);
v_traceState_4783_ = lean_ctor_get(v___x_4778_, 4);
v_messages_4784_ = lean_ctor_get(v___x_4778_, 6);
v_infoState_4785_ = lean_ctor_get(v___x_4778_, 7);
v_snapshotTasks_4786_ = lean_ctor_get(v___x_4778_, 8);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v___x_4778_, 5);
lean_dec(v_unused_4796_);
v___x_4788_ = v___x_4778_;
v_isShared_4789_ = v_isSharedCheck_4795_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_snapshotTasks_4786_);
lean_inc(v_infoState_4785_);
lean_inc(v_messages_4784_);
lean_inc(v_traceState_4783_);
lean_inc(v_auxDeclNGen_4782_);
lean_inc(v_ngen_4781_);
lean_inc(v_nextMacroScope_4780_);
lean_inc(v_env_4779_);
lean_dec(v___x_4778_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4795_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4790_ = l_Lean_Kernel_enableDiag(v_env_4779_, v___x_4743_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 5, v___x_4701_);
lean_ctor_set(v___x_4788_, 0, v___x_4790_);
v___x_4792_ = v___x_4788_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v_nextMacroScope_4780_);
lean_ctor_set(v_reuseFailAlloc_4794_, 2, v_ngen_4781_);
lean_ctor_set(v_reuseFailAlloc_4794_, 3, v_auxDeclNGen_4782_);
lean_ctor_set(v_reuseFailAlloc_4794_, 4, v_traceState_4783_);
lean_ctor_set(v_reuseFailAlloc_4794_, 5, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4794_, 6, v_messages_4784_);
lean_ctor_set(v_reuseFailAlloc_4794_, 7, v_infoState_4785_);
lean_ctor_set(v_reuseFailAlloc_4794_, 8, v_snapshotTasks_4786_);
v___x_4792_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
lean_object* v___x_4793_; 
v___x_4793_ = lean_st_ref_put(v___x_4715_, v___x_4792_);
lean_inc(v___x_4715_);
v_fileName_4745_ = v___x_4737_;
v_fileMap_4746_ = v___x_4738_;
v_currRecDepth_4747_ = v___x_4698_;
v_ref_4748_ = v___x_4740_;
v_currNamespace_4749_ = v___x_4707_;
v_openDecls_4750_ = v___x_4708_;
v_initHeartbeats_4751_ = v___x_4703_;
v_maxHeartbeats_4752_ = v___x_4741_;
v_quotContext_4753_ = v___x_4707_;
v_currMacroScope_4754_ = v___x_4704_;
v_cancelTk_x3f_4755_ = v___x_4742_;
v_suppressElabErrors_4756_ = v_anyFailed_4736_;
v_inheritedTraceOptions_4757_ = v___x_4733_;
v___y_4758_ = v___x_4715_;
goto v___jp_4744_;
}
}
}
else
{
lean_inc(v___x_4715_);
v_fileName_4745_ = v___x_4737_;
v_fileMap_4746_ = v___x_4738_;
v_currRecDepth_4747_ = v___x_4698_;
v_ref_4748_ = v___x_4740_;
v_currNamespace_4749_ = v___x_4707_;
v_openDecls_4750_ = v___x_4708_;
v_initHeartbeats_4751_ = v___x_4703_;
v_maxHeartbeats_4752_ = v___x_4741_;
v_quotContext_4753_ = v___x_4707_;
v_currMacroScope_4754_ = v___x_4704_;
v_cancelTk_x3f_4755_ = v___x_4742_;
v_suppressElabErrors_4756_ = v_anyFailed_4736_;
v_inheritedTraceOptions_4757_ = v___x_4733_;
v___y_4758_ = v___x_4715_;
goto v___jp_4744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4798_, lean_object* v_env_4799_, lean_object* v_mod_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4798_, v_env_4799_, v_mod_4800_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4803_, size_t v_sz_4804_, size_t v_i_4805_, lean_object* v_b_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4803_, v_sz_4804_, v_i_4805_, v_b_4806_, v___y_4807_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4811_, lean_object* v_sz_4812_, lean_object* v_i_4813_, lean_object* v_b_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
size_t v_sz_boxed_4818_; size_t v_i_boxed_4819_; lean_object* v_res_4820_; 
v_sz_boxed_4818_ = lean_unbox_usize(v_sz_4812_);
lean_dec(v_sz_4812_);
v_i_boxed_4819_ = lean_unbox_usize(v_i_4813_);
lean_dec(v_i_4813_);
v_res_4820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4811_, v_sz_boxed_4818_, v_i_boxed_4819_, v_b_4814_, v___y_4815_, v___y_4816_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec_ref(v_as_4811_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_enable_initializer_execution();
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4825_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = lean_compacted_region_free(v_region_4825_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4828_, lean_object* v_a_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4828_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4834_, lean_object* v_k_4835_, uint8_t v_v_4836_){
_start:
{
lean_object* v_map_4837_; uint8_t v_hasTrace_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4852_; 
v_map_4837_ = lean_ctor_get(v_o_4834_, 0);
v_hasTrace_4838_ = lean_ctor_get_uint8(v_o_4834_, sizeof(void*)*1);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_o_4834_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4840_ = v_o_4834_;
v_isShared_4841_ = v_isSharedCheck_4852_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_map_4837_);
lean_dec(v_o_4834_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4852_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4842_, 0, v_v_4836_);
lean_inc(v_k_4835_);
v___x_4843_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4835_, v___x_4842_, v_map_4837_);
if (v_hasTrace_4838_ == 0)
{
lean_object* v___x_4844_; uint8_t v___x_4845_; lean_object* v___x_4847_; 
v___x_4844_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4845_ = l_Lean_Name_isPrefixOf(v___x_4844_, v_k_4835_);
lean_dec(v_k_4835_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4843_);
v___x_4847_ = v___x_4840_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4843_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
lean_ctor_set_uint8(v___x_4847_, sizeof(void*)*1, v___x_4845_);
return v___x_4847_;
}
}
else
{
lean_object* v___x_4850_; 
lean_dec(v_k_4835_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4843_);
v___x_4850_ = v___x_4840_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4843_);
lean_ctor_set_uint8(v_reuseFailAlloc_4851_, sizeof(void*)*1, v_hasTrace_4838_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4853_, lean_object* v_k_4854_, lean_object* v_v_4855_){
_start:
{
uint8_t v_v_boxed_4856_; lean_object* v_res_4857_; 
v_v_boxed_4856_ = lean_unbox(v_v_4855_);
v_res_4857_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4853_, v_k_4854_, v_v_boxed_4856_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4858_){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; uint32_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4860_ = lean_unsigned_to_nat(80u);
v___x_4861_ = l_Lean_Json_pretty(v_s_4858_, v___x_4860_);
v___x_4862_ = 10;
v___x_4863_ = lean_string_push(v___x_4861_, v___x_4862_);
v___x_4864_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4865_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4868_, size_t v_sz_4869_, size_t v_i_4870_, lean_object* v_b_4871_){
_start:
{
uint8_t v___x_4873_; 
v___x_4873_ = lean_usize_dec_lt(v_i_4870_, v_sz_4869_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; 
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_b_4871_);
return v___x_4874_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v_a_4875_ = lean_array_uget_borrowed(v_as_4868_, v_i_4870_);
lean_inc(v_a_4875_);
v___x_4876_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4875_);
v___x_4877_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4876_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v___x_4878_; size_t v___x_4879_; size_t v___x_4880_; 
lean_dec_ref_known(v___x_4877_, 1);
v___x_4878_ = lean_box(0);
v___x_4879_ = ((size_t)1ULL);
v___x_4880_ = lean_usize_add(v_i_4870_, v___x_4879_);
v_i_4870_ = v___x_4880_;
v_b_4871_ = v___x_4878_;
goto _start;
}
else
{
return v___x_4877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4882_, lean_object* v_sz_4883_, lean_object* v_i_4884_, lean_object* v_b_4885_, lean_object* v___y_4886_){
_start:
{
size_t v_sz_boxed_4887_; size_t v_i_boxed_4888_; lean_object* v_res_4889_; 
v_sz_boxed_4887_ = lean_unbox_usize(v_sz_4883_);
lean_dec(v_sz_4883_);
v_i_boxed_4888_ = lean_unbox_usize(v_i_4884_);
lean_dec(v_i_4884_);
v_res_4889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4882_, v_sz_boxed_4887_, v_i_boxed_4888_, v_b_4885_);
lean_dec_ref(v_as_4882_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4890_, size_t v_sz_4891_, size_t v_i_4892_, lean_object* v_bs_4893_){
_start:
{
uint8_t v_anyUnlocated_4894_; 
v_anyUnlocated_4894_ = lean_usize_dec_lt(v_i_4892_, v_sz_4891_);
if (v_anyUnlocated_4894_ == 0)
{
return v_bs_4893_;
}
else
{
lean_object* v___x_4895_; uint8_t v_anyFailed_4896_; lean_object* v_v_4897_; lean_object* v_bs_x27_4898_; lean_object* v___x_4899_; size_t v___x_4900_; size_t v___x_4901_; lean_object* v___x_4902_; 
v___x_4895_ = lean_unsigned_to_nat(0u);
v_anyFailed_4896_ = lean_nat_dec_eq(v___x_4890_, v___x_4895_);
v_v_4897_ = lean_array_uget(v_bs_4893_, v_i_4892_);
v_bs_x27_4898_ = lean_array_uset(v_bs_4893_, v_i_4892_, v___x_4895_);
v___x_4899_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4899_, 0, v_v_4897_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*1, v_anyFailed_4896_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*1 + 1, v_anyUnlocated_4894_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*1 + 2, v_anyFailed_4896_);
v___x_4900_ = ((size_t)1ULL);
v___x_4901_ = lean_usize_add(v_i_4892_, v___x_4900_);
v___x_4902_ = lean_array_uset(v_bs_x27_4898_, v_i_4892_, v___x_4899_);
v_i_4892_ = v___x_4901_;
v_bs_4893_ = v___x_4902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4904_, lean_object* v_sz_4905_, lean_object* v_i_4906_, lean_object* v_bs_4907_){
_start:
{
size_t v_sz_boxed_4908_; size_t v_i_boxed_4909_; lean_object* v_res_4910_; 
v_sz_boxed_4908_ = lean_unbox_usize(v_sz_4905_);
lean_dec(v_sz_4905_);
v_i_boxed_4909_ = lean_unbox_usize(v_i_4906_);
lean_dec(v_i_4906_);
v_res_4910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4904_, v_sz_boxed_4908_, v_i_boxed_4909_, v_bs_4907_);
lean_dec(v___x_4904_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4911_, size_t v_i_4912_, size_t v_stop_4913_, lean_object* v_b_4914_){
_start:
{
uint8_t v___x_4915_; 
v___x_4915_ = lean_usize_dec_eq(v_i_4912_, v_stop_4913_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4916_; lean_object* v_fst_4917_; lean_object* v_snd_4918_; uint8_t v___x_4919_; lean_object* v___x_4920_; size_t v___x_4921_; size_t v___x_4922_; 
v___x_4916_ = lean_array_uget_borrowed(v_as_4911_, v_i_4912_);
v_fst_4917_ = lean_ctor_get(v___x_4916_, 0);
v_snd_4918_ = lean_ctor_get(v___x_4916_, 1);
v___x_4919_ = lean_unbox(v_snd_4918_);
lean_inc(v_fst_4917_);
v___x_4920_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4914_, v_fst_4917_, v___x_4919_);
v___x_4921_ = ((size_t)1ULL);
v___x_4922_ = lean_usize_add(v_i_4912_, v___x_4921_);
v_i_4912_ = v___x_4922_;
v_b_4914_ = v___x_4920_;
goto _start;
}
else
{
return v_b_4914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4924_, lean_object* v_i_4925_, lean_object* v_stop_4926_, lean_object* v_b_4927_){
_start:
{
size_t v_i_boxed_4928_; size_t v_stop_boxed_4929_; lean_object* v_res_4930_; 
v_i_boxed_4928_ = lean_unbox_usize(v_i_4925_);
lean_dec(v_i_4925_);
v_stop_boxed_4929_ = lean_unbox_usize(v_stop_4926_);
lean_dec(v_stop_4926_);
v_res_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4924_, v_i_boxed_4928_, v_stop_boxed_4929_, v_b_4927_);
lean_dec_ref(v_as_4924_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4940_, lean_object* v_checkImports_4941_, lean_object* v_args_4942_, lean_object* v___x_4943_, lean_object* v_as_4944_, size_t v_sz_4945_, size_t v_i_4946_, lean_object* v_b_4947_){
_start:
{
lean_object* v_a_4950_; lean_object* v___x_4954_; uint8_t v_anyFailed_4955_; uint8_t v_anyUnlocated_4956_; lean_object* v___x_4957_; lean_object* v_envLinterModule_4958_; uint8_t v___x_4959_; 
v___x_4954_ = lean_unsigned_to_nat(0u);
v_anyFailed_4955_ = lean_nat_dec_eq(v___x_4940_, v___x_4954_);
v_anyUnlocated_4956_ = 1;
v___x_4957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4958_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4958_, 0, v___x_4957_);
lean_ctor_set_uint8(v_envLinterModule_4958_, sizeof(void*)*1, v_anyFailed_4955_);
lean_ctor_set_uint8(v_envLinterModule_4958_, sizeof(void*)*1 + 1, v_anyUnlocated_4956_);
lean_ctor_set_uint8(v_envLinterModule_4958_, sizeof(void*)*1 + 2, v_anyFailed_4955_);
v___x_4959_ = lean_usize_dec_lt(v_i_4946_, v_sz_4945_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; 
lean_dec_ref_known(v_envLinterModule_4958_, 1);
lean_dec(v___x_4943_);
v___x_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4960_, 0, v_b_4947_);
return v___x_4960_;
}
else
{
lean_object* v___x_4961_; lean_object* v_a_4962_; lean_object* v___x_4963_; 
v___x_4961_ = lean_enable_initializer_execution();
v_a_4962_ = lean_array_uget_borrowed(v_as_4944_, v_i_4946_);
lean_inc(v_a_4962_);
v___x_4963_ = l_Lean_findOLean(v_a_4962_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v___x_4965_ = l_Lean_readModuleData(v_a_4964_);
lean_dec(v_a_4964_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v_fst_4967_; lean_object* v_snd_4968_; uint8_t v___x_4969_; lean_object* v_snd_4970_; lean_object* v_snd_4971_; lean_object* v_snd_4972_; lean_object* v_snd_4973_; lean_object* v_fst_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5262_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v_fst_4967_ = lean_ctor_get(v_a_4966_, 0);
lean_inc(v_fst_4967_);
v_snd_4968_ = lean_ctor_get(v_a_4966_, 1);
lean_inc(v_snd_4968_);
lean_dec(v_a_4966_);
v___x_4969_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4967_);
lean_dec(v_fst_4967_);
v_snd_4970_ = lean_ctor_get(v_b_4947_, 1);
lean_inc(v_snd_4970_);
v_snd_4971_ = lean_ctor_get(v_snd_4970_, 1);
lean_inc(v_snd_4971_);
v_snd_4972_ = lean_ctor_get(v_snd_4971_, 1);
lean_inc(v_snd_4972_);
v_snd_4973_ = lean_ctor_get(v_snd_4972_, 1);
lean_inc(v_snd_4973_);
v_fst_4974_ = lean_ctor_get(v_b_4947_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v_b_4947_);
if (v_isSharedCheck_5262_ == 0)
{
lean_object* v_unused_5263_; 
v_unused_5263_ = lean_ctor_get(v_b_4947_, 1);
lean_dec(v_unused_5263_);
v___x_4976_ = v_b_4947_;
v_isShared_4977_ = v_isSharedCheck_5262_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_fst_4974_);
lean_dec(v_b_4947_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5262_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v_fst_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5260_; 
v_fst_4978_ = lean_ctor_get(v_snd_4970_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v_snd_4970_);
if (v_isSharedCheck_5260_ == 0)
{
lean_object* v_unused_5261_; 
v_unused_5261_ = lean_ctor_get(v_snd_4970_, 1);
lean_dec(v_unused_5261_);
v___x_4980_ = v_snd_4970_;
v_isShared_4981_ = v_isSharedCheck_5260_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_fst_4978_);
lean_dec(v_snd_4970_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5260_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v_fst_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5258_; 
v_fst_4982_ = lean_ctor_get(v_snd_4971_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_snd_4971_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_snd_4971_, 1);
lean_dec(v_unused_5259_);
v___x_4984_ = v_snd_4971_;
v_isShared_4985_ = v_isSharedCheck_5258_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_fst_4982_);
lean_dec(v_snd_4971_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5258_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v_fst_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5256_; 
v_fst_4986_ = lean_ctor_get(v_snd_4972_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_snd_4972_);
if (v_isSharedCheck_5256_ == 0)
{
lean_object* v_unused_5257_; 
v_unused_5257_ = lean_ctor_get(v_snd_4972_, 1);
lean_dec(v_unused_5257_);
v___x_4988_ = v_snd_4972_;
v_isShared_4989_ = v_isSharedCheck_5256_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_fst_4986_);
lean_dec(v_snd_4972_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5256_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v_fst_4990_; lean_object* v_snd_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5255_; 
v_fst_4990_ = lean_ctor_get(v_snd_4973_, 0);
v_snd_4991_ = lean_ctor_get(v_snd_4973_, 1);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_snd_4973_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_4993_ = v_snd_4973_;
v_isShared_4994_ = v_isSharedCheck_5255_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_snd_4991_);
lean_inc(v_fst_4990_);
lean_dec(v_snd_4973_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5255_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___y_4996_; lean_object* v___y_4997_; uint8_t v_anyFailed_4998_; uint8_t v_anyUnlocated_4999_; lean_object* v_records_5000_; lean_object* v_codeQualityEntries_5001_; lean_object* v___y_5148_; lean_object* v___y_5149_; uint8_t v_anyFailed_5150_; uint8_t v_anyUnlocated_5151_; lean_object* v_records_5152_; lean_object* v_codeQualityEntries_5153_; lean_object* v___x_5170_; lean_object* v___y_5172_; lean_object* v___y_5173_; uint8_t v___y_5213_; 
v___x_5170_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
if (v___x_4969_ == 0)
{
uint8_t v___x_5253_; 
v___x_5253_ = 2;
v___y_5213_ = v___x_5253_;
goto v___jp_5212_;
}
else
{
uint8_t v___x_5254_; 
v___x_5254_ = 1;
v___y_5213_ = v___x_5254_;
goto v___jp_5212_;
}
v___jp_4995_:
{
uint8_t v_mode_5002_; uint8_t v___x_5003_; uint8_t v___x_5004_; 
v_mode_5002_ = lean_ctor_get_uint8(v_args_4942_, sizeof(void*)*4 + 1);
v___x_5003_ = 2;
v___x_5004_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_5002_, v___x_5003_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = l_Lean_Name_getRoot(v_a_4962_);
lean_inc(v___x_4943_);
v___x_5006_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4942_, v___y_4997_, v___x_4943_, v___y_4996_, v___x_5005_, v_fst_4990_);
lean_dec_ref(v___y_4997_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; lean_object* v_outcome_5008_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v_outcome_5008_ = lean_ctor_get(v_a_5007_, 0);
if (lean_obj_tag(v_outcome_5008_) == 0)
{
uint8_t v_failed_5009_; 
v_failed_5009_ = lean_ctor_get_uint8(v_outcome_5008_, 0);
if (v_failed_5009_ == 0)
{
lean_object* v_checkedModules_5010_; lean_object* v___x_5012_; 
v_checkedModules_5010_ = lean_ctor_get(v_a_5007_, 1);
lean_inc(v_checkedModules_5010_);
lean_dec(v_a_5007_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 0, v_checkedModules_5010_);
v___x_5012_ = v___x_4993_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_checkedModules_5010_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_snd_4991_);
v___x_5012_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5014_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5012_);
lean_ctor_set(v___x_4988_, 0, v_codeQualityEntries_5001_);
v___x_5014_ = v___x_4988_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_codeQualityEntries_5001_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v___x_5012_);
v___x_5014_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5016_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5014_);
lean_ctor_set(v___x_4984_, 0, v_records_5000_);
v___x_5016_ = v___x_4984_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_records_5000_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = lean_box(v_anyUnlocated_4999_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5016_);
lean_ctor_set(v___x_4980_, 0, v___x_5017_);
v___x_5019_ = v___x_4980_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5017_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5016_);
v___x_5019_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5020_ = lean_box(v_anyFailed_4998_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5019_);
lean_ctor_set(v___x_4976_, 0, v___x_5020_);
v___x_5022_ = v___x_4976_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v___x_5019_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
v_a_4950_ = v___x_5022_;
goto v___jp_4949_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5028_; lean_object* v___x_5030_; 
v_checkedModules_5028_ = lean_ctor_get(v_a_5007_, 1);
lean_inc(v_checkedModules_5028_);
lean_dec(v_a_5007_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 0, v_checkedModules_5028_);
v___x_5030_ = v___x_4993_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_checkedModules_5028_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v_snd_4991_);
v___x_5030_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5032_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5030_);
lean_ctor_set(v___x_4988_, 0, v_codeQualityEntries_5001_);
v___x_5032_ = v___x_4988_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_codeQualityEntries_5001_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___x_5030_);
v___x_5032_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5034_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5032_);
lean_ctor_set(v___x_4984_, 0, v_records_5000_);
v___x_5034_ = v___x_4984_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_records_5000_);
lean_ctor_set(v_reuseFailAlloc_5043_, 1, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5035_; lean_object* v___x_5037_; 
v___x_5035_ = lean_box(v_anyUnlocated_4999_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5034_);
lean_ctor_set(v___x_4980_, 0, v___x_5035_);
v___x_5037_ = v___x_4980_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5035_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v___x_5034_);
v___x_5037_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5040_; 
v___x_5038_ = lean_box(v_anyUnlocated_4956_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5037_);
lean_ctor_set(v___x_4976_, 0, v___x_5038_);
v___x_5040_ = v___x_4976_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5038_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v___x_5037_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
v_a_4950_ = v___x_5040_;
goto v___jp_4949_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5046_; lean_object* v_records_5047_; uint8_t v_unlocated_5048_; lean_object* v___x_5049_; 
lean_inc_ref(v_outcome_5008_);
v_checkedModules_5046_ = lean_ctor_get(v_a_5007_, 1);
lean_inc(v_checkedModules_5046_);
lean_dec(v_a_5007_);
v_records_5047_ = lean_ctor_get(v_outcome_5008_, 0);
lean_inc_ref(v_records_5047_);
v_unlocated_5048_ = lean_ctor_get_uint8(v_outcome_5008_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_5008_, 1);
v___x_5049_ = l_Array_append___redArg(v_records_5000_, v_records_5047_);
lean_dec_ref(v_records_5047_);
if (v_unlocated_5048_ == 0)
{
lean_object* v___x_5051_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 0, v_checkedModules_5046_);
v___x_5051_ = v___x_4993_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_checkedModules_5046_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_snd_4991_);
v___x_5051_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
lean_object* v___x_5053_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5051_);
lean_ctor_set(v___x_4988_, 0, v_codeQualityEntries_5001_);
v___x_5053_ = v___x_4988_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_codeQualityEntries_5001_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
lean_object* v___x_5055_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5053_);
lean_ctor_set(v___x_4984_, 0, v___x_5049_);
v___x_5055_ = v___x_4984_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5049_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_box(v_anyUnlocated_4999_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5055_);
lean_ctor_set(v___x_4980_, 0, v___x_5056_);
v___x_5058_ = v___x_4980_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5056_);
lean_ctor_set(v_reuseFailAlloc_5063_, 1, v___x_5055_);
v___x_5058_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; lean_object* v___x_5061_; 
v___x_5059_ = lean_box(v_anyFailed_4998_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5058_);
lean_ctor_set(v___x_4976_, 0, v___x_5059_);
v___x_5061_ = v___x_4976_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v___x_5058_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
v_a_4950_ = v___x_5061_;
goto v___jp_4949_;
}
}
}
}
}
}
else
{
lean_object* v___x_5068_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 0, v_checkedModules_5046_);
v___x_5068_ = v___x_4993_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_checkedModules_5046_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_snd_4991_);
v___x_5068_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5070_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5068_);
lean_ctor_set(v___x_4988_, 0, v_codeQualityEntries_5001_);
v___x_5070_ = v___x_4988_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_codeQualityEntries_5001_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5072_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5070_);
lean_ctor_set(v___x_4984_, 0, v___x_5049_);
v___x_5072_ = v___x_4984_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5049_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5073_ = lean_box(v_anyUnlocated_4956_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5072_);
lean_ctor_set(v___x_4980_, 0, v___x_5073_);
v___x_5075_ = v___x_4980_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5072_);
v___x_5075_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5078_; 
v___x_5076_ = lean_box(v_anyFailed_4998_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5075_);
lean_ctor_set(v___x_4976_, 0, v___x_5076_);
v___x_5078_ = v___x_4976_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v___x_5075_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
v_a_4950_ = v___x_5078_;
goto v___jp_4949_;
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
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
lean_dec_ref(v_codeQualityEntries_5001_);
lean_dec_ref(v_records_5000_);
lean_del_object(v___x_4993_);
lean_dec(v_snd_4991_);
lean_del_object(v___x_4988_);
lean_del_object(v___x_4984_);
lean_del_object(v___x_4980_);
lean_del_object(v___x_4976_);
lean_dec(v___x_4943_);
v_a_5084_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5086_ = v___x_5006_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5006_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
else
{
lean_object* v___x_5092_; lean_object* v_fst_5093_; lean_object* v_snd_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5146_; 
lean_del_object(v___x_4976_);
v___x_5092_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4942_, v___y_4997_, v___y_4996_, v_a_4962_, v_snd_4991_);
lean_dec_ref(v___y_4997_);
v_fst_5093_ = lean_ctor_get(v___x_5092_, 0);
v_snd_5094_ = lean_ctor_get(v___x_5092_, 1);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5096_ = v___x_5092_;
v_isShared_5097_ = v_isSharedCheck_5146_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_snd_5094_);
lean_inc(v_fst_5093_);
lean_dec(v___x_5092_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5146_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; 
lean_inc(v_a_4962_);
lean_inc(v___x_4943_);
v___x_5098_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4943_, v___y_4996_, v_a_4962_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v_entries_5100_; uint8_t v_failed_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v_entries_5100_ = lean_ctor_get(v_a_5099_, 0);
lean_inc_ref(v_entries_5100_);
v_failed_5101_ = lean_ctor_get_uint8(v_a_5099_, sizeof(void*)*1);
lean_dec(v_a_5099_);
v___x_5102_ = l_Array_append___redArg(v_codeQualityEntries_5001_, v_fst_5093_);
lean_dec(v_fst_5093_);
v___x_5103_ = l_Array_append___redArg(v___x_5102_, v_entries_5100_);
lean_dec_ref(v_entries_5100_);
if (v_failed_5101_ == 0)
{
lean_object* v___x_5105_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v_fst_4990_);
v___x_5105_ = v___x_5096_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_fst_4990_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v_snd_5094_);
v___x_5105_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5107_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5105_);
lean_ctor_set(v___x_4993_, 0, v___x_5103_);
v___x_5107_ = v___x_4993_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5103_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5107_);
lean_ctor_set(v___x_4988_, 0, v_records_5000_);
v___x_5109_ = v___x_4988_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_records_5000_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5110_ = lean_box(v_anyUnlocated_4999_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5109_);
lean_ctor_set(v___x_4984_, 0, v___x_5110_);
v___x_5112_ = v___x_4984_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5117_, 1, v___x_5109_);
v___x_5112_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
lean_object* v___x_5113_; lean_object* v___x_5115_; 
v___x_5113_ = lean_box(v_anyFailed_4998_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5112_);
lean_ctor_set(v___x_4980_, 0, v___x_5113_);
v___x_5115_ = v___x_4980_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v___x_5112_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
v_a_4950_ = v___x_5115_;
goto v___jp_4949_;
}
}
}
}
}
}
else
{
lean_object* v___x_5122_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v_fst_4990_);
v___x_5122_ = v___x_5096_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_fst_4990_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_snd_5094_);
v___x_5122_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
lean_object* v___x_5124_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5122_);
lean_ctor_set(v___x_4993_, 0, v___x_5103_);
v___x_5124_ = v___x_4993_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5103_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v___x_5122_);
v___x_5124_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5126_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5124_);
lean_ctor_set(v___x_4988_, 0, v_records_5000_);
v___x_5126_ = v___x_4988_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_records_5000_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; lean_object* v___x_5129_; 
v___x_5127_ = lean_box(v_anyUnlocated_4999_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5126_);
lean_ctor_set(v___x_4984_, 0, v___x_5127_);
v___x_5129_ = v___x_4984_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5127_);
lean_ctor_set(v_reuseFailAlloc_5134_, 1, v___x_5126_);
v___x_5129_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5130_ = lean_box(v_anyUnlocated_4956_);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v___x_5129_);
lean_ctor_set(v___x_4980_, 0, v___x_5130_);
v___x_5132_ = v___x_4980_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5133_, 1, v___x_5129_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
v_a_4950_ = v___x_5132_;
goto v___jp_4949_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_del_object(v___x_5096_);
lean_dec(v_snd_5094_);
lean_dec(v_fst_5093_);
lean_dec_ref(v_codeQualityEntries_5001_);
lean_dec_ref(v_records_5000_);
lean_del_object(v___x_4993_);
lean_dec(v_fst_4990_);
lean_del_object(v___x_4988_);
lean_del_object(v___x_4984_);
lean_del_object(v___x_4980_);
lean_dec(v___x_4943_);
v_a_5138_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5098_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5098_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
}
}
v___jp_5147_:
{
lean_object* v___x_5154_; 
lean_inc(v_a_4962_);
lean_inc_ref(v___y_5148_);
lean_inc(v___x_4943_);
lean_inc_ref(v___y_5149_);
v___x_5154_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4942_, v___y_5149_, v___x_4943_, v___y_5148_, v_a_4962_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5154_, 1);
switch(lean_obj_tag(v_a_5155_))
{
case 0:
{
uint8_t v_failed_5156_; 
v_failed_5156_ = lean_ctor_get_uint8(v_a_5155_, 0);
lean_dec_ref_known(v_a_5155_, 0);
if (v_failed_5156_ == 0)
{
v___y_4996_ = v___y_5148_;
v___y_4997_ = v___y_5149_;
v_anyFailed_4998_ = v_anyFailed_5150_;
v_anyUnlocated_4999_ = v_anyUnlocated_5151_;
v_records_5000_ = v_records_5152_;
v_codeQualityEntries_5001_ = v_codeQualityEntries_5153_;
goto v___jp_4995_;
}
else
{
v___y_4996_ = v___y_5148_;
v___y_4997_ = v___y_5149_;
v_anyFailed_4998_ = v_anyUnlocated_4956_;
v_anyUnlocated_4999_ = v_anyUnlocated_5151_;
v_records_5000_ = v_records_5152_;
v_codeQualityEntries_5001_ = v_codeQualityEntries_5153_;
goto v___jp_4995_;
}
}
case 1:
{
lean_object* v_records_5157_; uint8_t v_unlocated_5158_; lean_object* v___x_5159_; 
v_records_5157_ = lean_ctor_get(v_a_5155_, 0);
lean_inc_ref(v_records_5157_);
v_unlocated_5158_ = lean_ctor_get_uint8(v_a_5155_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5155_, 1);
v___x_5159_ = l_Array_append___redArg(v_records_5152_, v_records_5157_);
lean_dec_ref(v_records_5157_);
if (v_unlocated_5158_ == 0)
{
v___y_4996_ = v___y_5148_;
v___y_4997_ = v___y_5149_;
v_anyFailed_4998_ = v_anyFailed_5150_;
v_anyUnlocated_4999_ = v_anyUnlocated_5151_;
v_records_5000_ = v___x_5159_;
v_codeQualityEntries_5001_ = v_codeQualityEntries_5153_;
goto v___jp_4995_;
}
else
{
v___y_4996_ = v___y_5148_;
v___y_4997_ = v___y_5149_;
v_anyFailed_4998_ = v_anyFailed_5150_;
v_anyUnlocated_4999_ = v_anyUnlocated_4956_;
v_records_5000_ = v___x_5159_;
v_codeQualityEntries_5001_ = v_codeQualityEntries_5153_;
goto v___jp_4995_;
}
}
default: 
{
lean_object* v_entries_5160_; lean_object* v___x_5161_; 
v_entries_5160_ = lean_ctor_get(v_a_5155_, 0);
lean_inc_ref(v_entries_5160_);
lean_dec_ref_known(v_a_5155_, 1);
v___x_5161_ = l_Array_append___redArg(v_codeQualityEntries_5153_, v_entries_5160_);
lean_dec_ref(v_entries_5160_);
v___y_4996_ = v___y_5148_;
v___y_4997_ = v___y_5149_;
v_anyFailed_4998_ = v_anyFailed_5150_;
v_anyUnlocated_4999_ = v_anyUnlocated_5151_;
v_records_5000_ = v_records_5152_;
v_codeQualityEntries_5001_ = v___x_5161_;
goto v___jp_4995_;
}
}
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
lean_dec_ref(v_codeQualityEntries_5153_);
lean_dec_ref(v_records_5152_);
lean_dec_ref(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_del_object(v___x_4993_);
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_del_object(v___x_4988_);
lean_del_object(v___x_4984_);
lean_del_object(v___x_4980_);
lean_del_object(v___x_4976_);
lean_dec(v___x_4943_);
v_a_5162_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5154_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5154_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
v___jp_5171_:
{
lean_object* v___x_5174_; lean_object* v_toEnvExtension_5175_; lean_object* v_asyncMode_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v_merged_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5210_; 
v___x_5174_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5175_ = lean_ctor_get(v___x_5174_, 0);
v_asyncMode_5176_ = lean_ctor_get(v_toEnvExtension_5175_, 2);
v___x_5177_ = lean_box(0);
lean_inc_ref(v___y_5172_);
v___x_5178_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5170_, v___x_5174_, v___y_5172_, v_asyncMode_5176_, v___x_5177_);
v_merged_5179_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5210_ == 0)
{
lean_object* v_unused_5211_; 
v_unused_5211_ = lean_ctor_get(v___x_5178_, 1);
lean_dec(v_unused_5211_);
v___x_5181_ = v___x_5178_;
v_isShared_5182_ = v_isSharedCheck_5210_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_merged_5179_);
lean_dec(v___x_5178_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5210_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 1, v_merged_5179_);
lean_ctor_set(v___x_5181_, 0, v___y_5173_);
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___y_5173_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_merged_5179_);
v___x_5184_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5185_; 
v___x_5185_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4942_, v___x_5184_, v___y_5172_, v_a_4962_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref_known(v___x_5185_, 1);
switch(lean_obj_tag(v_a_5186_))
{
case 0:
{
uint8_t v___x_5187_; 
v___x_5187_ = lean_unbox(v_fst_4974_);
lean_dec(v_fst_4974_);
if (v___x_5187_ == 0)
{
uint8_t v_failed_5188_; uint8_t v___x_5189_; 
v_failed_5188_ = lean_ctor_get_uint8(v_a_5186_, 0);
lean_dec_ref_known(v_a_5186_, 0);
v___x_5189_ = lean_unbox(v_fst_4978_);
lean_dec(v_fst_4978_);
v___y_5148_ = v___y_5172_;
v___y_5149_ = v___x_5184_;
v_anyFailed_5150_ = v_failed_5188_;
v_anyUnlocated_5151_ = v___x_5189_;
v_records_5152_ = v_fst_4982_;
v_codeQualityEntries_5153_ = v_fst_4986_;
goto v___jp_5147_;
}
else
{
uint8_t v___x_5190_; 
lean_dec_ref_known(v_a_5186_, 0);
v___x_5190_ = lean_unbox(v_fst_4978_);
lean_dec(v_fst_4978_);
v___y_5148_ = v___y_5172_;
v___y_5149_ = v___x_5184_;
v_anyFailed_5150_ = v_anyUnlocated_4956_;
v_anyUnlocated_5151_ = v___x_5190_;
v_records_5152_ = v_fst_4982_;
v_codeQualityEntries_5153_ = v_fst_4986_;
goto v___jp_5147_;
}
}
case 1:
{
lean_object* v_records_5191_; uint8_t v_unlocated_5192_; lean_object* v___x_5193_; 
v_records_5191_ = lean_ctor_get(v_a_5186_, 0);
lean_inc_ref(v_records_5191_);
v_unlocated_5192_ = lean_ctor_get_uint8(v_a_5186_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5186_, 1);
v___x_5193_ = l_Array_append___redArg(v_fst_4982_, v_records_5191_);
lean_dec_ref(v_records_5191_);
if (v_unlocated_5192_ == 0)
{
uint8_t v___x_5194_; uint8_t v___x_5195_; 
v___x_5194_ = lean_unbox(v_fst_4974_);
lean_dec(v_fst_4974_);
v___x_5195_ = lean_unbox(v_fst_4978_);
lean_dec(v_fst_4978_);
v___y_5148_ = v___y_5172_;
v___y_5149_ = v___x_5184_;
v_anyFailed_5150_ = v___x_5194_;
v_anyUnlocated_5151_ = v___x_5195_;
v_records_5152_ = v___x_5193_;
v_codeQualityEntries_5153_ = v_fst_4986_;
goto v___jp_5147_;
}
else
{
uint8_t v___x_5196_; 
lean_dec(v_fst_4978_);
v___x_5196_ = lean_unbox(v_fst_4974_);
lean_dec(v_fst_4974_);
v___y_5148_ = v___y_5172_;
v___y_5149_ = v___x_5184_;
v_anyFailed_5150_ = v___x_5196_;
v_anyUnlocated_5151_ = v_anyUnlocated_4956_;
v_records_5152_ = v___x_5193_;
v_codeQualityEntries_5153_ = v_fst_4986_;
goto v___jp_5147_;
}
}
default: 
{
lean_object* v_entries_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; uint8_t v___x_5200_; 
v_entries_5197_ = lean_ctor_get(v_a_5186_, 0);
lean_inc_ref(v_entries_5197_);
lean_dec_ref_known(v_a_5186_, 1);
v___x_5198_ = l_Array_append___redArg(v_fst_4986_, v_entries_5197_);
lean_dec_ref(v_entries_5197_);
v___x_5199_ = lean_unbox(v_fst_4974_);
lean_dec(v_fst_4974_);
v___x_5200_ = lean_unbox(v_fst_4978_);
lean_dec(v_fst_4978_);
v___y_5148_ = v___y_5172_;
v___y_5149_ = v___x_5184_;
v_anyFailed_5150_ = v___x_5199_;
v_anyUnlocated_5151_ = v___x_5200_;
v_records_5152_ = v_fst_4982_;
v_codeQualityEntries_5153_ = v___x_5198_;
goto v___jp_5147_;
}
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
lean_dec_ref(v___x_5184_);
lean_dec_ref(v___y_5172_);
lean_del_object(v___x_4993_);
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_del_object(v___x_4988_);
lean_dec(v_fst_4986_);
lean_del_object(v___x_4984_);
lean_dec(v_fst_4982_);
lean_del_object(v___x_4980_);
lean_dec(v_fst_4978_);
lean_del_object(v___x_4976_);
lean_dec(v_fst_4974_);
lean_dec(v___x_4943_);
v_a_5201_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5203_ = v___x_5185_;
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5185_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5204_ == 0)
{
v___x_5206_ = v___x_5203_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
}
}
v___jp_5212_:
{
lean_object* v___x_5214_; 
v___x_5214_ = lean_compacted_region_free(v_snd_4968_);
if (lean_obj_tag(v___x_5214_) == 0)
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; uint32_t v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_dec_ref_known(v___x_5214_, 1);
lean_inc(v_a_4962_);
v___x_5215_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5215_, 0, v_a_4962_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*1, v_anyFailed_4955_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*1 + 1, v_anyUnlocated_4956_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*1 + 2, v_anyFailed_4955_);
v___x_5216_ = lean_unsigned_to_nat(2u);
v___x_5217_ = lean_mk_empty_array_with_capacity(v___x_5216_);
v___x_5218_ = lean_array_push(v___x_5217_, v___x_5215_);
v___x_5219_ = lean_array_push(v___x_5218_, v_envLinterModule_4958_);
v___x_5220_ = l_Array_append___redArg(v___x_5219_, v_checkImports_4941_);
v___x_5221_ = l_Lean_Options_empty;
v___x_5222_ = 1024;
v___x_5223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5224_ = lean_box(1);
v___x_5225_ = l_Lean_importModules(v___x_5220_, v___x_5221_, v___x_5222_, v___x_5223_, v_anyFailed_4955_, v_anyUnlocated_4956_, v___y_5213_, v___x_5224_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v_linterOverrides_5227_; lean_object* v___x_5228_; uint8_t v___x_5229_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v_linterOverrides_5227_ = lean_ctor_get(v_args_4942_, 0);
v___x_5228_ = lean_array_get_size(v_linterOverrides_5227_);
v___x_5229_ = lean_nat_dec_lt(v___x_4954_, v___x_5228_);
if (v___x_5229_ == 0)
{
v___y_5172_ = v_a_5226_;
v___y_5173_ = v___x_5221_;
goto v___jp_5171_;
}
else
{
uint8_t v___x_5230_; 
v___x_5230_ = lean_nat_dec_le(v___x_5228_, v___x_5228_);
if (v___x_5230_ == 0)
{
if (v___x_5229_ == 0)
{
v___y_5172_ = v_a_5226_;
v___y_5173_ = v___x_5221_;
goto v___jp_5171_;
}
else
{
size_t v___x_5231_; size_t v___x_5232_; lean_object* v___x_5233_; 
v___x_5231_ = ((size_t)0ULL);
v___x_5232_ = lean_usize_of_nat(v___x_5228_);
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5227_, v___x_5231_, v___x_5232_, v___x_5221_);
v___y_5172_ = v_a_5226_;
v___y_5173_ = v___x_5233_;
goto v___jp_5171_;
}
}
else
{
size_t v___x_5234_; size_t v___x_5235_; lean_object* v___x_5236_; 
v___x_5234_ = ((size_t)0ULL);
v___x_5235_ = lean_usize_of_nat(v___x_5228_);
v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5227_, v___x_5234_, v___x_5235_, v___x_5221_);
v___y_5172_ = v_a_5226_;
v___y_5173_ = v___x_5236_;
goto v___jp_5171_;
}
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_del_object(v___x_4993_);
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_del_object(v___x_4988_);
lean_dec(v_fst_4986_);
lean_del_object(v___x_4984_);
lean_dec(v_fst_4982_);
lean_del_object(v___x_4980_);
lean_dec(v_fst_4978_);
lean_del_object(v___x_4976_);
lean_dec(v_fst_4974_);
lean_dec(v___x_4943_);
v_a_5237_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5225_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5225_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_del_object(v___x_4993_);
lean_dec(v_snd_4991_);
lean_dec(v_fst_4990_);
lean_del_object(v___x_4988_);
lean_dec(v_fst_4986_);
lean_del_object(v___x_4984_);
lean_dec(v_fst_4982_);
lean_del_object(v___x_4980_);
lean_dec(v_fst_4978_);
lean_del_object(v___x_4976_);
lean_dec(v_fst_4974_);
lean_dec_ref_known(v_envLinterModule_4958_, 1);
lean_dec(v___x_4943_);
v_a_5245_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5214_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5214_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
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
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5271_; 
lean_dec_ref_known(v_envLinterModule_4958_, 1);
lean_dec_ref(v_b_4947_);
lean_dec(v___x_4943_);
v_a_5264_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5266_ = v___x_4965_;
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_4965_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5269_; 
if (v_isShared_5267_ == 0)
{
v___x_5269_ = v___x_5266_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_a_5264_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_dec_ref_known(v_envLinterModule_4958_, 1);
lean_dec_ref(v_b_4947_);
lean_dec(v___x_4943_);
v_a_5272_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_4963_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_4963_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
v___jp_4949_:
{
size_t v___x_4951_; size_t v___x_4952_; 
v___x_4951_ = ((size_t)1ULL);
v___x_4952_ = lean_usize_add(v_i_4946_, v___x_4951_);
v_i_4946_ = v___x_4952_;
v_b_4947_ = v_a_4950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5280_, lean_object* v_checkImports_5281_, lean_object* v_args_5282_, lean_object* v___x_5283_, lean_object* v_as_5284_, lean_object* v_sz_5285_, lean_object* v_i_5286_, lean_object* v_b_5287_, lean_object* v___y_5288_){
_start:
{
size_t v_sz_boxed_5289_; size_t v_i_boxed_5290_; lean_object* v_res_5291_; 
v_sz_boxed_5289_ = lean_unbox_usize(v_sz_5285_);
lean_dec(v_sz_5285_);
v_i_boxed_5290_ = lean_unbox_usize(v_i_5286_);
lean_dec(v_i_5286_);
v_res_5291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5280_, v_checkImports_5281_, v_args_5282_, v___x_5283_, v_as_5284_, v_sz_boxed_5289_, v_i_boxed_5290_, v_b_5287_);
lean_dec_ref(v_as_5284_);
lean_dec_ref(v_args_5282_);
lean_dec_ref(v_checkImports_5281_);
lean_dec(v___x_5280_);
return v_res_5291_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5292_ = l_Lean_NameSet_empty;
v___x_5293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
lean_ctor_set(v___x_5293_, 1, v___x_5292_);
return v___x_5293_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5295_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
lean_ctor_set(v___x_5296_, 1, v___x_5294_);
return v___x_5296_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5297_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5298_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5298_);
lean_ctor_set(v___x_5299_, 1, v___x_5297_);
return v___x_5299_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5301_; lean_object* v___x_5302_; 
v___x_5301_ = 0;
v___x_5302_ = lean_box_uint32(v___x_5301_);
return v___x_5302_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = 1;
v___x_5304_ = lean_box_uint32(v___x_5303_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5305_){
_start:
{
lean_object* v_mods_5307_; uint8_t v_mode_5308_; lean_object* v_checks_5309_; lean_object* v_srcSearchPath_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; uint8_t v_anyFailed_5313_; 
v_mods_5307_ = lean_ctor_get(v_args_5305_, 1);
lean_inc_ref(v_mods_5307_);
v_mode_5308_ = lean_ctor_get_uint8(v_args_5305_, sizeof(void*)*4 + 1);
v_checks_5309_ = lean_ctor_get(v_args_5305_, 2);
v_srcSearchPath_5310_ = lean_ctor_get(v_args_5305_, 3);
v___x_5311_ = lean_array_get_size(v_mods_5307_);
v___x_5312_ = lean_unsigned_to_nat(0u);
v_anyFailed_5313_ = lean_nat_dec_eq(v___x_5311_, v___x_5312_);
if (v_anyFailed_5313_ == 0)
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v_a_5315_; size_t v_sz_5316_; size_t v___x_5317_; lean_object* v_checkImports_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; size_t v_sz_5325_; lean_object* v___x_5326_; 
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
lean_inc(v_a_5315_);
lean_dec_ref_known(v___x_5314_, 1);
v_sz_5316_ = lean_array_size(v_checks_5309_);
v___x_5317_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5309_);
v_checkImports_5318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5311_, v_sz_5316_, v___x_5317_, v_checks_5309_);
lean_inc(v_srcSearchPath_5310_);
v___x_5319_ = l_List_appendTR___redArg(v_srcSearchPath_5310_, v_a_5315_);
v___x_5320_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5321_ = lean_box(v_anyFailed_5313_);
v___x_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5321_);
lean_ctor_set(v___x_5322_, 1, v___x_5320_);
v___x_5323_ = lean_box(v_anyFailed_5313_);
v___x_5324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5323_);
lean_ctor_set(v___x_5324_, 1, v___x_5322_);
v_sz_5325_ = lean_array_size(v_mods_5307_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5311_, v_checkImports_5318_, v_args_5305_, v___x_5319_, v_mods_5307_, v_sz_5325_, v___x_5317_, v___x_5324_);
lean_dec_ref(v_mods_5307_);
lean_dec_ref(v_args_5305_);
lean_dec_ref(v_checkImports_5318_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5398_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5398_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5398_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
switch(v_mode_5308_)
{
case 0:
{
lean_object* v_fst_5331_; uint8_t v___x_5332_; 
v_fst_5331_ = lean_ctor_get(v_a_5327_, 0);
lean_inc(v_fst_5331_);
lean_dec(v_a_5327_);
v___x_5332_ = lean_unbox(v_fst_5331_);
lean_dec(v_fst_5331_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5333_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5333_);
v___x_5335_ = v___x_5329_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
else
{
lean_object* v___x_5337_; lean_object* v___x_5339_; 
v___x_5337_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5337_);
v___x_5339_ = v___x_5329_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5337_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
case 1:
{
lean_object* v_snd_5341_; lean_object* v_snd_5342_; lean_object* v_fst_5343_; lean_object* v_fst_5344_; lean_object* v___x_5345_; 
v_snd_5341_ = lean_ctor_get(v_a_5327_, 1);
lean_inc(v_snd_5341_);
lean_del_object(v___x_5329_);
lean_dec(v_a_5327_);
v_snd_5342_ = lean_ctor_get(v_snd_5341_, 1);
lean_inc(v_snd_5342_);
v_fst_5343_ = lean_ctor_get(v_snd_5341_, 0);
lean_inc(v_fst_5343_);
lean_dec(v_snd_5341_);
v_fst_5344_ = lean_ctor_get(v_snd_5342_, 0);
lean_inc(v_fst_5344_);
lean_dec(v_snd_5342_);
v___x_5345_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5344_);
lean_dec(v_fst_5344_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5358_; 
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5358_ == 0)
{
lean_object* v_unused_5359_; 
v_unused_5359_ = lean_ctor_get(v___x_5345_, 0);
lean_dec(v_unused_5359_);
v___x_5347_ = v___x_5345_;
v_isShared_5348_ = v_isSharedCheck_5358_;
goto v_resetjp_5346_;
}
else
{
lean_dec(v___x_5345_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5358_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
uint8_t v___x_5349_; 
v___x_5349_ = lean_unbox(v_fst_5343_);
lean_dec(v_fst_5343_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; lean_object* v___x_5352_; 
v___x_5350_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5350_);
v___x_5352_ = v___x_5347_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5350_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
else
{
lean_object* v___x_5354_; lean_object* v___x_5356_; 
v___x_5354_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5354_);
v___x_5356_ = v___x_5347_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_fst_5343_);
v_a_5360_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5345_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5345_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
default: 
{
lean_object* v_snd_5368_; lean_object* v_snd_5369_; lean_object* v_snd_5370_; lean_object* v_fst_5371_; lean_object* v_fst_5372_; lean_object* v___x_5373_; size_t v_sz_5374_; lean_object* v___x_5375_; 
v_snd_5368_ = lean_ctor_get(v_a_5327_, 1);
lean_del_object(v___x_5329_);
v_snd_5369_ = lean_ctor_get(v_snd_5368_, 1);
v_snd_5370_ = lean_ctor_get(v_snd_5369_, 1);
lean_inc(v_snd_5370_);
v_fst_5371_ = lean_ctor_get(v_a_5327_, 0);
lean_inc(v_fst_5371_);
lean_dec(v_a_5327_);
v_fst_5372_ = lean_ctor_get(v_snd_5370_, 0);
lean_inc(v_fst_5372_);
lean_dec(v_snd_5370_);
v___x_5373_ = lean_box(0);
v_sz_5374_ = lean_array_size(v_fst_5372_);
v___x_5375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5372_, v_sz_5374_, v___x_5317_, v___x_5373_);
lean_dec(v_fst_5372_);
if (lean_obj_tag(v___x_5375_) == 0)
{
lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5388_; 
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5388_ == 0)
{
lean_object* v_unused_5389_; 
v_unused_5389_ = lean_ctor_get(v___x_5375_, 0);
lean_dec(v_unused_5389_);
v___x_5377_ = v___x_5375_;
v_isShared_5378_ = v_isSharedCheck_5388_;
goto v_resetjp_5376_;
}
else
{
lean_dec(v___x_5375_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5388_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
uint8_t v___x_5379_; 
v___x_5379_ = lean_unbox(v_fst_5371_);
lean_dec(v_fst_5371_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
v___x_5380_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5380_);
v___x_5382_ = v___x_5377_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
else
{
lean_object* v___x_5384_; lean_object* v___x_5386_; 
v___x_5384_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5384_);
v___x_5386_ = v___x_5377_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5384_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
lean_dec(v_fst_5371_);
v_a_5390_ = lean_ctor_get(v___x_5375_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5375_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5375_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5393_ == 0)
{
v___x_5395_ = v___x_5392_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_a_5390_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
return v___x_5395_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5406_; 
v_a_5399_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5401_ = v___x_5326_;
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5326_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5404_; 
if (v_isShared_5402_ == 0)
{
v___x_5404_ = v___x_5401_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
lean_dec_ref(v_mods_5307_);
lean_dec_ref(v_args_5305_);
v_a_5407_ = lean_ctor_get(v___x_5314_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5314_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5314_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v___x_5415_; lean_object* v___x_5416_; 
lean_dec_ref(v_mods_5307_);
lean_dec_ref(v_args_5305_);
v___x_5415_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5416_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5415_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5424_; 
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5424_ == 0)
{
lean_object* v_unused_5425_; 
v_unused_5425_ = lean_ctor_get(v___x_5416_, 0);
lean_dec(v_unused_5425_);
v___x_5418_ = v___x_5416_;
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
else
{
lean_dec(v___x_5416_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5420_; lean_object* v___x_5422_; 
v___x_5420_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 0, v___x_5420_);
v___x_5422_ = v___x_5418_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
v_a_5426_ = lean_ctor_get(v___x_5416_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5416_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5416_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5434_, lean_object* v_a_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Lake_BuiltinLint_run(v_args_5434_);
return v_res_5436_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
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
lean_object* initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin);
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
res = initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
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
