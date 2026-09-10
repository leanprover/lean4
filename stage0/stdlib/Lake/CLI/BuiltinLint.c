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
uint8_t v___y_7063__boxed_2030_; uint8_t v_res_2031_; lean_object* v_r_2032_; 
v___y_7063__boxed_2030_ = lean_unbox(v___y_2028_);
v_res_2031_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2026_, v_docCheckedModules_2027_, v___y_7063__boxed_2030_, v_m_2029_);
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
v_ref_2094_ = lean_ctor_get(v___y_2046_, 2);
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
v_ref_2139_ = lean_ctor_get(v___y_2046_, 2);
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
v_ref_2164_ = lean_ctor_get(v___y_2046_, 2);
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
uint8_t v___x_7087__boxed_2198_; size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v___x_7087__boxed_2198_ = lean_unbox(v___x_2189_);
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_7087__boxed_2198_, v_sp_2190_, v_as_2191_, v_sz_boxed_2199_, v_i_boxed_2200_, v_b_2194_, v___y_2195_, v___y_2196_);
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
v_ref_2256_ = lean_ctor_get(v___y_2214_, 2);
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
v_ref_2285_ = lean_ctor_get(v___y_2214_, 2);
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
v_ref_2303_ = lean_ctor_get(v___y_2214_, 2);
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
uint8_t v___y_7379__boxed_2332_; size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v___y_7379__boxed_2332_ = lean_unbox(v___y_2325_);
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2324_, v___y_7379__boxed_2332_, v_as_2326_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2329_, v___y_2330_);
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
lean_object* v___y_2419_; lean_object* v_a_2420_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2449_; lean_object* v_a_2453_; uint8_t v___y_2457_; lean_object* v_a_2458_; uint8_t v_lintOnly_2474_; uint8_t v_mode_2475_; lean_object* v___f_2476_; lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v_fileName_2485_; lean_object* v_fileMap_2486_; lean_object* v_currNamespace_2487_; lean_object* v_openDecls_2488_; lean_object* v_initHeartbeats_2489_; lean_object* v_maxHeartbeats_2490_; lean_object* v_quotContext_2491_; lean_object* v_currMacroScope_2492_; lean_object* v_cancelTk_x3f_2493_; lean_object* v_inheritedTraceOptions_2494_; lean_object* v_currRecDepth_2495_; lean_object* v_ref_2496_; uint8_t v_suppressElabErrors_2497_; lean_object* v___y_2498_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2530_; uint8_t v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; uint8_t v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; uint8_t v___y_2561_; uint8_t v___y_2582_; 
v_lintOnly_2474_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4);
v_mode_2475_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4 + 1);
v___f_2476_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2474_ == 0)
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = l_Lean_linter_doc_deferred;
v___x_2622_ = l_Lean_Linter_getLinterValue(v___x_2621_, v_linterOpts_2412_);
v___y_2582_ = v___x_2622_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2623_; lean_object* v_name_2624_; uint8_t v___x_2625_; 
v___x_2623_ = l_Lean_linter_doc_deferred;
v_name_2624_ = lean_ctor_get(v___x_2623_, 0);
v___x_2625_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2624_, v_linterOpts_2412_);
v___y_2582_ = v___x_2625_;
goto v___jp_2581_;
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
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2499_ = l_Lean_maxRecDepth;
v___x_2500_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2482_, v___x_2499_);
lean_inc_ref(v___y_2482_);
v___x_2501_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2501_, 0, v_fileName_2485_);
lean_ctor_set(v___x_2501_, 1, v_fileMap_2486_);
lean_ctor_set(v___x_2501_, 2, v___y_2482_);
lean_ctor_set(v___x_2501_, 3, v___x_2500_);
lean_ctor_set(v___x_2501_, 4, v_currNamespace_2487_);
lean_ctor_set(v___x_2501_, 5, v_openDecls_2488_);
lean_ctor_set(v___x_2501_, 6, v_initHeartbeats_2489_);
lean_ctor_set(v___x_2501_, 7, v_maxHeartbeats_2490_);
lean_ctor_set(v___x_2501_, 8, v_quotContext_2491_);
lean_ctor_set(v___x_2501_, 9, v_currMacroScope_2492_);
lean_ctor_set(v___x_2501_, 10, v_cancelTk_x3f_2493_);
lean_ctor_set(v___x_2501_, 11, v_inheritedTraceOptions_2494_);
v___x_2502_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v_currRecDepth_2495_);
lean_ctor_set(v___x_2502_, 2, v_ref_2496_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*3, v___y_2484_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*3 + 1, v_suppressElabErrors_2497_);
v___x_2503_ = l_Lean_Doc_DeferredCheck_run(v___y_2483_, v___f_2476_, v___x_2502_, v___y_2498_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; uint8_t v___x_2505_; uint8_t v___x_2506_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = 1;
v___x_2506_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v___y_2498_);
v___x_2507_ = lean_box(0);
v_sz_2508_ = lean_array_size(v_a_2504_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2413_, v___y_2481_, v_a_2504_, v_sz_2508_, v___x_2509_, v___x_2507_, v___x_2502_);
lean_dec_ref_known(v___x_2502_, 3);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
lean_dec_ref_known(v___x_2510_, 1);
v___x_2511_ = lean_array_get_size(v_a_2504_);
lean_dec(v_a_2504_);
v___x_2512_ = lean_nat_dec_eq(v___x_2511_, v___y_2478_);
lean_dec(v___y_2478_);
if (v___x_2512_ == 0)
{
v___y_2445_ = v___y_2479_;
v___y_2446_ = v___y_2481_;
goto v___jp_2444_;
}
else
{
v___y_2445_ = v___y_2479_;
v___y_2446_ = v___x_2506_;
goto v___jp_2444_;
}
}
else
{
lean_object* v_a_2513_; 
lean_dec(v_a_2504_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2513_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2510_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2513_;
goto v___jp_2456_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; size_t v_sz_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2514_ = lean_mk_empty_array_with_capacity(v___y_2478_);
lean_dec(v___y_2478_);
v___x_2515_ = lean_box(v___y_2480_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v_sz_2517_ = lean_array_size(v_a_2504_);
v___x_2518_ = ((size_t)0ULL);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2506_, v_sp_2413_, v_a_2504_, v_sz_2517_, v___x_2518_, v___x_2516_, v___x_2502_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref_known(v___x_2502_, 3);
lean_dec(v_a_2504_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v_fst_2521_; lean_object* v_snd_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_fst_2521_ = lean_ctor_get(v_a_2520_, 0);
lean_inc(v_fst_2521_);
v_snd_2522_ = lean_ctor_get(v_a_2520_, 1);
lean_inc(v_snd_2522_);
lean_dec(v_a_2520_);
v___x_2523_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2523_, 0, v_fst_2521_);
v___x_2524_ = lean_unbox(v_snd_2522_);
lean_dec(v_snd_2522_);
lean_ctor_set_uint8(v___x_2523_, sizeof(void*)*1, v___x_2524_);
v___y_2419_ = v___y_2479_;
v_a_2420_ = v___x_2523_;
goto v___jp_2418_;
}
else
{
lean_object* v_a_2525_; 
lean_dec(v___y_2479_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2525_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2519_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2525_;
goto v___jp_2456_;
}
}
}
else
{
lean_object* v_a_2526_; 
lean_dec_ref_known(v___x_2502_, 3);
lean_dec(v___y_2498_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v_a_2526_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2503_, 1);
v___y_2457_ = v___y_2481_;
v_a_2458_ = v_a_2526_;
goto v___jp_2456_;
}
}
v___jp_2527_:
{
lean_object* v_toCold_2537_; lean_object* v_currRecDepth_2538_; lean_object* v_ref_2539_; uint8_t v_suppressElabErrors_2540_; lean_object* v_fileName_2541_; lean_object* v_fileMap_2542_; lean_object* v_currNamespace_2543_; lean_object* v_openDecls_2544_; lean_object* v_initHeartbeats_2545_; lean_object* v_maxHeartbeats_2546_; lean_object* v_quotContext_2547_; lean_object* v_currMacroScope_2548_; lean_object* v_cancelTk_x3f_2549_; lean_object* v_inheritedTraceOptions_2550_; 
v_toCold_2537_ = lean_ctor_get(v___y_2535_, 0);
lean_inc_ref(v_toCold_2537_);
v_currRecDepth_2538_ = lean_ctor_get(v___y_2535_, 1);
lean_inc(v_currRecDepth_2538_);
v_ref_2539_ = lean_ctor_get(v___y_2535_, 2);
lean_inc(v_ref_2539_);
v_suppressElabErrors_2540_ = lean_ctor_get_uint8(v___y_2535_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_2535_);
v_fileName_2541_ = lean_ctor_get(v_toCold_2537_, 0);
lean_inc_ref(v_fileName_2541_);
v_fileMap_2542_ = lean_ctor_get(v_toCold_2537_, 1);
lean_inc_ref(v_fileMap_2542_);
v_currNamespace_2543_ = lean_ctor_get(v_toCold_2537_, 4);
lean_inc(v_currNamespace_2543_);
v_openDecls_2544_ = lean_ctor_get(v_toCold_2537_, 5);
lean_inc(v_openDecls_2544_);
v_initHeartbeats_2545_ = lean_ctor_get(v_toCold_2537_, 6);
lean_inc(v_initHeartbeats_2545_);
v_maxHeartbeats_2546_ = lean_ctor_get(v_toCold_2537_, 7);
lean_inc(v_maxHeartbeats_2546_);
v_quotContext_2547_ = lean_ctor_get(v_toCold_2537_, 8);
lean_inc(v_quotContext_2547_);
v_currMacroScope_2548_ = lean_ctor_get(v_toCold_2537_, 9);
lean_inc(v_currMacroScope_2548_);
v_cancelTk_x3f_2549_ = lean_ctor_get(v_toCold_2537_, 10);
lean_inc(v_cancelTk_x3f_2549_);
v_inheritedTraceOptions_2550_ = lean_ctor_get(v_toCold_2537_, 11);
lean_inc_ref(v_inheritedTraceOptions_2550_);
lean_dec_ref(v_toCold_2537_);
v___y_2478_ = v___y_2528_;
v___y_2479_ = v___y_2529_;
v___y_2480_ = v___y_2530_;
v___y_2481_ = v___y_2531_;
v___y_2482_ = v___y_2532_;
v___y_2483_ = v___y_2533_;
v___y_2484_ = v___y_2534_;
v_fileName_2485_ = v_fileName_2541_;
v_fileMap_2486_ = v_fileMap_2542_;
v_currNamespace_2487_ = v_currNamespace_2543_;
v_openDecls_2488_ = v_openDecls_2544_;
v_initHeartbeats_2489_ = v_initHeartbeats_2545_;
v_maxHeartbeats_2490_ = v_maxHeartbeats_2546_;
v_quotContext_2491_ = v_quotContext_2547_;
v_currMacroScope_2492_ = v_currMacroScope_2548_;
v_cancelTk_x3f_2493_ = v_cancelTk_x3f_2549_;
v_inheritedTraceOptions_2494_ = v_inheritedTraceOptions_2550_;
v_currRecDepth_2495_ = v_currRecDepth_2538_;
v_ref_2496_ = v_ref_2539_;
v_suppressElabErrors_2497_ = v_suppressElabErrors_2540_;
v___y_2498_ = v___y_2536_;
goto v___jp_2477_;
}
v___jp_2551_:
{
if (v___y_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v_env_2563_; lean_object* v_nextMacroScope_2564_; lean_object* v_ngen_2565_; lean_object* v_auxDeclNGen_2566_; lean_object* v_traceState_2567_; lean_object* v_messages_2568_; lean_object* v_infoState_2569_; lean_object* v_snapshotTasks_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2579_; 
v___x_2562_ = lean_st_ref_take(v___y_2553_);
v_env_2563_ = lean_ctor_get(v___x_2562_, 0);
v_nextMacroScope_2564_ = lean_ctor_get(v___x_2562_, 1);
v_ngen_2565_ = lean_ctor_get(v___x_2562_, 2);
v_auxDeclNGen_2566_ = lean_ctor_get(v___x_2562_, 3);
v_traceState_2567_ = lean_ctor_get(v___x_2562_, 4);
v_messages_2568_ = lean_ctor_get(v___x_2562_, 6);
v_infoState_2569_ = lean_ctor_get(v___x_2562_, 7);
v_snapshotTasks_2570_ = lean_ctor_get(v___x_2562_, 8);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2562_, 5);
lean_dec(v_unused_2580_);
v___x_2572_ = v___x_2562_;
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snapshotTasks_2570_);
lean_inc(v_infoState_2569_);
lean_inc(v_messages_2568_);
lean_inc(v_traceState_2567_);
lean_inc(v_auxDeclNGen_2566_);
lean_inc(v_ngen_2565_);
lean_inc(v_nextMacroScope_2564_);
lean_inc(v_env_2563_);
lean_dec(v___x_2562_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = l_Lean_Kernel_enableDiag(v_env_2563_, v___y_2560_);
lean_inc_ref(v___y_2557_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 5, v___y_2557_);
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_nextMacroScope_2564_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_ngen_2565_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_auxDeclNGen_2566_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_traceState_2567_);
lean_ctor_set(v_reuseFailAlloc_2578_, 5, v___y_2557_);
lean_ctor_set(v_reuseFailAlloc_2578_, 6, v_messages_2568_);
lean_ctor_set(v_reuseFailAlloc_2578_, 7, v_infoState_2569_);
lean_ctor_set(v_reuseFailAlloc_2578_, 8, v_snapshotTasks_2570_);
v___x_2576_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_st_ref_put(v___y_2553_, v___x_2576_);
lean_inc(v___y_2553_);
v___y_2528_ = v___y_2552_;
v___y_2529_ = v___y_2553_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2558_;
v___y_2533_ = v___y_2559_;
v___y_2534_ = v___y_2560_;
v___y_2535_ = v___y_2556_;
v___y_2536_ = v___y_2553_;
goto v___jp_2527_;
}
}
}
else
{
lean_inc(v___y_2553_);
v___y_2528_ = v___y_2552_;
v___y_2529_ = v___y_2553_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2558_;
v___y_2533_ = v___y_2559_;
v___y_2534_ = v___y_2560_;
v___y_2535_ = v___y_2556_;
v___y_2536_ = v___y_2553_;
goto v___jp_2527_;
}
}
v___jp_2581_:
{
if (v___y_2582_ == 0)
{
uint8_t v___x_2583_; uint8_t v___x_2584_; 
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v___x_2583_ = 1;
v___x_2584_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2585_, 0, v___x_2584_);
v___y_2449_ = v___x_2585_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2587_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*1, v___y_2582_);
v___y_2449_ = v___x_2587_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v_env_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; uint8_t v___x_2619_; uint8_t v___x_2620_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2590_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2591_ = lean_io_get_num_heartbeats();
v___x_2592_ = l_Lean_firstFrontendMacroScope;
v___x_2593_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2594_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_box(0);
v___x_2597_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2598_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2599_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2600_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2414_);
v___x_2601_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2601_, 0, v_env_2414_);
lean_ctor_set(v___x_2601_, 1, v___x_2593_);
lean_ctor_set(v___x_2601_, 2, v___x_2594_);
lean_ctor_set(v___x_2601_, 3, v___x_2597_);
lean_ctor_set(v___x_2601_, 4, v___x_2598_);
lean_ctor_set(v___x_2601_, 5, v___x_2589_);
lean_ctor_set(v___x_2601_, 6, v___x_2590_);
lean_ctor_set(v___x_2601_, 7, v___x_2599_);
lean_ctor_set(v___x_2601_, 8, v___x_2600_);
v___x_2602_ = lean_st_mk_ref(v___x_2601_);
v___x_2603_ = l_Lean_inheritedTraceOptions;
v___x_2604_ = lean_st_ref_get(v___x_2603_);
v___x_2605_ = lean_st_ref_get(v___x_2602_);
v___x_2606_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2607_ = l_Lean_instInhabitedFileMap_default;
v___x_2608_ = l_Lean_Options_empty;
v___x_2609_ = lean_unsigned_to_nat(1000u);
v___x_2610_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_box(0);
v___x_2613_ = 0;
lean_inc(v___x_2604_);
lean_inc(v___x_2591_);
v___x_2614_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2606_);
lean_ctor_set(v___x_2614_, 1, v___x_2607_);
lean_ctor_set(v___x_2614_, 2, v___x_2608_);
lean_ctor_set(v___x_2614_, 3, v___x_2609_);
lean_ctor_set(v___x_2614_, 4, v___x_2595_);
lean_ctor_set(v___x_2614_, 5, v___x_2596_);
lean_ctor_set(v___x_2614_, 6, v___x_2591_);
lean_ctor_set(v___x_2614_, 7, v___x_2610_);
lean_ctor_set(v___x_2614_, 8, v___x_2595_);
lean_ctor_set(v___x_2614_, 9, v___x_2592_);
lean_ctor_set(v___x_2614_, 10, v___x_2611_);
lean_ctor_set(v___x_2614_, 11, v___x_2604_);
v___x_2615_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2588_);
lean_ctor_set(v___x_2615_, 2, v___x_2612_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*3, v___x_2613_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*3 + 1, v___x_2613_);
v_env_2616_ = lean_ctor_get(v___x_2605_, 0);
lean_inc_ref(v_env_2616_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_box(v___y_2582_);
lean_inc(v_docCheckedModules_2416_);
lean_inc(v_pkgRoot_2415_);
v___f_2618_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2618_, 0, v_pkgRoot_2415_);
lean_closure_set(v___f_2618_, 1, v_docCheckedModules_2416_);
lean_closure_set(v___f_2618_, 2, v___x_2617_);
v___x_2619_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2620_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2616_);
lean_dec_ref(v_env_2616_);
if (v___x_2619_ == 0)
{
if (v___x_2620_ == 0)
{
lean_dec_ref_known(v___x_2615_, 3);
lean_inc(v___x_2602_);
v___y_2478_ = v___x_2588_;
v___y_2479_ = v___x_2602_;
v___y_2480_ = v___x_2613_;
v___y_2481_ = v___y_2582_;
v___y_2482_ = v___x_2608_;
v___y_2483_ = v___f_2618_;
v___y_2484_ = v___x_2619_;
v_fileName_2485_ = v___x_2606_;
v_fileMap_2486_ = v___x_2607_;
v_currNamespace_2487_ = v___x_2595_;
v_openDecls_2488_ = v___x_2596_;
v_initHeartbeats_2489_ = v___x_2591_;
v_maxHeartbeats_2490_ = v___x_2610_;
v_quotContext_2491_ = v___x_2595_;
v_currMacroScope_2492_ = v___x_2592_;
v_cancelTk_x3f_2493_ = v___x_2611_;
v_inheritedTraceOptions_2494_ = v___x_2604_;
v_currRecDepth_2495_ = v___x_2588_;
v_ref_2496_ = v___x_2612_;
v_suppressElabErrors_2497_ = v___x_2613_;
v___y_2498_ = v___x_2602_;
goto v___jp_2477_;
}
else
{
lean_dec(v___x_2604_);
lean_dec(v___x_2591_);
v___y_2552_ = v___x_2588_;
v___y_2553_ = v___x_2602_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___x_2613_;
v___y_2556_ = v___x_2615_;
v___y_2557_ = v___x_2589_;
v___y_2558_ = v___x_2608_;
v___y_2559_ = v___f_2618_;
v___y_2560_ = v___x_2619_;
v___y_2561_ = v___x_2619_;
goto v___jp_2551_;
}
}
else
{
lean_dec(v___x_2604_);
lean_dec(v___x_2591_);
v___y_2552_ = v___x_2588_;
v___y_2553_ = v___x_2602_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___x_2613_;
v___y_2556_ = v___x_2615_;
v___y_2557_ = v___x_2589_;
v___y_2558_ = v___x_2608_;
v___y_2559_ = v___f_2618_;
v___y_2560_ = v___x_2619_;
v___y_2561_ = v___x_2620_;
goto v___jp_2551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2626_, lean_object* v_linterOpts_2627_, lean_object* v_sp_2628_, lean_object* v_env_2629_, lean_object* v_pkgRoot_2630_, lean_object* v_docCheckedModules_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2626_, v_linterOpts_2627_, v_sp_2628_, v_env_2629_, v_pkgRoot_2630_, v_docCheckedModules_2631_);
lean_dec_ref(v_linterOpts_2627_);
lean_dec_ref(v_args_2626_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2634_, uint8_t v___y_2635_, lean_object* v_as_2636_, size_t v_sz_2637_, size_t v_i_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2634_, v___y_2635_, v_as_2636_, v_sz_2637_, v_i_2638_, v_b_2639_, v___y_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2644_, lean_object* v___y_2645_, lean_object* v_as_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v___y_8112__boxed_2653_; size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v___y_8112__boxed_2653_ = lean_unbox(v___y_2645_);
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2644_, v___y_8112__boxed_2653_, v_as_2646_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v_as_2646_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2657_, lean_object* v_as_2658_, size_t v_i_2659_, size_t v_stop_2660_, lean_object* v_b_2661_){
_start:
{
lean_object* v___y_2663_; uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_eq(v_i_2659_, v_stop_2660_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v_linter_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_array_uget_borrowed(v_as_2658_, v_i_2659_);
v_linter_2669_ = lean_ctor_get(v___x_2668_, 0);
v___x_2670_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2669_, v_linterOpts_2657_);
if (v___x_2670_ == 0)
{
v___y_2663_ = v_b_2661_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2671_; 
lean_inc(v___x_2668_);
v___x_2671_ = lean_array_push(v_b_2661_, v___x_2668_);
v___y_2663_ = v___x_2671_;
goto v___jp_2662_;
}
}
else
{
return v_b_2661_;
}
v___jp_2662_:
{
size_t v___x_2664_; size_t v___x_2665_; 
v___x_2664_ = ((size_t)1ULL);
v___x_2665_ = lean_usize_add(v_i_2659_, v___x_2664_);
v_i_2659_ = v___x_2665_;
v_b_2661_ = v___y_2663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2672_, lean_object* v_as_2673_, lean_object* v_i_2674_, lean_object* v_stop_2675_, lean_object* v_b_2676_){
_start:
{
size_t v_i_boxed_2677_; size_t v_stop_boxed_2678_; lean_object* v_res_2679_; 
v_i_boxed_2677_ = lean_unbox_usize(v_i_2674_);
lean_dec(v_i_2674_);
v_stop_boxed_2678_ = lean_unbox_usize(v_stop_2675_);
lean_dec(v_stop_2675_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2672_, v_as_2673_, v_i_boxed_2677_, v_stop_boxed_2678_, v_b_2676_);
lean_dec_ref(v_as_2673_);
lean_dec_ref(v_linterOpts_2672_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2682_, lean_object* v_as_2683_, size_t v_i_2684_, size_t v_stop_2685_, lean_object* v_b_2686_){
_start:
{
lean_object* v___y_2688_; uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_eq(v_i_2684_, v_stop_2685_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2719_; 
v___x_2693_ = lean_array_uget(v_as_2683_, v_i_2684_);
v_fst_2694_ = lean_ctor_get(v___x_2693_, 0);
v_snd_2695_ = lean_ctor_get(v___x_2693_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2697_ = v___x_2693_;
v_isShared_2698_ = v_isSharedCheck_2719_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_inc(v_fst_2694_);
lean_dec(v___x_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2719_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___y_2700_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_array_get_size(v_snd_2695_);
v___x_2710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2711_ = lean_nat_dec_lt(v___x_2708_, v___x_2709_);
if (v___x_2711_ == 0)
{
lean_dec(v_snd_2695_);
v___y_2700_ = v___x_2710_;
goto v___jp_2699_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_nat_dec_le(v___x_2709_, v___x_2709_);
if (v___x_2712_ == 0)
{
if (v___x_2711_ == 0)
{
lean_dec(v_snd_2695_);
v___y_2700_ = v___x_2710_;
goto v___jp_2699_;
}
else
{
size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((size_t)0ULL);
v___x_2714_ = lean_usize_of_nat(v___x_2709_);
v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2682_, v_snd_2695_, v___x_2713_, v___x_2714_, v___x_2710_);
lean_dec(v_snd_2695_);
v___y_2700_ = v___x_2715_;
goto v___jp_2699_;
}
}
else
{
size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = lean_usize_of_nat(v___x_2709_);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2682_, v_snd_2695_, v___x_2716_, v___x_2717_, v___x_2710_);
lean_dec(v_snd_2695_);
v___y_2700_ = v___x_2718_;
goto v___jp_2699_;
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_array_get_size(v___y_2700_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_nat_dec_eq(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___y_2700_);
v___x_2705_ = v___x_2697_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_fst_2694_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___y_2700_);
v___x_2705_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_array_push(v_b_2686_, v___x_2705_);
v___y_2688_ = v___x_2706_;
goto v___jp_2687_;
}
}
else
{
lean_dec_ref(v___y_2700_);
lean_del_object(v___x_2697_);
lean_dec(v_fst_2694_);
v___y_2688_ = v_b_2686_;
goto v___jp_2687_;
}
}
}
}
else
{
return v_b_2686_;
}
v___jp_2687_:
{
size_t v___x_2689_; size_t v___x_2690_; 
v___x_2689_ = ((size_t)1ULL);
v___x_2690_ = lean_usize_add(v_i_2684_, v___x_2689_);
v_i_2684_ = v___x_2690_;
v_b_2686_ = v___y_2688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2720_, lean_object* v_as_2721_, lean_object* v_i_2722_, lean_object* v_stop_2723_, lean_object* v_b_2724_){
_start:
{
size_t v_i_boxed_2725_; size_t v_stop_boxed_2726_; lean_object* v_res_2727_; 
v_i_boxed_2725_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_stop_boxed_2726_ = lean_unbox_usize(v_stop_2723_);
lean_dec(v_stop_2723_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2720_, v_as_2721_, v_i_boxed_2725_, v_stop_boxed_2726_, v_b_2724_);
lean_dec_ref(v_as_2721_);
lean_dec_ref(v_linterOpts_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2728_, lean_object* v_as_2729_, lean_object* v_start_2730_, lean_object* v_stop_2731_){
_start:
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2733_ = lean_nat_dec_lt(v_start_2730_, v_stop_2731_);
if (v___x_2733_ == 0)
{
return v___x_2732_;
}
else
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = lean_array_get_size(v_as_2729_);
v___x_2735_ = lean_nat_dec_le(v_stop_2731_, v___x_2734_);
if (v___x_2735_ == 0)
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_nat_dec_lt(v_start_2730_, v___x_2734_);
if (v___x_2736_ == 0)
{
return v___x_2732_;
}
else
{
size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_usize_of_nat(v_start_2730_);
v___x_2738_ = lean_usize_of_nat(v___x_2734_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2728_, v_as_2729_, v___x_2737_, v___x_2738_, v___x_2732_);
return v___x_2739_;
}
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_usize_of_nat(v_start_2730_);
v___x_2741_ = lean_usize_of_nat(v_stop_2731_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2728_, v_as_2729_, v___x_2740_, v___x_2741_, v___x_2732_);
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2743_, lean_object* v_as_2744_, lean_object* v_start_2745_, lean_object* v_stop_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2743_, v_as_2744_, v_start_2745_, v_stop_2746_);
lean_dec(v_stop_2746_);
lean_dec(v_start_2745_);
lean_dec_ref(v_as_2744_);
lean_dec_ref(v_linterOpts_2743_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2748_, lean_object* v_init_2749_, lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_k_2752_; lean_object* v_v_2753_; lean_object* v_l_2754_; lean_object* v_r_2755_; lean_object* v___x_2756_; lean_object* v_a_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2772_; 
v_k_2752_ = lean_ctor_get(v_x_2750_, 1);
lean_inc(v_k_2752_);
v_v_2753_ = lean_ctor_get(v_x_2750_, 2);
lean_inc(v_v_2753_);
v_l_2754_ = lean_ctor_get(v_x_2750_, 3);
lean_inc(v_l_2754_);
v_r_2755_ = lean_ctor_get(v_x_2750_, 4);
lean_inc(v_r_2755_);
lean_dec_ref_known(v_x_2750_, 5);
lean_inc(v_fst_2748_);
v___x_2756_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2748_, v_init_2749_, v_l_2754_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v_a_2758_ = lean_ctor_get(v_a_2757_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2760_ = v_a_2757_;
v_isShared_2761_ = v_isSharedCheck_2772_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v_a_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2772_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
uint8_t v_anyUnlocated_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v_anyUnlocated_2762_ = 1;
v___x_2763_ = l_Lean_Name_toString(v_k_2752_, v_anyUnlocated_2762_);
lean_inc(v_fst_2748_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 0);
lean_ctor_set(v___x_2760_, 0, v_fst_2748_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_fst_2748_);
v___x_2765_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
double v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2766_ = lean_float_of_nat(v_v_2753_);
v___x_2767_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2763_);
lean_ctor_set(v___x_2768_, 1, v___x_2765_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
v___x_2769_ = lean_array_push(v_a_2758_, v___x_2768_);
v_init_2749_ = v___x_2769_;
v_x_2750_ = v_r_2755_;
goto _start;
}
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v_fst_2748_);
v___x_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_init_2749_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2775_, lean_object* v_init_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2775_, v_init_2776_, v_x_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2780_, lean_object* v_k_2781_, lean_object* v_fallback_2782_){
_start:
{
if (lean_obj_tag(v_t_2780_) == 0)
{
lean_object* v_k_2783_; lean_object* v_v_2784_; lean_object* v_l_2785_; lean_object* v_r_2786_; uint8_t v___x_2787_; 
v_k_2783_ = lean_ctor_get(v_t_2780_, 1);
v_v_2784_ = lean_ctor_get(v_t_2780_, 2);
v_l_2785_ = lean_ctor_get(v_t_2780_, 3);
v_r_2786_ = lean_ctor_get(v_t_2780_, 4);
v___x_2787_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2781_, v_k_2783_);
switch(v___x_2787_)
{
case 0:
{
v_t_2780_ = v_l_2785_;
goto _start;
}
case 1:
{
lean_inc(v_v_2784_);
return v_v_2784_;
}
default: 
{
v_t_2780_ = v_r_2786_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2782_);
return v_fallback_2782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2790_, lean_object* v_k_2791_, lean_object* v_fallback_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2790_, v_k_2791_, v_fallback_2792_);
lean_dec(v_fallback_2792_);
lean_dec(v_k_2791_);
lean_dec(v_t_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2794_, size_t v_i_2795_, size_t v_stop_2796_, lean_object* v_b_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_usize_dec_eq(v_i_2795_, v_stop_2796_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v_linter_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; 
v___x_2799_ = lean_array_uget_borrowed(v_as_2794_, v_i_2795_);
v_linter_2800_ = lean_ctor_get(v___x_2799_, 0);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2797_, v_linter_2800_, v___x_2801_);
v___x_2803_ = lean_unsigned_to_nat(1u);
v___x_2804_ = lean_nat_add(v___x_2802_, v___x_2803_);
lean_dec(v___x_2802_);
lean_inc(v_linter_2800_);
v___x_2805_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2800_, v___x_2804_, v_b_2797_);
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_add(v_i_2795_, v___x_2806_);
v_i_2795_ = v___x_2807_;
v_b_2797_ = v___x_2805_;
goto _start;
}
else
{
return v_b_2797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_stop_2811_, lean_object* v_b_2812_){
_start:
{
size_t v_i_boxed_2813_; size_t v_stop_boxed_2814_; lean_object* v_res_2815_; 
v_i_boxed_2813_ = lean_unbox_usize(v_i_2810_);
lean_dec(v_i_2810_);
v_stop_boxed_2814_ = lean_unbox_usize(v_stop_2811_);
lean_dec(v_stop_2811_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2809_, v_i_boxed_2813_, v_stop_boxed_2814_, v_b_2812_);
lean_dec_ref(v_as_2809_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2816_, size_t v_sz_2817_, size_t v_i_2818_, lean_object* v_b_2819_){
_start:
{
lean_object* v_a_2822_; uint8_t v___x_2826_; 
v___x_2826_ = lean_usize_dec_lt(v_i_2818_, v_sz_2817_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_b_2819_);
return v___x_2827_;
}
else
{
lean_object* v_a_2828_; lean_object* v_fst_2829_; lean_object* v_snd_2830_; lean_object* v___y_2832_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_a_2828_ = lean_array_uget_borrowed(v_as_2816_, v_i_2818_);
v_fst_2829_ = lean_ctor_get(v_a_2828_, 0);
v_snd_2830_ = lean_ctor_get(v_a_2828_, 1);
v___x_2854_ = lean_box(1);
v___x_2855_ = lean_unsigned_to_nat(0u);
v___x_2856_ = lean_array_get_size(v_snd_2830_);
v___x_2857_ = lean_nat_dec_lt(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
v___y_2832_ = v___x_2854_;
goto v___jp_2831_;
}
else
{
uint8_t v___x_2858_; 
v___x_2858_ = lean_nat_dec_le(v___x_2856_, v___x_2856_);
if (v___x_2858_ == 0)
{
if (v___x_2857_ == 0)
{
v___y_2832_ = v___x_2854_;
goto v___jp_2831_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = lean_usize_of_nat(v___x_2856_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2830_, v___x_2859_, v___x_2860_, v___x_2854_);
v___y_2832_ = v___x_2861_;
goto v___jp_2831_;
}
}
else
{
size_t v___x_2862_; size_t v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = ((size_t)0ULL);
v___x_2863_ = lean_usize_of_nat(v___x_2856_);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2830_, v___x_2862_, v___x_2863_, v___x_2854_);
v___y_2832_ = v___x_2864_;
goto v___jp_2831_;
}
}
v___jp_2831_:
{
lean_object* v___x_2833_; 
lean_inc(v_fst_2829_);
v___x_2833_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2829_, v_b_2819_, v___y_2832_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v_a_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v_a_2835_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_a_2835_);
lean_dec(v_a_2834_);
v_a_2822_ = v_a_2835_;
goto v___jp_2821_;
}
else
{
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2845_; 
v_a_2836_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2838_ = v___x_2833_;
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2833_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
if (lean_obj_tag(v_a_2836_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v_a_2836_, 1);
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2840_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
else
{
lean_object* v_a_2844_; 
lean_del_object(v___x_2838_);
v_a_2844_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v_a_2836_, 1);
v_a_2822_ = v_a_2844_;
goto v___jp_2821_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_a_2846_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2833_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2833_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
v___jp_2821_:
{
size_t v___x_2823_; size_t v___x_2824_; 
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2818_, v___x_2823_);
v_i_2818_ = v___x_2824_;
v_b_2819_ = v_a_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2865_, lean_object* v_sz_2866_, lean_object* v_i_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_){
_start:
{
size_t v_sz_boxed_2870_; size_t v_i_boxed_2871_; lean_object* v_res_2872_; 
v_sz_boxed_2870_ = lean_unbox_usize(v_sz_2866_);
lean_dec(v_sz_2866_);
v_i_boxed_2871_ = lean_unbox_usize(v_i_2867_);
lean_dec(v_i_2867_);
v_res_2872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2865_, v_sz_boxed_2870_, v_i_boxed_2871_, v_b_2868_);
lean_dec_ref(v_as_2865_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2876_, lean_object* v_as_2877_, size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_b_2880_){
_start:
{
lean_object* v_a_2883_; uint8_t v_anyUnlocated_2887_; 
v_anyUnlocated_2887_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v_anyUnlocated_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec(v_fst_2876_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_b_2880_);
return v___x_2888_;
}
else
{
lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2927_; 
v_fst_2889_ = lean_ctor_get(v_b_2880_, 0);
v_snd_2890_ = lean_ctor_get(v_b_2880_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_b_2880_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2892_ = v_b_2880_;
v_isShared_2893_ = v_isSharedCheck_2927_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_snd_2890_);
lean_inc(v_fst_2889_);
lean_dec(v_b_2880_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2927_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v_a_2894_; lean_object* v_position_x3f_2895_; 
v_a_2894_ = lean_array_uget_borrowed(v_as_2877_, v_i_2879_);
v_position_x3f_2895_ = lean_ctor_get(v_a_2894_, 2);
if (lean_obj_tag(v_position_x3f_2895_) == 0)
{
lean_object* v_linter_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v_snd_2890_);
v_linter_2896_ = lean_ctor_get(v_a_2894_, 0);
v___x_2897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2896_);
v___x_2898_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2896_, v_anyUnlocated_2887_);
v___x_2899_ = lean_string_append(v___x_2897_, v___x_2898_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
lean_inc(v_fst_2876_);
v___x_2902_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2876_, v_anyUnlocated_2887_);
v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2905_ = lean_string_append(v___x_2903_, v___x_2904_);
v___x_2906_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec_ref_known(v___x_2906_, 1);
v___x_2907_ = lean_box(v_anyUnlocated_2887_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2907_);
v___x_2909_ = v___x_2892_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_fst_2889_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
v_a_2883_ = v___x_2909_;
goto v___jp_2882_;
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_del_object(v___x_2892_);
lean_dec(v_fst_2889_);
lean_dec(v_fst_2876_);
v_a_2911_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2906_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2906_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_linter_2919_; lean_object* v_file_2920_; lean_object* v_val_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v_linter_2919_ = lean_ctor_get(v_a_2894_, 0);
v_file_2920_ = lean_ctor_get(v_a_2894_, 3);
v_val_2921_ = lean_ctor_get(v_position_x3f_2895_, 0);
lean_inc(v_linter_2919_);
lean_inc(v_val_2921_);
lean_inc_ref(v_file_2920_);
v___x_2922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2922_, 0, v_file_2920_);
lean_ctor_set(v___x_2922_, 1, v_val_2921_);
lean_ctor_set(v___x_2922_, 2, v_linter_2919_);
v___x_2923_ = lean_array_push(v_fst_2889_, v___x_2922_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2923_);
v___x_2925_ = v___x_2892_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_snd_2890_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
v_a_2883_ = v___x_2925_;
goto v___jp_2882_;
}
}
}
}
v___jp_2882_:
{
size_t v___x_2884_; size_t v___x_2885_; 
v___x_2884_ = ((size_t)1ULL);
v___x_2885_ = lean_usize_add(v_i_2879_, v___x_2884_);
v_i_2879_ = v___x_2885_;
v_b_2880_ = v_a_2883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2928_, lean_object* v_as_2929_, lean_object* v_sz_2930_, lean_object* v_i_2931_, lean_object* v_b_2932_, lean_object* v___y_2933_){
_start:
{
size_t v_sz_boxed_2934_; size_t v_i_boxed_2935_; lean_object* v_res_2936_; 
v_sz_boxed_2934_ = lean_unbox_usize(v_sz_2930_);
lean_dec(v_sz_2930_);
v_i_boxed_2935_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_res_2936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2928_, v_as_2929_, v_sz_boxed_2934_, v_i_boxed_2935_, v_b_2932_);
lean_dec_ref(v_as_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2937_, size_t v_sz_2938_, size_t v_i_2939_, lean_object* v_b_2940_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_usize_dec_lt(v_i_2939_, v_sz_2938_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_b_2940_);
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2971_; 
v_a_2944_ = lean_array_uget_borrowed(v_as_2937_, v_i_2939_);
v_fst_2945_ = lean_ctor_get(v_a_2944_, 0);
v_snd_2946_ = lean_ctor_get(v_a_2944_, 1);
v_fst_2947_ = lean_ctor_get(v_b_2940_, 0);
v_snd_2948_ = lean_ctor_get(v_b_2940_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_b_2940_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2950_ = v_b_2940_;
v_isShared_2951_ = v_isSharedCheck_2971_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snd_2948_);
lean_inc(v_fst_2947_);
lean_dec(v_b_2940_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2971_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_fst_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_snd_2948_);
v___x_2953_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
size_t v_sz_2954_; size_t v___x_2955_; lean_object* v___x_2956_; 
v_sz_2954_ = lean_array_size(v_snd_2946_);
v___x_2955_ = ((size_t)0ULL);
lean_inc(v_fst_2945_);
v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2945_, v_snd_2946_, v_sz_2954_, v___x_2955_, v___x_2953_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_fst_2958_; lean_object* v_snd_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2969_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v_fst_2958_ = lean_ctor_get(v_a_2957_, 0);
v_snd_2959_ = lean_ctor_get(v_a_2957_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2961_ = v_a_2957_;
v_isShared_2962_ = v_isSharedCheck_2969_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_snd_2959_);
lean_inc(v_fst_2958_);
lean_dec(v_a_2957_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2969_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_fst_2958_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_snd_2959_);
v___x_2964_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
size_t v___x_2965_; size_t v___x_2966_; 
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_add(v_i_2939_, v___x_2965_);
v_i_2939_ = v___x_2966_;
v_b_2940_ = v___x_2964_;
goto _start;
}
}
}
else
{
return v___x_2956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2972_, lean_object* v_sz_2973_, lean_object* v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2973_);
lean_dec(v_sz_2973_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2972_, v_sz_boxed_2977_, v_i_boxed_2978_, v_b_2975_);
lean_dec_ref(v_as_2972_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2980_, size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_b_2983_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_usize_dec_lt(v_i_2982_, v_sz_2981_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2983_);
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; lean_object* v_message_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_a_2987_ = lean_array_uget_borrowed(v_as_2980_, v_i_2982_);
v_message_2988_ = lean_ctor_get(v_a_2987_, 1);
v___x_2989_ = 0;
lean_inc_ref(v_message_2988_);
v___x_2990_ = l_Lean_SerialMessage_toString(v_message_2988_, v___x_2989_);
v___x_2991_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2990_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; 
lean_dec_ref_known(v___x_2991_, 1);
v___x_2992_ = lean_box(0);
v___x_2993_ = ((size_t)1ULL);
v___x_2994_ = lean_usize_add(v_i_2982_, v___x_2993_);
v_i_2982_ = v___x_2994_;
v_b_2983_ = v___x_2992_;
goto _start;
}
else
{
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2996_, lean_object* v_sz_2997_, lean_object* v_i_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_){
_start:
{
size_t v_sz_boxed_3001_; size_t v_i_boxed_3002_; lean_object* v_res_3003_; 
v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2997_);
lean_dec(v_sz_2997_);
v_i_boxed_3002_ = lean_unbox_usize(v_i_2998_);
lean_dec(v_i_2998_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2996_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_2999_);
lean_dec_ref(v_as_2996_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3006_, size_t v_sz_3007_, size_t v_i_3008_, lean_object* v_b_3009_){
_start:
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_usize_dec_lt(v_i_3008_, v_sz_3007_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_b_3009_);
return v___x_3012_;
}
else
{
lean_object* v_a_3013_; lean_object* v_fst_3014_; lean_object* v_snd_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3013_ = lean_array_uget_borrowed(v_as_3006_, v_i_3008_);
v_fst_3014_ = lean_ctor_get(v_a_3013_, 0);
v_snd_3015_ = lean_ctor_get(v_a_3013_, 1);
v___x_3016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3014_);
v___x_3017_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3014_, v___x_3011_);
v___x_3018_ = lean_string_append(v___x_3016_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3020_ = lean_string_append(v___x_3018_, v___x_3019_);
v___x_3021_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; size_t v_sz_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = lean_box(0);
v_sz_3023_ = lean_array_size(v_snd_3015_);
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3015_, v_sz_3023_, v___x_3024_, v___x_3022_);
if (lean_obj_tag(v___x_3025_) == 0)
{
size_t v___x_3026_; size_t v___x_3027_; 
lean_dec_ref_known(v___x_3025_, 1);
v___x_3026_ = ((size_t)1ULL);
v___x_3027_ = lean_usize_add(v_i_3008_, v___x_3026_);
v_i_3008_ = v___x_3027_;
v_b_3009_ = v___x_3022_;
goto _start;
}
else
{
return v___x_3025_;
}
}
else
{
return v___x_3021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3029_, lean_object* v_sz_3030_, lean_object* v_i_3031_, lean_object* v_b_3032_, lean_object* v___y_3033_){
_start:
{
size_t v_sz_boxed_3034_; size_t v_i_boxed_3035_; lean_object* v_res_3036_; 
v_sz_boxed_3034_ = lean_unbox_usize(v_sz_3030_);
lean_dec(v_sz_3030_);
v_i_boxed_3035_ = lean_unbox_usize(v_i_3031_);
lean_dec(v_i_3031_);
v_res_3036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3029_, v_sz_boxed_3034_, v_i_boxed_3035_, v_b_3032_);
lean_dec_ref(v_as_3029_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3041_, lean_object* v_linterOpts_3042_, lean_object* v_env_3043_, lean_object* v_mod_3044_){
_start:
{
uint8_t v_lintOnly_3046_; uint8_t v_mode_3047_; lean_object* v___y_3049_; uint8_t v___y_3050_; lean_object* v___y_3118_; lean_object* v___x_3124_; lean_object* v_textGroups_3125_; 
v_lintOnly_3046_ = lean_ctor_get_uint8(v_args_3041_, sizeof(void*)*4);
v_mode_3047_ = lean_ctor_get_uint8(v_args_3041_, sizeof(void*)*4 + 1);
v___x_3124_ = l_Lean_Name_getRoot(v_mod_3044_);
v_textGroups_3125_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3043_, v___x_3124_);
lean_dec(v___x_3124_);
if (v_lintOnly_3046_ == 0)
{
v___y_3118_ = v_textGroups_3125_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = lean_array_get_size(v_textGroups_3125_);
v___x_3128_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3042_, v_textGroups_3125_, v___x_3126_, v___x_3127_);
lean_dec_ref(v_textGroups_3125_);
v___y_3118_ = v___x_3128_;
goto v___jp_3117_;
}
v___jp_3048_:
{
switch(v_mode_3047_)
{
case 0:
{
lean_object* v___x_3051_; size_t v_sz_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = lean_box(0);
v_sz_3052_ = lean_array_size(v___y_3049_);
v___x_3053_ = ((size_t)0ULL);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3049_, v_sz_3052_, v___x_3053_, v___x_3051_);
lean_dec_ref(v___y_3049_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3054_, 0);
lean_dec(v_unused_3063_);
v___x_3056_ = v___x_3054_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v___x_3054_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3058_, 0, v___y_3050_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
v_a_3064_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3054_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3054_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
case 1:
{
lean_object* v___x_3072_; size_t v_sz_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3073_ = lean_array_size(v___y_3049_);
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3049_, v_sz_3073_, v___x_3074_, v___x_3072_);
lean_dec_ref(v___y_3049_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3087_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3087_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3087_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3085_; 
v_fst_3080_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_fst_3080_);
v_snd_3081_ = lean_ctor_get(v_a_3076_, 1);
lean_inc(v_snd_3081_);
lean_dec(v_a_3076_);
v___x_3082_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3082_, 0, v_fst_3080_);
v___x_3083_ = lean_unbox(v_snd_3081_);
lean_dec(v_snd_3081_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*1, v___x_3083_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3082_);
v___x_3085_ = v___x_3078_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3082_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
v_a_3088_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3075_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3075_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v_codeQualityEntries_3096_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3097_ = lean_array_size(v___y_3049_);
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3049_, v_sz_3097_, v___x_3098_, v_codeQualityEntries_3096_);
lean_dec_ref(v___y_3049_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3108_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_a_3100_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3099_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3099_);
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
}
}
v___jp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_array_get_size(v___y_3118_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_nat_dec_eq(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; 
v___x_3122_ = 1;
v___y_3049_ = v___y_3118_;
v___y_3050_ = v___x_3122_;
goto v___jp_3048_;
}
else
{
uint8_t v___x_3123_; 
v___x_3123_ = 0;
v___y_3049_ = v___y_3118_;
v___y_3050_ = v___x_3123_;
goto v___jp_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3129_, lean_object* v_linterOpts_3130_, lean_object* v_env_3131_, lean_object* v_mod_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3129_, v_linterOpts_3130_, v_env_3131_, v_mod_3132_);
lean_dec(v_mod_3132_);
lean_dec_ref(v_env_3131_);
lean_dec_ref(v_linterOpts_3130_);
lean_dec_ref(v_args_3129_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3135_, lean_object* v_t_3136_, lean_object* v_k_3137_, lean_object* v_fallback_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3136_, v_k_3137_, v_fallback_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3140_, lean_object* v_t_3141_, lean_object* v_k_3142_, lean_object* v_fallback_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3140_, v_t_3141_, v_k_3142_, v_fallback_3143_);
lean_dec(v_fallback_3143_);
lean_dec(v_k_3142_);
lean_dec(v_t_3141_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3145_, lean_object* v_____r_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3150_, 0, v___y_3145_);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3152_, lean_object* v_____r_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___y_15651__boxed_3157_; lean_object* v_res_3158_; 
v___y_15651__boxed_3157_ = lean_unbox(v___y_3152_);
v_res_3158_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15651__boxed_3157_, v_____r_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
return v_res_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
lean_ctor_set(v___x_3164_, 2, v___x_3163_);
lean_ctor_set(v___x_3164_, 3, v___x_3163_);
lean_ctor_set(v___x_3164_, 4, v___x_3162_);
lean_ctor_set(v___x_3164_, 5, v___x_3162_);
lean_ctor_set(v___x_3164_, 6, v___x_3162_);
lean_ctor_set(v___x_3164_, 7, v___x_3162_);
lean_ctor_set(v___x_3164_, 8, v___x_3162_);
lean_ctor_set(v___x_3164_, 9, v___x_3162_);
lean_ctor_set(v___x_3164_, 10, v___x_3162_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = lean_unsigned_to_nat(32u);
v___x_3166_ = lean_mk_empty_array_with_capacity(v___x_3165_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3168_ = ((size_t)5ULL);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = lean_unsigned_to_nat(32u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3173_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3169_);
lean_ctor_set(v___x_3173_, 3, v___x_3169_);
lean_ctor_set_usize(v___x_3173_, 4, v___x_3168_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_box(1);
v___x_3175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3175_);
lean_ctor_set(v___x_3177_, 2, v___x_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v_toCold_3183_; lean_object* v_env_3184_; lean_object* v_options_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3182_ = lean_st_ref_get(v___y_3180_);
v_toCold_3183_ = lean_ctor_get(v___y_3179_, 0);
v_env_3184_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_env_3184_);
lean_dec(v___x_3182_);
v_options_3185_ = lean_ctor_get(v_toCold_3183_, 2);
v___x_3186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3185_);
v___x_3188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3188_, 0, v_env_3184_);
lean_ctor_set(v___x_3188_, 1, v___x_3186_);
lean_ctor_set(v___x_3188_, 2, v___x_3187_);
lean_ctor_set(v___x_3188_, 3, v_options_3185_);
v___x_3189_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v_msgData_3178_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_ref_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3210_; 
v_ref_3200_ = lean_ctor_get(v___y_3197_, 2);
v___x_3201_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3196_, v___y_3197_, v___y_3198_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3210_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3210_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
lean_inc(v_ref_3200_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_ref_3200_);
lean_ctor_set(v___x_3206_, 1, v_a_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 1);
lean_ctor_set(v___x_3204_, 0, v___x_3206_);
v___x_3208_ = v___x_3204_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3216_, lean_object* v_msg_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_toCold_3221_; lean_object* v_currRecDepth_3222_; lean_object* v_ref_3223_; uint8_t v_diag_3224_; uint8_t v_suppressElabErrors_3225_; lean_object* v_ref_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_toCold_3221_ = lean_ctor_get(v___y_3218_, 0);
v_currRecDepth_3222_ = lean_ctor_get(v___y_3218_, 1);
v_ref_3223_ = lean_ctor_get(v___y_3218_, 2);
v_diag_3224_ = lean_ctor_get_uint8(v___y_3218_, sizeof(void*)*3);
v_suppressElabErrors_3225_ = lean_ctor_get_uint8(v___y_3218_, sizeof(void*)*3 + 1);
v_ref_3226_ = l_Lean_replaceRef(v_ref_3216_, v_ref_3223_);
lean_inc(v_currRecDepth_3222_);
lean_inc_ref(v_toCold_3221_);
v___x_3227_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3227_, 0, v_toCold_3221_);
lean_ctor_set(v___x_3227_, 1, v_currRecDepth_3222_);
lean_ctor_set(v___x_3227_, 2, v_ref_3226_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3, v_diag_3224_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*3 + 1, v_suppressElabErrors_3225_);
v___x_3228_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3217_, v___x_3227_, v___y_3219_);
lean_dec_ref_known(v___x_3227_, 3);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3229_, lean_object* v_msg_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3229_, v_msg_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v_ref_3229_);
return v_res_3234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3256_, lean_object* v_declHint_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; lean_object* v_env_3261_; uint8_t v___x_3262_; 
v___x_3260_ = lean_st_ref_get(v___y_3258_);
v_env_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_env_3261_);
lean_dec(v___x_3260_);
v___x_3262_ = l_Lean_Name_isAnonymous(v_declHint_3257_);
if (v___x_3262_ == 0)
{
uint8_t v_isExporting_3263_; 
v_isExporting_3263_ = lean_ctor_get_uint8(v_env_3261_, sizeof(void*)*8);
if (v_isExporting_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_dec_ref(v_env_3261_);
lean_dec(v_declHint_3257_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_msg_3256_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
lean_inc_ref(v_env_3261_);
v___x_3265_ = l_Lean_Environment_setExporting(v_env_3261_, v___x_3262_);
lean_inc(v_declHint_3257_);
lean_inc_ref(v___x_3265_);
v___x_3266_ = l_Lean_Environment_contains(v___x_3265_, v_declHint_3257_, v_isExporting_3263_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; 
lean_dec_ref(v___x_3265_);
lean_dec_ref(v_env_3261_);
lean_dec(v_declHint_3257_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_msg_3256_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_c_3273_; lean_object* v___x_3274_; 
v___x_3268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3269_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3270_ = l_Lean_Options_empty;
v___x_3271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3265_);
lean_ctor_set(v___x_3271_, 1, v___x_3268_);
lean_ctor_set(v___x_3271_, 2, v___x_3269_);
lean_ctor_set(v___x_3271_, 3, v___x_3270_);
lean_inc(v_declHint_3257_);
v___x_3272_ = l_Lean_MessageData_ofConstName(v_declHint_3257_, v___x_3262_);
v_c_3273_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3273_, 0, v___x_3271_);
lean_ctor_set(v_c_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3261_, v_declHint_3257_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec_ref(v_env_3261_);
lean_dec(v_declHint_3257_);
v___x_3275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v_c_3273_);
v___x_3277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_MessageData_note(v___x_3278_);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_msg_3256_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3317_; 
v_val_3282_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3284_ = v___x_3274_;
v_isShared_3285_ = v_isSharedCheck_3317_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_val_3282_);
lean_dec(v___x_3274_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3317_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v_mod_3289_; uint8_t v___x_3290_; 
v___x_3286_ = lean_box(0);
v___x_3287_ = l_Lean_Environment_header(v_env_3261_);
lean_dec_ref(v_env_3261_);
v___x_3288_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3287_);
v_mod_3289_ = lean_array_get(v___x_3286_, v___x_3288_, v_val_3282_);
lean_dec(v_val_3282_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = l_Lean_isPrivateName(v_declHint_3257_);
lean_dec(v_declHint_3257_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
lean_ctor_set(v___x_3292_, 1, v_c_3273_);
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_MessageData_ofName(v_mod_3289_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = l_Lean_MessageData_note(v___x_3298_);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_msg_3256_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3300_);
v___x_3302_ = v___x_3284_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v_c_3273_);
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_MessageData_ofName(v_mod_3289_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_MessageData_note(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_msg_3256_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3313_);
v___x_3315_ = v___x_3284_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3318_; 
lean_dec_ref(v_env_3261_);
lean_dec(v_declHint_3257_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_msg_3256_);
return v___x_3318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3319_, lean_object* v_declHint_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3319_, v_declHint_3320_, v___y_3321_);
lean_dec(v___y_3321_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3324_, lean_object* v_declHint_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___x_3329_; lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3339_; 
v___x_3329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3324_, v_declHint_3325_, v___y_3327_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3339_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3339_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3334_ = l_Lean_unknownIdentifierMessageTag;
v___x_3335_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v_a_3330_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3335_);
v___x_3337_ = v___x_3332_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3340_, lean_object* v_declHint_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3340_, v_declHint_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3346_, lean_object* v_msg_3347_, lean_object* v_declHint_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3354_; 
v___x_3352_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3347_, v_declHint_3348_, v___y_3349_, v___y_3350_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3346_, v_a_3353_, v___y_3349_, v___y_3350_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3355_, lean_object* v_msg_3356_, lean_object* v_declHint_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3355_, v_msg_3356_, v_declHint_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v_ref_3355_);
return v_res_3361_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3367_, lean_object* v_constName_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3372_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3373_ = 0;
lean_inc(v_constName_3368_);
v___x_3374_ = l_Lean_MessageData_ofConstName(v_constName_3368_, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3372_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3367_, v___x_3377_, v_constName_3368_, v___y_3369_, v___y_3370_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3379_, lean_object* v_constName_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3379_, v_constName_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v_ref_3379_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_ref_3389_; lean_object* v___x_3390_; 
v_ref_3389_ = lean_ctor_get(v___y_3386_, 2);
v___x_3390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3389_, v_constName_3385_, v___y_3386_, v___y_3387_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; lean_object* v_env_3401_; uint8_t v___x_3402_; lean_object* v___x_3403_; 
v___x_3400_ = lean_st_ref_get(v___y_3398_);
v_env_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc_ref(v_env_3401_);
lean_dec(v___x_3400_);
v___x_3402_ = 0;
lean_inc(v_constName_3396_);
v___x_3403_ = l_Lean_Environment_find_x3f(v_env_3401_, v_constName_3396_, v___x_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3396_, v___y_3397_, v___y_3398_);
return v___x_3404_;
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_constName_3396_);
v_val_3405_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3403_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_val_3405_);
lean_dec(v___x_3403_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set_tag(v___x_3407_, 0);
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_val_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
lean_inc(v_declName_3418_);
v___x_3422_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3449_; 
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v___x_3422_, 0);
lean_dec(v_unused_3450_);
v___x_3424_ = v___x_3422_;
v_isShared_3425_ = v_isSharedCheck_3449_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___x_3422_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3449_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_env_3427_; lean_object* v___x_3428_; 
v___x_3426_ = lean_st_ref_get(v___y_3420_);
v_env_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc_ref(v_env_3427_);
lean_dec(v___x_3426_);
v___x_3428_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3427_, v_declName_3418_);
lean_dec(v_declName_3418_);
lean_dec_ref(v_env_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_box(0);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3429_);
v___x_3431_ = v___x_3424_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
else
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3448_; 
v_val_3433_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3435_ = v___x_3428_;
v_isShared_3436_ = v_isSharedCheck_3448_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v___x_3428_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3448_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v_env_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3437_ = lean_st_ref_get(v___y_3420_);
v_env_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc_ref(v_env_3438_);
lean_dec(v___x_3437_);
v___x_3439_ = lean_box(0);
v___x_3440_ = l_Lean_Environment_allImportedModuleNames(v_env_3438_);
lean_dec_ref(v_env_3438_);
v___x_3441_ = lean_array_get(v___x_3439_, v___x_3440_, v_val_3433_);
lean_dec(v_val_3433_);
lean_dec_ref(v___x_3440_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3441_);
v___x_3443_ = v___x_3435_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3443_);
v___x_3445_ = v___x_3424_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_declName_3418_);
v_a_3451_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3422_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3422_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3465_, lean_object* v_sp_3466_, lean_object* v___x_3467_, lean_object* v_as_3468_, size_t v_sz_3469_, size_t v_i_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_a_3476_; uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3470_, v_sz_3469_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_b_3471_);
return v___x_3481_;
}
else
{
lean_object* v_a_3482_; lean_object* v_fst_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3618_; 
v_a_3482_ = lean_array_uget(v_as_3468_, v_i_3470_);
v_fst_3483_ = lean_ctor_get(v_a_3482_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v_a_3482_, 1);
lean_dec(v_unused_3619_);
v___x_3485_ = v_a_3482_;
v_isShared_3486_ = v_isSharedCheck_3618_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_fst_3483_);
lean_dec(v_a_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3618_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; 
lean_inc(v_fst_3483_);
v___x_3487_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3483_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
if (lean_obj_tag(v_a_3488_) == 0)
{
lean_object* v_fst_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3523_; 
v_fst_3489_ = lean_ctor_get(v_b_3471_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_b_3471_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; 
v_unused_3524_ = lean_ctor_get(v_b_3471_, 1);
lean_dec(v_unused_3524_);
v___x_3491_ = v_b_3471_;
v_isShared_3492_ = v_isSharedCheck_3523_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_fst_3489_);
lean_dec(v_b_3471_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3523_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v_optName_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_optName_3493_ = lean_ctor_get(v_fst_3465_, 1);
v___x_3494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3483_, v___x_3480_);
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3498_ = lean_string_append(v___x_3496_, v___x_3497_);
lean_inc(v_optName_3493_);
v___x_3499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3493_, v___x_3480_);
v___x_3500_ = lean_string_append(v___x_3498_, v___x_3499_);
lean_dec_ref(v___x_3499_);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3502_ = lean_string_append(v___x_3500_, v___x_3501_);
v___x_3503_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3503_, 1);
lean_del_object(v___x_3485_);
v___x_3504_ = lean_box(v___x_3480_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v___x_3504_);
v___x_3506_ = v___x_3491_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_fst_3489_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
v_a_3476_ = v___x_3506_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3522_; 
lean_del_object(v___x_3491_);
lean_dec(v_fst_3489_);
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v_a_3508_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3510_ = v___x_3503_;
v_isShared_3511_ = v_isSharedCheck_3522_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3503_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3522_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_ref_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v_ref_3512_ = lean_ctor_get(v___y_3472_, 2);
v___x_3513_ = lean_io_error_to_string(v_a_3508_);
v___x_3514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
v___x_3515_ = l_Lean_MessageData_ofFormat(v___x_3514_);
lean_inc(v_ref_3512_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___x_3515_);
lean_ctor_set(v___x_3485_, 0, v_ref_3512_);
v___x_3517_ = v___x_3485_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_ref_3512_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3517_);
v___x_3519_ = v___x_3510_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3525_; lean_object* v_snd_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3609_; 
v_fst_3525_ = lean_ctor_get(v_b_3471_, 0);
v_snd_3526_ = lean_ctor_get(v_b_3471_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_b_3471_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3528_ = v_b_3471_;
v_isShared_3529_ = v_isSharedCheck_3609_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_snd_3526_);
lean_inc(v_fst_3525_);
lean_dec(v_b_3471_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3609_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_val_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3608_; 
v_val_3530_ = lean_ctor_get(v_a_3488_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_a_3488_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3532_ = v_a_3488_;
v_isShared_3533_ = v_isSharedCheck_3608_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_val_3530_);
lean_dec(v_a_3488_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3608_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3483_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___y_3537_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
if (lean_obj_tag(v_a_3535_) == 0)
{
lean_inc(v___x_3467_);
v___y_3537_ = v___x_3467_;
goto v___jp_3536_;
}
else
{
lean_object* v_val_3599_; 
v_val_3599_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_val_3599_);
lean_dec_ref_known(v_a_3535_, 1);
v___y_3537_ = v_val_3599_;
goto v___jp_3536_;
}
v___jp_3536_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3537_);
lean_inc(v_sp_3466_);
v___x_3539_ = l_Lean_SearchPath_findWithExt(v_sp_3466_, v___x_3538_, v___y_3537_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v_optName_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v_val_3530_);
lean_dec(v_snd_3526_);
v_optName_3541_ = lean_ctor_get(v_fst_3465_, 1);
v___x_3542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3537_, v___x_3480_);
v___x_3544_ = lean_string_append(v___x_3542_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
lean_inc(v_optName_3541_);
v___x_3547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3541_, v___x_3480_);
v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3550_ = lean_string_append(v___x_3548_, v___x_3549_);
v___x_3551_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3550_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
lean_dec_ref_known(v___x_3551_, 1);
lean_del_object(v___x_3532_);
lean_del_object(v___x_3485_);
v___x_3552_ = lean_box(v___x_3480_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v___x_3552_);
v___x_3554_ = v___x_3528_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_fst_3525_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
v_a_3476_ = v___x_3554_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3572_; 
lean_del_object(v___x_3528_);
lean_dec(v_fst_3525_);
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v_a_3556_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3558_ = v___x_3551_;
v_isShared_3559_ = v_isSharedCheck_3572_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3551_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3572_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_ref_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v_ref_3560_ = lean_ctor_get(v___y_3472_, 2);
v___x_3561_ = lean_io_error_to_string(v_a_3556_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 3);
lean_ctor_set(v___x_3532_, 0, v___x_3561_);
v___x_3563_ = v___x_3532_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = l_Lean_MessageData_ofFormat(v___x_3563_);
lean_inc(v_ref_3560_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___x_3564_);
lean_ctor_set(v___x_3485_, 0, v_ref_3560_);
v___x_3566_ = v___x_3485_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_ref_3560_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3566_);
v___x_3568_ = v___x_3558_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
else
{
lean_object* v_range_3573_; lean_object* v_val_3574_; lean_object* v_pos_3575_; lean_object* v_optName_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_dec(v___y_3537_);
lean_del_object(v___x_3532_);
lean_del_object(v___x_3485_);
v_range_3573_ = lean_ctor_get(v_val_3530_, 0);
lean_inc_ref(v_range_3573_);
lean_dec(v_val_3530_);
v_val_3574_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v_a_3540_, 1);
v_pos_3575_ = lean_ctor_get(v_range_3573_, 0);
lean_inc_ref(v_pos_3575_);
lean_dec_ref(v_range_3573_);
v_optName_3576_ = lean_ctor_get(v_fst_3465_, 1);
lean_inc(v_optName_3576_);
v___x_3577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3577_, 0, v_val_3574_);
lean_ctor_set(v___x_3577_, 1, v_pos_3575_);
lean_ctor_set(v___x_3577_, 2, v_optName_3576_);
v___x_3578_ = lean_array_push(v_fst_3525_, v___x_3577_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3578_);
v___x_3580_ = v___x_3528_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_snd_3526_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
v_a_3476_ = v___x_3580_;
goto v___jp_3475_;
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v___y_3537_);
lean_dec(v_val_3530_);
lean_del_object(v___x_3528_);
lean_dec(v_snd_3526_);
lean_dec(v_fst_3525_);
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v_a_3582_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3584_ = v___x_3539_;
v_isShared_3585_ = v_isSharedCheck_3598_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3539_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3598_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_ref_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v_ref_3586_ = lean_ctor_get(v___y_3472_, 2);
v___x_3587_ = lean_io_error_to_string(v_a_3582_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 3);
lean_ctor_set(v___x_3532_, 0, v___x_3587_);
v___x_3589_ = v___x_3532_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = l_Lean_MessageData_ofFormat(v___x_3589_);
lean_inc(v_ref_3586_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v___x_3590_);
lean_ctor_set(v___x_3485_, 0, v_ref_3586_);
v___x_3592_ = v___x_3485_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_ref_3586_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3592_);
v___x_3594_ = v___x_3584_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3532_);
lean_dec(v_val_3530_);
lean_del_object(v___x_3528_);
lean_dec(v_snd_3526_);
lean_dec(v_fst_3525_);
lean_del_object(v___x_3485_);
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v_a_3600_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3534_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3534_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_del_object(v___x_3485_);
lean_dec(v_fst_3483_);
lean_dec_ref(v_b_3471_);
lean_dec(v___x_3467_);
lean_dec(v_sp_3466_);
lean_dec_ref(v_fst_3465_);
v_a_3610_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3487_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3487_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
v___jp_3475_:
{
size_t v___x_3477_; size_t v___x_3478_; 
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3470_, v___x_3477_);
v_i_3470_ = v___x_3478_;
v_b_3471_ = v_a_3476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3620_, lean_object* v_sp_3621_, lean_object* v___x_3622_, lean_object* v_as_3623_, lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
size_t v_sz_boxed_3630_; size_t v_i_boxed_3631_; lean_object* v_res_3632_; 
v_sz_boxed_3630_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3631_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3620_, v_sp_3621_, v___x_3622_, v_as_3623_, v_sz_boxed_3630_, v_i_boxed_3631_, v_b_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_as_3623_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
if (lean_obj_tag(v_x_3634_) == 0)
{
return v_x_3633_;
}
else
{
lean_object* v_key_3635_; lean_object* v_value_3636_; lean_object* v_tail_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_key_3635_ = lean_ctor_get(v_x_3634_, 0);
v_value_3636_ = lean_ctor_get(v_x_3634_, 1);
v_tail_3637_ = lean_ctor_get(v_x_3634_, 2);
lean_inc(v_value_3636_);
lean_inc(v_key_3635_);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_key_3635_);
lean_ctor_set(v___x_3638_, 1, v_value_3636_);
v___x_3639_ = lean_array_push(v_x_3633_, v___x_3638_);
v_x_3633_ = v___x_3639_;
v_x_3634_ = v_tail_3637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3641_, lean_object* v_x_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3641_, v_x_3642_);
lean_dec(v_x_3642_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3644_, size_t v_i_3645_, size_t v_stop_3646_, lean_object* v_b_3647_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_eq(v_i_3645_, v_stop_3646_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; size_t v___x_3651_; size_t v___x_3652_; 
v___x_3649_ = lean_array_uget_borrowed(v_as_3644_, v_i_3645_);
v___x_3650_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3647_, v___x_3649_);
v___x_3651_ = ((size_t)1ULL);
v___x_3652_ = lean_usize_add(v_i_3645_, v___x_3651_);
v_i_3645_ = v___x_3652_;
v_b_3647_ = v___x_3650_;
goto _start;
}
else
{
return v_b_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3654_, lean_object* v_i_3655_, lean_object* v_stop_3656_, lean_object* v_b_3657_){
_start:
{
size_t v_i_boxed_3658_; size_t v_stop_boxed_3659_; lean_object* v_res_3660_; 
v_i_boxed_3658_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_stop_boxed_3659_ = lean_unbox_usize(v_stop_3656_);
lean_dec(v_stop_3656_);
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3654_, v_i_boxed_3658_, v_stop_boxed_3659_, v_b_3657_);
lean_dec_ref(v_as_3654_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3661_, lean_object* v___x_3662_, lean_object* v_as_3663_, size_t v_sz_3664_, size_t v_i_3665_, lean_object* v_b_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_usize_dec_lt(v_i_3665_, v_sz_3664_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec(v___x_3662_);
lean_dec(v_sp_3661_);
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_b_3666_);
return v___x_3671_;
}
else
{
lean_object* v_a_3672_; lean_object* v_fst_3673_; lean_object* v_snd_3674_; lean_object* v_fst_3675_; lean_object* v_snd_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3710_; 
v_a_3672_ = lean_array_uget_borrowed(v_as_3663_, v_i_3665_);
v_fst_3673_ = lean_ctor_get(v_a_3672_, 0);
v_snd_3674_ = lean_ctor_get(v_a_3672_, 1);
v_fst_3675_ = lean_ctor_get(v_b_3666_, 0);
v_snd_3676_ = lean_ctor_get(v_b_3666_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_b_3666_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3678_ = v_b_3666_;
v_isShared_3679_ = v_isSharedCheck_3710_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_snd_3676_);
lean_inc(v_fst_3675_);
lean_dec(v_b_3666_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3710_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___y_3681_; lean_object* v_size_3701_; lean_object* v_buckets_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_size_3701_ = lean_ctor_get(v_snd_3674_, 0);
v_buckets_3702_ = lean_ctor_get(v_snd_3674_, 1);
v___x_3703_ = lean_mk_empty_array_with_capacity(v_size_3701_);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_array_get_size(v_buckets_3702_);
v___x_3706_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
v___y_3681_ = v___x_3703_;
goto v___jp_3680_;
}
else
{
size_t v___x_3707_; size_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = ((size_t)0ULL);
v___x_3708_ = lean_usize_of_nat(v___x_3705_);
v___x_3709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3702_, v___x_3707_, v___x_3708_, v___x_3703_);
v___y_3681_ = v___x_3709_;
goto v___jp_3680_;
}
v___jp_3680_:
{
lean_object* v___x_3683_; 
if (v_isShared_3679_ == 0)
{
v___x_3683_ = v___x_3678_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_snd_3676_);
v___x_3683_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
size_t v_sz_3684_; size_t v___x_3685_; lean_object* v___x_3686_; 
v_sz_3684_ = lean_array_size(v___y_3681_);
v___x_3685_ = ((size_t)0ULL);
lean_inc(v___x_3662_);
lean_inc(v_sp_3661_);
lean_inc(v_fst_3673_);
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3673_, v_sp_3661_, v___x_3662_, v___y_3681_, v_sz_3684_, v___x_3685_, v___x_3683_, v___y_3667_, v___y_3668_);
lean_dec_ref(v___y_3681_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_fst_3688_; lean_object* v_snd_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3699_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_fst_3688_ = lean_ctor_get(v_a_3687_, 0);
v_snd_3689_ = lean_ctor_get(v_a_3687_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3691_ = v_a_3687_;
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3689_);
lean_inc(v_fst_3688_);
lean_dec(v_a_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_fst_3688_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_snd_3689_);
v___x_3694_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
size_t v___x_3695_; size_t v___x_3696_; 
v___x_3695_ = ((size_t)1ULL);
v___x_3696_ = lean_usize_add(v_i_3665_, v___x_3695_);
v_i_3665_ = v___x_3696_;
v_b_3666_ = v___x_3694_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3662_);
lean_dec(v_sp_3661_);
return v___x_3686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3711_, lean_object* v___x_3712_, lean_object* v_as_3713_, lean_object* v_sz_3714_, lean_object* v_i_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
size_t v_sz_boxed_3720_; size_t v_i_boxed_3721_; lean_object* v_res_3722_; 
v_sz_boxed_3720_ = lean_unbox_usize(v_sz_3714_);
lean_dec(v_sz_3714_);
v_i_boxed_3721_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3711_, v___x_3712_, v_as_3713_, v_sz_boxed_3720_, v_i_boxed_3721_, v_b_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v_as_3713_);
return v_res_3722_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3723_, lean_object* v_as_3724_, size_t v_i_3725_, size_t v_stop_3726_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = lean_usize_dec_eq(v_i_3725_, v_stop_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v_snd_3729_; lean_object* v_size_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3728_ = lean_array_uget_borrowed(v_as_3724_, v_i_3725_);
v_snd_3729_ = lean_ctor_get(v___x_3728_, 1);
v_size_3730_ = lean_ctor_get(v_snd_3729_, 0);
v___x_3731_ = 1;
v___x_3732_ = lean_unsigned_to_nat(0u);
v___x_3733_ = lean_nat_dec_eq(v_size_3730_, v___x_3732_);
if (v___x_3733_ == 0)
{
return v___x_3731_;
}
else
{
if (v___y_3723_ == 0)
{
size_t v___x_3734_; size_t v___x_3735_; 
v___x_3734_ = ((size_t)1ULL);
v___x_3735_ = lean_usize_add(v_i_3725_, v___x_3734_);
v_i_3725_ = v___x_3735_;
goto _start;
}
else
{
return v___x_3731_;
}
}
}
else
{
uint8_t v___x_3737_; 
v___x_3737_ = 0;
return v___x_3737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3738_, lean_object* v_as_3739_, lean_object* v_i_3740_, lean_object* v_stop_3741_){
_start:
{
uint8_t v___y_16635__boxed_3742_; size_t v_i_boxed_3743_; size_t v_stop_boxed_3744_; uint8_t v_res_3745_; lean_object* v_r_3746_; 
v___y_16635__boxed_3742_ = lean_unbox(v___y_3738_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3740_);
lean_dec(v_i_3740_);
v_stop_boxed_3744_ = lean_unbox_usize(v_stop_3741_);
lean_dec(v_stop_3741_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16635__boxed_3742_, v_as_3739_, v_i_boxed_3743_, v_stop_boxed_3744_);
lean_dec_ref(v_as_3739_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3747_, lean_object* v_v_3748_, lean_object* v_t_3749_){
_start:
{
lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; 
if (lean_obj_tag(v_t_3749_) == 0)
{
lean_object* v_size_3764_; lean_object* v_k_3765_; lean_object* v_v_3766_; lean_object* v_l_3767_; lean_object* v_r_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_4028_; 
v_size_3764_ = lean_ctor_get(v_t_3749_, 0);
v_k_3765_ = lean_ctor_get(v_t_3749_, 1);
v_v_3766_ = lean_ctor_get(v_t_3749_, 2);
v_l_3767_ = lean_ctor_get(v_t_3749_, 3);
v_r_3768_ = lean_ctor_get(v_t_3749_, 4);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_t_3749_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_3770_ = v_t_3749_;
v_isShared_3771_ = v_isSharedCheck_4028_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_r_3768_);
lean_inc(v_l_3767_);
lean_inc(v_v_3766_);
lean_inc(v_k_3765_);
lean_inc(v_size_3764_);
lean_dec(v_t_3749_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_4028_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; uint8_t v___y_3822_; lean_object* v_fst_4022_; lean_object* v_snd_4023_; lean_object* v_fst_4024_; lean_object* v_snd_4025_; uint8_t v___x_4026_; 
v_fst_4022_ = lean_ctor_get(v_k_3747_, 0);
v_snd_4023_ = lean_ctor_get(v_k_3747_, 1);
v_fst_4024_ = lean_ctor_get(v_k_3765_, 0);
v_snd_4025_ = lean_ctor_get(v_k_3765_, 1);
v___x_4026_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4022_, v_fst_4024_);
if (v___x_4026_ == 1)
{
uint8_t v___x_4027_; 
v___x_4027_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4023_, v_snd_4025_);
v___y_3822_ = v___x_4027_;
goto v___jp_3821_;
}
else
{
v___y_3822_ = v___x_4026_;
goto v___jp_3821_;
}
v___jp_3772_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_nat_add(v___y_3776_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec(v___y_3776_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 3, v___y_3777_);
lean_ctor_set(v___x_3770_, 0, v___x_3780_);
v___x_3782_ = v___x_3770_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3784_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3784_, 3, v___y_3777_);
lean_ctor_set(v_reuseFailAlloc_3784_, 4, v_r_3768_);
v___x_3782_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3783_, 0, v___y_3775_);
lean_ctor_set(v___x_3783_, 1, v___y_3774_);
lean_ctor_set(v___x_3783_, 2, v___y_3773_);
lean_ctor_set(v___x_3783_, 3, v___y_3778_);
lean_ctor_set(v___x_3783_, 4, v___x_3782_);
return v___x_3783_;
}
}
v___jp_3785_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_nat_add(v___y_3791_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec(v___y_3791_);
v___x_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
lean_ctor_set(v___x_3799_, 1, v___y_3789_);
lean_ctor_set(v___x_3799_, 2, v___y_3793_);
lean_ctor_set(v___x_3799_, 3, v___y_3795_);
lean_ctor_set(v___x_3799_, 4, v___y_3787_);
v___x_3800_ = lean_nat_add(v___y_3796_, v___y_3788_);
lean_dec(v___y_3788_);
if (lean_obj_tag(v___y_3794_) == 0)
{
lean_object* v_size_3801_; 
v_size_3801_ = lean_ctor_get(v___y_3794_, 0);
lean_inc(v_size_3801_);
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___y_3790_;
v___y_3775_ = v___y_3792_;
v___y_3776_ = v___x_3800_;
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___x_3799_;
v___y_3779_ = v_size_3801_;
goto v___jp_3772_;
}
else
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_unsigned_to_nat(0u);
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___y_3790_;
v___y_3775_ = v___y_3792_;
v___y_3776_ = v___x_3800_;
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___x_3799_;
v___y_3779_ = v___x_3802_;
goto v___jp_3772_;
}
}
v___jp_3803_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = lean_nat_add(v___y_3810_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec(v___y_3810_);
v___x_3817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v_k_3765_);
lean_ctor_set(v___x_3817_, 2, v_v_3766_);
lean_ctor_set(v___x_3817_, 3, v_l_3767_);
lean_ctor_set(v___x_3817_, 4, v___y_3807_);
v___x_3818_ = lean_nat_add(v___y_3811_, v___y_3805_);
lean_dec(v___y_3805_);
if (lean_obj_tag(v___y_3804_) == 0)
{
lean_object* v_size_3819_; 
v_size_3819_ = lean_ctor_get(v___y_3804_, 0);
lean_inc(v_size_3819_);
v___y_3751_ = v___y_3804_;
v___y_3752_ = v___y_3806_;
v___y_3753_ = v___x_3817_;
v___y_3754_ = v___y_3809_;
v___y_3755_ = v___y_3808_;
v___y_3756_ = v___x_3818_;
v___y_3757_ = v___y_3812_;
v___y_3758_ = v___y_3813_;
v___y_3759_ = v___y_3814_;
v___y_3760_ = v_size_3819_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___y_3751_ = v___y_3804_;
v___y_3752_ = v___y_3806_;
v___y_3753_ = v___x_3817_;
v___y_3754_ = v___y_3809_;
v___y_3755_ = v___y_3808_;
v___y_3756_ = v___x_3818_;
v___y_3757_ = v___y_3812_;
v___y_3758_ = v___y_3813_;
v___y_3759_ = v___y_3814_;
v___y_3760_ = v___x_3820_;
goto v___jp_3750_;
}
}
v___jp_3821_:
{
switch(v___y_3822_)
{
case 0:
{
lean_object* v_impl_3823_; lean_object* v___x_3824_; 
lean_dec(v_size_3764_);
v_impl_3823_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3747_, v_v_3748_, v_l_3767_);
v___x_3824_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3768_) == 0)
{
lean_object* v_size_3825_; lean_object* v_size_3826_; lean_object* v_k_3827_; lean_object* v_v_3828_; lean_object* v_l_3829_; lean_object* v_r_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_size_3825_ = lean_ctor_get(v_r_3768_, 0);
v_size_3826_ = lean_ctor_get(v_impl_3823_, 0);
lean_inc(v_size_3826_);
v_k_3827_ = lean_ctor_get(v_impl_3823_, 1);
lean_inc(v_k_3827_);
v_v_3828_ = lean_ctor_get(v_impl_3823_, 2);
lean_inc(v_v_3828_);
v_l_3829_ = lean_ctor_get(v_impl_3823_, 3);
lean_inc(v_l_3829_);
v_r_3830_ = lean_ctor_get(v_impl_3823_, 4);
lean_inc(v_r_3830_);
v___x_3831_ = lean_unsigned_to_nat(3u);
v___x_3832_ = lean_nat_mul(v___x_3831_, v_size_3825_);
v___x_3833_ = lean_nat_dec_lt(v___x_3832_, v_size_3826_);
lean_dec(v___x_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec(v_r_3830_);
lean_dec(v_l_3829_);
lean_dec(v_v_3828_);
lean_dec(v_k_3827_);
lean_del_object(v___x_3770_);
v___x_3834_ = lean_nat_add(v___x_3824_, v_size_3826_);
lean_dec(v_size_3826_);
v___x_3835_ = lean_nat_add(v___x_3834_, v_size_3825_);
lean_dec(v___x_3834_);
v___x_3836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
lean_ctor_set(v___x_3836_, 1, v_k_3765_);
lean_ctor_set(v___x_3836_, 2, v_v_3766_);
lean_ctor_set(v___x_3836_, 3, v_impl_3823_);
lean_ctor_set(v___x_3836_, 4, v_r_3768_);
return v___x_3836_;
}
else
{
lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3873_; 
v_isSharedCheck_3873_ = !lean_is_exclusive(v_impl_3823_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; 
v_unused_3874_ = lean_ctor_get(v_impl_3823_, 4);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_impl_3823_, 3);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_impl_3823_, 2);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_impl_3823_, 1);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_impl_3823_, 0);
lean_dec(v_unused_3878_);
v___x_3838_ = v_impl_3823_;
v_isShared_3839_ = v_isSharedCheck_3873_;
goto v_resetjp_3837_;
}
else
{
lean_dec(v_impl_3823_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3873_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v_size_3840_; lean_object* v_size_3841_; lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v_l_3844_; lean_object* v_r_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_size_3840_ = lean_ctor_get(v_l_3829_, 0);
v_size_3841_ = lean_ctor_get(v_r_3830_, 0);
v_k_3842_ = lean_ctor_get(v_r_3830_, 1);
v_v_3843_ = lean_ctor_get(v_r_3830_, 2);
v_l_3844_ = lean_ctor_get(v_r_3830_, 3);
v_r_3845_ = lean_ctor_get(v_r_3830_, 4);
v___x_3846_ = lean_unsigned_to_nat(2u);
v___x_3847_ = lean_nat_mul(v___x_3846_, v_size_3840_);
v___x_3848_ = lean_nat_dec_lt(v_size_3841_, v___x_3847_);
lean_dec(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_inc(v_r_3845_);
lean_inc(v_l_3844_);
lean_inc(v_v_3843_);
lean_inc(v_k_3842_);
lean_del_object(v___x_3838_);
lean_dec(v_r_3830_);
v___x_3849_ = lean_nat_add(v___x_3824_, v_size_3826_);
lean_dec(v_size_3826_);
v___x_3850_ = lean_nat_add(v___x_3849_, v_size_3825_);
lean_dec(v___x_3849_);
v___x_3851_ = lean_nat_add(v___x_3824_, v_size_3840_);
if (lean_obj_tag(v_l_3844_) == 0)
{
lean_object* v_size_3852_; 
v_size_3852_ = lean_ctor_get(v_l_3844_, 0);
lean_inc(v_size_3852_);
lean_inc(v_size_3825_);
v___y_3786_ = v_v_3843_;
v___y_3787_ = v_l_3844_;
v___y_3788_ = v_size_3825_;
v___y_3789_ = v_k_3827_;
v___y_3790_ = v_k_3842_;
v___y_3791_ = v___x_3851_;
v___y_3792_ = v___x_3850_;
v___y_3793_ = v_v_3828_;
v___y_3794_ = v_r_3845_;
v___y_3795_ = v_l_3829_;
v___y_3796_ = v___x_3824_;
v___y_3797_ = v_size_3852_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3825_);
v___y_3786_ = v_v_3843_;
v___y_3787_ = v_l_3844_;
v___y_3788_ = v_size_3825_;
v___y_3789_ = v_k_3827_;
v___y_3790_ = v_k_3842_;
v___y_3791_ = v___x_3851_;
v___y_3792_ = v___x_3850_;
v___y_3793_ = v_v_3828_;
v___y_3794_ = v_r_3845_;
v___y_3795_ = v_l_3829_;
v___y_3796_ = v___x_3824_;
v___y_3797_ = v___x_3853_;
goto v___jp_3785_;
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3859_; 
lean_del_object(v___x_3770_);
v___x_3854_ = lean_nat_add(v___x_3824_, v_size_3826_);
lean_dec(v_size_3826_);
v___x_3855_ = lean_nat_add(v___x_3854_, v_size_3825_);
lean_dec(v___x_3854_);
v___x_3856_ = lean_nat_add(v___x_3824_, v_size_3825_);
v___x_3857_ = lean_nat_add(v___x_3856_, v_size_3841_);
lean_dec(v___x_3856_);
lean_inc_ref(v_r_3768_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 4, v_r_3768_);
lean_ctor_set(v___x_3838_, 3, v_r_3830_);
lean_ctor_set(v___x_3838_, 2, v_v_3766_);
lean_ctor_set(v___x_3838_, 1, v_k_3765_);
lean_ctor_set(v___x_3838_, 0, v___x_3857_);
v___x_3859_ = v___x_3838_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_r_3830_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_r_3768_);
v___x_3859_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
v_isSharedCheck_3866_ = !lean_is_exclusive(v_r_3768_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; 
v_unused_3867_ = lean_ctor_get(v_r_3768_, 4);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_r_3768_, 3);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_r_3768_, 2);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_r_3768_, 1);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_r_3768_, 0);
lean_dec(v_unused_3871_);
v___x_3861_ = v_r_3768_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_dec(v_r_3768_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 4, v___x_3859_);
lean_ctor_set(v___x_3861_, 3, v_l_3829_);
lean_ctor_set(v___x_3861_, 2, v_v_3828_);
lean_ctor_set(v___x_3861_, 1, v_k_3827_);
lean_ctor_set(v___x_3861_, 0, v___x_3855_);
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3827_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3828_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_l_3829_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v___x_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3879_; 
lean_del_object(v___x_3770_);
v_l_3879_ = lean_ctor_get(v_impl_3823_, 3);
lean_inc(v_l_3879_);
if (lean_obj_tag(v_l_3879_) == 0)
{
lean_object* v_r_3880_; lean_object* v_k_3881_; lean_object* v_v_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3891_; 
v_r_3880_ = lean_ctor_get(v_impl_3823_, 4);
v_k_3881_ = lean_ctor_get(v_impl_3823_, 1);
v_v_3882_ = lean_ctor_get(v_impl_3823_, 2);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_impl_3823_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3892_ = lean_ctor_get(v_impl_3823_, 3);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_impl_3823_, 0);
lean_dec(v_unused_3893_);
v___x_3884_ = v_impl_3823_;
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_r_3880_);
lean_inc(v_v_3882_);
lean_inc(v_k_3881_);
lean_dec(v_impl_3823_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3880_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 3, v_r_3880_);
lean_ctor_set(v___x_3884_, 2, v_v_3766_);
lean_ctor_set(v___x_3884_, 1, v_k_3765_);
lean_ctor_set(v___x_3884_, 0, v___x_3824_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v_r_3880_);
lean_ctor_set(v_reuseFailAlloc_3890_, 4, v_r_3880_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3886_);
lean_ctor_set(v___x_3889_, 1, v_k_3881_);
lean_ctor_set(v___x_3889_, 2, v_v_3882_);
lean_ctor_set(v___x_3889_, 3, v_l_3879_);
lean_ctor_set(v___x_3889_, 4, v___x_3888_);
return v___x_3889_;
}
}
}
else
{
lean_object* v_r_3894_; 
v_r_3894_ = lean_ctor_get(v_impl_3823_, 4);
lean_inc(v_r_3894_);
if (lean_obj_tag(v_r_3894_) == 0)
{
lean_object* v_k_3895_; lean_object* v_v_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3917_; 
v_k_3895_ = lean_ctor_get(v_impl_3823_, 1);
v_v_3896_ = lean_ctor_get(v_impl_3823_, 2);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_impl_3823_);
if (v_isSharedCheck_3917_ == 0)
{
lean_object* v_unused_3918_; lean_object* v_unused_3919_; lean_object* v_unused_3920_; 
v_unused_3918_ = lean_ctor_get(v_impl_3823_, 4);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_impl_3823_, 3);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_impl_3823_, 0);
lean_dec(v_unused_3920_);
v___x_3898_ = v_impl_3823_;
v_isShared_3899_ = v_isSharedCheck_3917_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_v_3896_);
lean_inc(v_k_3895_);
lean_dec(v_impl_3823_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3917_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_k_3900_; lean_object* v_v_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3913_; 
v_k_3900_ = lean_ctor_get(v_r_3894_, 1);
v_v_3901_ = lean_ctor_get(v_r_3894_, 2);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_r_3894_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3914_ = lean_ctor_get(v_r_3894_, 4);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_r_3894_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_r_3894_, 0);
lean_dec(v_unused_3916_);
v___x_3903_ = v_r_3894_;
v_isShared_3904_ = v_isSharedCheck_3913_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_v_3901_);
lean_inc(v_k_3900_);
lean_dec(v_r_3894_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3913_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_unsigned_to_nat(3u);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 4, v_l_3879_);
lean_ctor_set(v___x_3903_, 3, v_l_3879_);
lean_ctor_set(v___x_3903_, 2, v_v_3896_);
lean_ctor_set(v___x_3903_, 1, v_k_3895_);
lean_ctor_set(v___x_3903_, 0, v___x_3824_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_k_3895_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_v_3896_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_l_3879_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_l_3879_);
v___x_3907_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 4, v_l_3879_);
lean_ctor_set(v___x_3898_, 2, v_v_3766_);
lean_ctor_set(v___x_3898_, 1, v_k_3765_);
lean_ctor_set(v___x_3898_, 0, v___x_3824_);
v___x_3909_ = v___x_3898_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_l_3879_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_l_3879_);
v___x_3909_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3905_);
lean_ctor_set(v___x_3910_, 1, v_k_3900_);
lean_ctor_set(v___x_3910_, 2, v_v_3901_);
lean_ctor_set(v___x_3910_, 3, v___x_3907_);
lean_ctor_set(v___x_3910_, 4, v___x_3909_);
return v___x_3910_;
}
}
}
}
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_unsigned_to_nat(2u);
v___x_3922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v_k_3765_);
lean_ctor_set(v___x_3922_, 2, v_v_3766_);
lean_ctor_set(v___x_3922_, 3, v_impl_3823_);
lean_ctor_set(v___x_3922_, 4, v_r_3894_);
return v___x_3922_;
}
}
}
}
case 1:
{
lean_object* v___x_3923_; 
lean_del_object(v___x_3770_);
lean_dec(v_v_3766_);
lean_dec(v_k_3765_);
v___x_3923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3923_, 0, v_size_3764_);
lean_ctor_set(v___x_3923_, 1, v_k_3747_);
lean_ctor_set(v___x_3923_, 2, v_v_3748_);
lean_ctor_set(v___x_3923_, 3, v_l_3767_);
lean_ctor_set(v___x_3923_, 4, v_r_3768_);
return v___x_3923_;
}
default: 
{
lean_object* v_impl_3924_; lean_object* v___x_3925_; 
lean_del_object(v___x_3770_);
lean_dec(v_size_3764_);
v_impl_3924_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3747_, v_v_3748_, v_r_3768_);
v___x_3925_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3767_) == 0)
{
lean_object* v_size_3926_; lean_object* v_size_3927_; lean_object* v_k_3928_; lean_object* v_v_3929_; lean_object* v_l_3930_; lean_object* v_r_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v_size_3926_ = lean_ctor_get(v_l_3767_, 0);
v_size_3927_ = lean_ctor_get(v_impl_3924_, 0);
lean_inc(v_size_3927_);
v_k_3928_ = lean_ctor_get(v_impl_3924_, 1);
lean_inc(v_k_3928_);
v_v_3929_ = lean_ctor_get(v_impl_3924_, 2);
lean_inc(v_v_3929_);
v_l_3930_ = lean_ctor_get(v_impl_3924_, 3);
lean_inc(v_l_3930_);
v_r_3931_ = lean_ctor_get(v_impl_3924_, 4);
lean_inc(v_r_3931_);
v___x_3932_ = lean_unsigned_to_nat(3u);
v___x_3933_ = lean_nat_mul(v___x_3932_, v_size_3926_);
v___x_3934_ = lean_nat_dec_lt(v___x_3933_, v_size_3927_);
lean_dec(v___x_3933_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v_r_3931_);
lean_dec(v_l_3930_);
lean_dec(v_v_3929_);
lean_dec(v_k_3928_);
v___x_3935_ = lean_nat_add(v___x_3925_, v_size_3926_);
v___x_3936_ = lean_nat_add(v___x_3935_, v_size_3927_);
lean_dec(v_size_3927_);
lean_dec(v___x_3935_);
v___x_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v_k_3765_);
lean_ctor_set(v___x_3937_, 2, v_v_3766_);
lean_ctor_set(v___x_3937_, 3, v_l_3767_);
lean_ctor_set(v___x_3937_, 4, v_impl_3924_);
return v___x_3937_;
}
else
{
lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3972_; 
v_isSharedCheck_3972_ = !lean_is_exclusive(v_impl_3924_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; lean_object* v_unused_3974_; lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; 
v_unused_3973_ = lean_ctor_get(v_impl_3924_, 4);
lean_dec(v_unused_3973_);
v_unused_3974_ = lean_ctor_get(v_impl_3924_, 3);
lean_dec(v_unused_3974_);
v_unused_3975_ = lean_ctor_get(v_impl_3924_, 2);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_impl_3924_, 1);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_impl_3924_, 0);
lean_dec(v_unused_3977_);
v___x_3939_ = v_impl_3924_;
v_isShared_3940_ = v_isSharedCheck_3972_;
goto v_resetjp_3938_;
}
else
{
lean_dec(v_impl_3924_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3972_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v_size_3941_; lean_object* v_k_3942_; lean_object* v_v_3943_; lean_object* v_l_3944_; lean_object* v_r_3945_; lean_object* v_size_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v_size_3941_ = lean_ctor_get(v_l_3930_, 0);
v_k_3942_ = lean_ctor_get(v_l_3930_, 1);
v_v_3943_ = lean_ctor_get(v_l_3930_, 2);
v_l_3944_ = lean_ctor_get(v_l_3930_, 3);
v_r_3945_ = lean_ctor_get(v_l_3930_, 4);
v_size_3946_ = lean_ctor_get(v_r_3931_, 0);
v___x_3947_ = lean_unsigned_to_nat(2u);
v___x_3948_ = lean_nat_mul(v___x_3947_, v_size_3946_);
v___x_3949_ = lean_nat_dec_lt(v_size_3941_, v___x_3948_);
lean_dec(v___x_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_inc(v_size_3946_);
lean_inc(v_r_3945_);
lean_inc(v_l_3944_);
lean_inc(v_v_3943_);
lean_inc(v_k_3942_);
lean_del_object(v___x_3939_);
lean_dec(v_l_3930_);
v___x_3950_ = lean_nat_add(v___x_3925_, v_size_3926_);
v___x_3951_ = lean_nat_add(v___x_3950_, v_size_3927_);
lean_dec(v_size_3927_);
if (lean_obj_tag(v_l_3944_) == 0)
{
lean_object* v_size_3952_; 
v_size_3952_ = lean_ctor_get(v_l_3944_, 0);
lean_inc(v_size_3952_);
v___y_3804_ = v_r_3945_;
v___y_3805_ = v_size_3946_;
v___y_3806_ = v_k_3942_;
v___y_3807_ = v_l_3944_;
v___y_3808_ = v_k_3928_;
v___y_3809_ = v___x_3951_;
v___y_3810_ = v___x_3950_;
v___y_3811_ = v___x_3925_;
v___y_3812_ = v_v_3943_;
v___y_3813_ = v_v_3929_;
v___y_3814_ = v_r_3931_;
v___y_3815_ = v_size_3952_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_unsigned_to_nat(0u);
v___y_3804_ = v_r_3945_;
v___y_3805_ = v_size_3946_;
v___y_3806_ = v_k_3942_;
v___y_3807_ = v_l_3944_;
v___y_3808_ = v_k_3928_;
v___y_3809_ = v___x_3951_;
v___y_3810_ = v___x_3950_;
v___y_3811_ = v___x_3925_;
v___y_3812_ = v_v_3943_;
v___y_3813_ = v_v_3929_;
v___y_3814_ = v_r_3931_;
v___y_3815_ = v___x_3953_;
goto v___jp_3803_;
}
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3954_ = lean_nat_add(v___x_3925_, v_size_3926_);
v___x_3955_ = lean_nat_add(v___x_3954_, v_size_3927_);
lean_dec(v_size_3927_);
v___x_3956_ = lean_nat_add(v___x_3954_, v_size_3941_);
lean_dec(v___x_3954_);
lean_inc_ref(v_l_3767_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 4, v_l_3930_);
lean_ctor_set(v___x_3939_, 3, v_l_3767_);
lean_ctor_set(v___x_3939_, 2, v_v_3766_);
lean_ctor_set(v___x_3939_, 1, v_k_3765_);
lean_ctor_set(v___x_3939_, 0, v___x_3956_);
v___x_3958_ = v___x_3939_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_l_3767_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_l_3930_);
v___x_3958_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
v_isSharedCheck_3965_ = !lean_is_exclusive(v_l_3767_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; lean_object* v_unused_3967_; lean_object* v_unused_3968_; lean_object* v_unused_3969_; lean_object* v_unused_3970_; 
v_unused_3966_ = lean_ctor_get(v_l_3767_, 4);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_l_3767_, 3);
lean_dec(v_unused_3967_);
v_unused_3968_ = lean_ctor_get(v_l_3767_, 2);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_l_3767_, 1);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_l_3767_, 0);
lean_dec(v_unused_3970_);
v___x_3960_ = v_l_3767_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_dec(v_l_3767_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 4, v_r_3931_);
lean_ctor_set(v___x_3960_, 3, v___x_3958_);
lean_ctor_set(v___x_3960_, 2, v_v_3929_);
lean_ctor_set(v___x_3960_, 1, v_k_3928_);
lean_ctor_set(v___x_3960_, 0, v___x_3955_);
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_k_3928_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_v_3929_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_r_3931_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3978_; 
v_l_3978_ = lean_ctor_get(v_impl_3924_, 3);
lean_inc(v_l_3978_);
if (lean_obj_tag(v_l_3978_) == 0)
{
lean_object* v_r_3979_; lean_object* v_k_3980_; lean_object* v_v_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4002_; 
v_r_3979_ = lean_ctor_get(v_impl_3924_, 4);
v_k_3980_ = lean_ctor_get(v_impl_3924_, 1);
v_v_3981_ = lean_ctor_get(v_impl_3924_, 2);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_impl_3924_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_4003_ = lean_ctor_get(v_impl_3924_, 3);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_impl_3924_, 0);
lean_dec(v_unused_4004_);
v___x_3983_ = v_impl_3924_;
v_isShared_3984_ = v_isSharedCheck_4002_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_r_3979_);
lean_inc(v_v_3981_);
lean_inc(v_k_3980_);
lean_dec(v_impl_3924_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4002_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v_k_3985_; lean_object* v_v_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3998_; 
v_k_3985_ = lean_ctor_get(v_l_3978_, 1);
v_v_3986_ = lean_ctor_get(v_l_3978_, 2);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_l_3978_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; lean_object* v_unused_4001_; 
v_unused_3999_ = lean_ctor_get(v_l_3978_, 4);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_l_3978_, 3);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_l_3978_, 0);
lean_dec(v_unused_4001_);
v___x_3988_ = v_l_3978_;
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_v_3986_);
lean_inc(v_k_3985_);
lean_dec(v_l_3978_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3979_, 2);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 4, v_r_3979_);
lean_ctor_set(v___x_3988_, 3, v_r_3979_);
lean_ctor_set(v___x_3988_, 2, v_v_3766_);
lean_ctor_set(v___x_3988_, 1, v_k_3765_);
lean_ctor_set(v___x_3988_, 0, v___x_3925_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_3997_, 3, v_r_3979_);
lean_ctor_set(v_reuseFailAlloc_3997_, 4, v_r_3979_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
lean_inc(v_r_3979_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 3, v_r_3979_);
lean_ctor_set(v___x_3983_, 0, v___x_3925_);
v___x_3994_ = v___x_3983_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_k_3980_);
lean_ctor_set(v_reuseFailAlloc_3996_, 2, v_v_3981_);
lean_ctor_set(v_reuseFailAlloc_3996_, 3, v_r_3979_);
lean_ctor_set(v_reuseFailAlloc_3996_, 4, v_r_3979_);
v___x_3994_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3990_);
lean_ctor_set(v___x_3995_, 1, v_k_3985_);
lean_ctor_set(v___x_3995_, 2, v_v_3986_);
lean_ctor_set(v___x_3995_, 3, v___x_3992_);
lean_ctor_set(v___x_3995_, 4, v___x_3994_);
return v___x_3995_;
}
}
}
}
}
else
{
lean_object* v_r_4005_; 
v_r_4005_ = lean_ctor_get(v_impl_3924_, 4);
lean_inc(v_r_4005_);
if (lean_obj_tag(v_r_4005_) == 0)
{
lean_object* v_k_4006_; lean_object* v_v_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4016_; 
v_k_4006_ = lean_ctor_get(v_impl_3924_, 1);
v_v_4007_ = lean_ctor_get(v_impl_3924_, 2);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_impl_3924_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; lean_object* v_unused_4018_; lean_object* v_unused_4019_; 
v_unused_4017_ = lean_ctor_get(v_impl_3924_, 4);
lean_dec(v_unused_4017_);
v_unused_4018_ = lean_ctor_get(v_impl_3924_, 3);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_impl_3924_, 0);
lean_dec(v_unused_4019_);
v___x_4009_ = v_impl_3924_;
v_isShared_4010_ = v_isSharedCheck_4016_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_v_4007_);
lean_inc(v_k_4006_);
lean_dec(v_impl_3924_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4016_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4011_ = lean_unsigned_to_nat(3u);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 4, v_l_3978_);
lean_ctor_set(v___x_4009_, 2, v_v_3766_);
lean_ctor_set(v___x_4009_, 1, v_k_3765_);
lean_ctor_set(v___x_4009_, 0, v___x_3925_);
v___x_4013_ = v___x_4009_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_k_3765_);
lean_ctor_set(v_reuseFailAlloc_4015_, 2, v_v_3766_);
lean_ctor_set(v_reuseFailAlloc_4015_, 3, v_l_3978_);
lean_ctor_set(v_reuseFailAlloc_4015_, 4, v_l_3978_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4011_);
lean_ctor_set(v___x_4014_, 1, v_k_4006_);
lean_ctor_set(v___x_4014_, 2, v_v_4007_);
lean_ctor_set(v___x_4014_, 3, v___x_4013_);
lean_ctor_set(v___x_4014_, 4, v_r_4005_);
return v___x_4014_;
}
}
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_unsigned_to_nat(2u);
v___x_4021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
lean_ctor_set(v___x_4021_, 1, v_k_3765_);
lean_ctor_set(v___x_4021_, 2, v_v_3766_);
lean_ctor_set(v___x_4021_, 3, v_r_4005_);
lean_ctor_set(v___x_4021_, 4, v_impl_3924_);
return v___x_4021_;
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
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v_k_3747_);
lean_ctor_set(v___x_4030_, 2, v_v_3748_);
lean_ctor_set(v___x_4030_, 3, v_t_3749_);
lean_ctor_set(v___x_4030_, 4, v_t_3749_);
return v___x_4030_;
}
v___jp_3750_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = lean_nat_add(v___y_3756_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec(v___y_3756_);
v___x_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___y_3755_);
lean_ctor_set(v___x_3762_, 2, v___y_3758_);
lean_ctor_set(v___x_3762_, 3, v___y_3751_);
lean_ctor_set(v___x_3762_, 4, v___y_3759_);
v___x_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3763_, 0, v___y_3754_);
lean_ctor_set(v___x_3763_, 1, v___y_3752_);
lean_ctor_set(v___x_3763_, 2, v___y_3757_);
lean_ctor_set(v___x_3763_, 3, v___y_3753_);
lean_ctor_set(v___x_3763_, 4, v___x_3762_);
return v___x_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4031_, lean_object* v_k_4032_, lean_object* v_fallback_4033_){
_start:
{
if (lean_obj_tag(v_t_4031_) == 0)
{
lean_object* v_k_4034_; lean_object* v_v_4035_; lean_object* v_l_4036_; lean_object* v_r_4037_; uint8_t v___y_4039_; lean_object* v_fst_4042_; lean_object* v_snd_4043_; lean_object* v_fst_4044_; lean_object* v_snd_4045_; uint8_t v___x_4046_; 
v_k_4034_ = lean_ctor_get(v_t_4031_, 1);
v_v_4035_ = lean_ctor_get(v_t_4031_, 2);
v_l_4036_ = lean_ctor_get(v_t_4031_, 3);
v_r_4037_ = lean_ctor_get(v_t_4031_, 4);
v_fst_4042_ = lean_ctor_get(v_k_4032_, 0);
v_snd_4043_ = lean_ctor_get(v_k_4032_, 1);
v_fst_4044_ = lean_ctor_get(v_k_4034_, 0);
v_snd_4045_ = lean_ctor_get(v_k_4034_, 1);
v___x_4046_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4042_, v_fst_4044_);
if (v___x_4046_ == 1)
{
uint8_t v___x_4047_; 
v___x_4047_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4043_, v_snd_4045_);
v___y_4039_ = v___x_4047_;
goto v___jp_4038_;
}
else
{
v___y_4039_ = v___x_4046_;
goto v___jp_4038_;
}
v___jp_4038_:
{
switch(v___y_4039_)
{
case 0:
{
v_t_4031_ = v_l_4036_;
goto _start;
}
case 1:
{
lean_inc(v_v_4035_);
return v_v_4035_;
}
default: 
{
v_t_4031_ = v_r_4037_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4033_);
return v_fallback_4033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4048_, lean_object* v_k_4049_, lean_object* v_fallback_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4048_, v_k_4049_, v_fallback_4050_);
lean_dec(v_fallback_4050_);
lean_dec_ref(v_k_4049_);
lean_dec(v_t_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4052_, lean_object* v_as_4053_, size_t v_sz_4054_, size_t v_i_4055_, lean_object* v_b_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_usize_dec_lt(v_i_4055_, v_sz_4054_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4061_; 
lean_dec(v___x_4052_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v_b_4056_);
return v___x_4061_;
}
else
{
lean_object* v_a_4062_; lean_object* v_fst_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4091_; 
v_a_4062_ = lean_array_uget(v_as_4053_, v_i_4055_);
v_fst_4063_ = lean_ctor_get(v_a_4062_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_a_4062_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v_a_4062_, 1);
lean_dec(v_unused_4092_);
v___x_4065_ = v_a_4062_;
v_isShared_4066_ = v_isSharedCheck_4091_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_fst_4063_);
lean_dec(v_a_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4091_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; 
lean_inc(v_fst_4063_);
v___x_4067_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4063_, v___y_4057_, v___y_4058_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v___y_4071_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_4068_) == 0)
{
lean_inc(v___x_4052_);
v___y_4071_ = v___x_4052_;
goto v___jp_4070_;
}
else
{
lean_object* v_val_4082_; 
v_val_4082_ = lean_ctor_get(v_a_4068_, 0);
lean_inc(v_val_4082_);
lean_dec_ref_known(v_a_4068_, 1);
v___y_4071_ = v_val_4082_;
goto v___jp_4070_;
}
v___jp_4070_:
{
lean_object* v___x_4073_; 
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 1, v_fst_4063_);
lean_ctor_set(v___x_4065_, 0, v___y_4071_);
v___x_4073_ = v___x_4065_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___y_4071_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_fst_4063_);
v___x_4073_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; size_t v___x_4078_; size_t v___x_4079_; 
v___x_4074_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4056_, v___x_4073_, v___x_4069_);
v___x_4075_ = lean_unsigned_to_nat(1u);
v___x_4076_ = lean_nat_add(v___x_4074_, v___x_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4073_, v___x_4076_, v_b_4056_);
v___x_4078_ = ((size_t)1ULL);
v___x_4079_ = lean_usize_add(v_i_4055_, v___x_4078_);
v_i_4055_ = v___x_4079_;
v_b_4056_ = v___x_4077_;
goto _start;
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_del_object(v___x_4065_);
lean_dec(v_fst_4063_);
lean_dec(v_b_4056_);
lean_dec(v___x_4052_);
v_a_4083_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4067_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4067_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4093_, lean_object* v_as_4094_, lean_object* v_sz_4095_, lean_object* v_i_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
size_t v_sz_boxed_4101_; size_t v_i_boxed_4102_; lean_object* v_res_4103_; 
v_sz_boxed_4101_ = lean_unbox_usize(v_sz_4095_);
lean_dec(v_sz_4095_);
v_i_boxed_4102_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4093_, v_as_4094_, v_sz_boxed_4101_, v_i_boxed_4102_, v_b_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec_ref(v_as_4094_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4104_, lean_object* v_init_4105_, lean_object* v_x_4106_){
_start:
{
if (lean_obj_tag(v_x_4106_) == 0)
{
lean_object* v_k_4108_; lean_object* v_v_4109_; lean_object* v_l_4110_; lean_object* v_r_4111_; lean_object* v___x_4112_; lean_object* v_a_4113_; lean_object* v_a_4114_; lean_object* v_fst_4115_; lean_object* v_snd_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4131_; 
v_k_4108_ = lean_ctor_get(v_x_4106_, 1);
lean_inc(v_k_4108_);
v_v_4109_ = lean_ctor_get(v_x_4106_, 2);
lean_inc(v_v_4109_);
v_l_4110_ = lean_ctor_get(v_x_4106_, 3);
lean_inc(v_l_4110_);
v_r_4111_ = lean_ctor_get(v_x_4106_, 4);
lean_inc(v_r_4111_);
lean_dec_ref_known(v_x_4106_, 5);
lean_inc_ref(v_fst_4104_);
v___x_4112_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4104_, v_init_4105_, v_l_4110_);
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref(v___x_4112_);
v_a_4114_ = lean_ctor_get(v_a_4113_, 0);
lean_inc(v_a_4114_);
lean_dec(v_a_4113_);
v_fst_4115_ = lean_ctor_get(v_k_4108_, 0);
v_snd_4116_ = lean_ctor_get(v_k_4108_, 1);
v_isSharedCheck_4131_ = !lean_is_exclusive(v_k_4108_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4118_ = v_k_4108_;
v_isShared_4119_ = v_isSharedCheck_4131_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_snd_4116_);
lean_inc(v_fst_4115_);
lean_dec(v_k_4108_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4131_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v_optName_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v_optName_4120_ = lean_ctor_get(v_fst_4104_, 1);
v___x_4121_ = 1;
lean_inc(v_optName_4120_);
v___x_4122_ = l_Lean_Name_toString(v_optName_4120_, v___x_4121_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 1);
v___x_4124_ = v___x_4118_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_fst_4115_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_snd_4116_);
v___x_4124_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
double v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4125_ = lean_float_of_nat(v_v_4109_);
v___x_4126_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4122_);
lean_ctor_set(v___x_4127_, 1, v___x_4124_);
lean_ctor_set(v___x_4127_, 2, v___x_4126_);
v___x_4128_ = lean_array_push(v_a_4114_, v___x_4127_);
v_init_4105_ = v___x_4128_;
v_x_4106_ = v_r_4111_;
goto _start;
}
}
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec_ref(v_fst_4104_);
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_init_4105_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4134_, lean_object* v_init_4135_, lean_object* v_x_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4134_, v_init_4135_, v_x_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4139_, lean_object* v_as_4140_, size_t v_sz_4141_, size_t v_i_4142_, lean_object* v_b_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_a_4148_; uint8_t v___x_4152_; 
v___x_4152_ = lean_usize_dec_lt(v_i_4142_, v_sz_4141_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec(v___x_4139_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_b_4143_);
return v___x_4153_;
}
else
{
lean_object* v_a_4154_; lean_object* v_snd_4155_; lean_object* v_fst_4156_; lean_object* v_size_4157_; lean_object* v_buckets_4158_; lean_object* v___x_4159_; lean_object* v___y_4161_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v_a_4154_ = lean_array_uget_borrowed(v_as_4140_, v_i_4142_);
v_snd_4155_ = lean_ctor_get(v_a_4154_, 1);
v_fst_4156_ = lean_ctor_get(v_a_4154_, 0);
v_size_4157_ = lean_ctor_get(v_snd_4155_, 0);
v_buckets_4158_ = lean_ctor_get(v_snd_4155_, 1);
v___x_4159_ = lean_box(1);
v___x_4195_ = lean_mk_empty_array_with_capacity(v_size_4157_);
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_array_get_size(v_buckets_4158_);
v___x_4198_ = lean_nat_dec_lt(v___x_4196_, v___x_4197_);
if (v___x_4198_ == 0)
{
v___y_4161_ = v___x_4195_;
goto v___jp_4160_;
}
else
{
size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = ((size_t)0ULL);
v___x_4200_ = lean_usize_of_nat(v___x_4197_);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4158_, v___x_4199_, v___x_4200_, v___x_4195_);
v___y_4161_ = v___x_4201_;
goto v___jp_4160_;
}
v___jp_4160_:
{
size_t v_sz_4162_; size_t v___x_4163_; lean_object* v___x_4164_; 
v_sz_4162_ = lean_array_size(v___y_4161_);
v___x_4163_ = ((size_t)0ULL);
lean_inc(v___x_4139_);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4139_, v___y_4161_, v_sz_4162_, v___x_4163_, v___x_4159_, v___y_4144_, v___y_4145_);
lean_dec_ref(v___y_4161_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
lean_inc(v_fst_4156_);
v___x_4166_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4156_, v_b_4143_, v_a_4165_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v_a_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v_a_4168_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_a_4168_);
lean_dec(v_a_4167_);
v_a_4148_ = v_a_4168_;
goto v___jp_4147_;
}
else
{
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4178_; 
v_a_4169_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4171_ = v___x_4166_;
v_isShared_4172_ = v_isSharedCheck_4178_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4166_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4178_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
if (lean_obj_tag(v_a_4169_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; 
lean_dec(v___x_4139_);
v_a_4173_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v_a_4169_, 1);
if (v_isShared_4172_ == 0)
{
lean_ctor_set_tag(v___x_4171_, 0);
lean_ctor_set(v___x_4171_, 0, v_a_4173_);
v___x_4175_ = v___x_4171_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
else
{
lean_object* v_a_4177_; 
lean_del_object(v___x_4171_);
v_a_4177_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v_a_4169_, 1);
v_a_4148_ = v_a_4177_;
goto v___jp_4147_;
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v___x_4139_);
v_a_4179_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4166_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4166_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v_b_4143_);
lean_dec(v___x_4139_);
v_a_4187_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4164_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4164_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
v___jp_4147_:
{
size_t v___x_4149_; size_t v___x_4150_; 
v___x_4149_ = ((size_t)1ULL);
v___x_4150_ = lean_usize_add(v_i_4142_, v___x_4149_);
v_i_4142_ = v___x_4150_;
v_b_4143_ = v_a_4148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4202_, lean_object* v_as_4203_, lean_object* v_sz_4204_, lean_object* v_i_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
size_t v_sz_boxed_4210_; size_t v_i_boxed_4211_; lean_object* v_res_4212_; 
v_sz_boxed_4210_ = lean_unbox_usize(v_sz_4204_);
lean_dec(v_sz_4204_);
v_i_boxed_4211_ = lean_unbox_usize(v_i_4205_);
lean_dec(v_i_4205_);
v_res_4212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4202_, v_as_4203_, v_sz_boxed_4210_, v_i_boxed_4211_, v_b_4206_, v___y_4207_, v___y_4208_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_as_4203_);
return v_res_4212_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4219_ = l_Lean_maxRecDepth;
v___x_4220_ = l_Lean_Options_empty;
v___x_4221_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4220_, v___x_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4222_, lean_object* v_linterOpts_4223_, lean_object* v_sp_4224_, lean_object* v_env_4225_, lean_object* v_mod_4226_){
_start:
{
lean_object* v_msg_4229_; lean_object* v_a_4234_; lean_object* v_a_4238_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v_a_4269_; lean_object* v___y_4273_; uint8_t v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; uint8_t v___y_4281_; lean_object* v___y_4282_; uint8_t v___y_4283_; lean_object* v___y_4353_; lean_object* v___y_4354_; uint8_t v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; uint8_t v___y_4358_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v_env_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; lean_object* v___y_4379_; lean_object* v___y_4380_; uint8_t v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___x_4408_; uint8_t v___x_4409_; lean_object* v_fileName_4411_; lean_object* v_fileMap_4412_; lean_object* v_currNamespace_4413_; lean_object* v_openDecls_4414_; lean_object* v_initHeartbeats_4415_; lean_object* v_maxHeartbeats_4416_; lean_object* v_quotContext_4417_; lean_object* v_currMacroScope_4418_; lean_object* v_cancelTk_x3f_4419_; lean_object* v_inheritedTraceOptions_4420_; lean_object* v_currRecDepth_4421_; lean_object* v_ref_4422_; uint8_t v_suppressElabErrors_4423_; lean_object* v___y_4424_; uint8_t v___y_4441_; uint8_t v___x_4461_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4254_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4255_ = lean_io_get_num_heartbeats();
v___x_4256_ = l_Lean_firstFrontendMacroScope;
v___x_4257_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4258_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4259_ = lean_box(0);
v___x_4260_ = lean_box(0);
v___x_4261_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4262_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4263_ = 1;
v___x_4264_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4265_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4266_, 0, v_env_4225_);
lean_ctor_set(v___x_4266_, 1, v___x_4257_);
lean_ctor_set(v___x_4266_, 2, v___x_4258_);
lean_ctor_set(v___x_4266_, 3, v___x_4261_);
lean_ctor_set(v___x_4266_, 4, v___x_4262_);
lean_ctor_set(v___x_4266_, 5, v___x_4253_);
lean_ctor_set(v___x_4266_, 6, v___x_4254_);
lean_ctor_set(v___x_4266_, 7, v___x_4264_);
lean_ctor_set(v___x_4266_, 8, v___x_4265_);
v___x_4267_ = lean_st_mk_ref(v___x_4266_);
v___x_4367_ = l_Lean_inheritedTraceOptions;
v___x_4368_ = lean_st_ref_get(v___x_4367_);
v___x_4369_ = lean_st_ref_get(v___x_4267_);
v_env_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc_ref(v_env_4370_);
lean_dec(v___x_4369_);
v___x_4371_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4372_ = l_Lean_instInhabitedFileMap_default;
v___x_4373_ = l_Lean_Options_empty;
v___x_4374_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4375_ = lean_box(0);
v___x_4376_ = lean_box(0);
v___x_4377_ = 0;
v___x_4408_ = l_Lean_Name_getRoot(v_mod_4226_);
v___x_4409_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4461_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4370_);
lean_dec_ref(v_env_4370_);
if (v___x_4409_ == 0)
{
if (v___x_4461_ == 0)
{
lean_inc(v___x_4267_);
v_fileName_4411_ = v___x_4371_;
v_fileMap_4412_ = v___x_4372_;
v_currNamespace_4413_ = v___x_4259_;
v_openDecls_4414_ = v___x_4260_;
v_initHeartbeats_4415_ = v___x_4255_;
v_maxHeartbeats_4416_ = v___x_4374_;
v_quotContext_4417_ = v___x_4259_;
v_currMacroScope_4418_ = v___x_4256_;
v_cancelTk_x3f_4419_ = v___x_4375_;
v_inheritedTraceOptions_4420_ = v___x_4368_;
v_currRecDepth_4421_ = v___x_4252_;
v_ref_4422_ = v___x_4376_;
v_suppressElabErrors_4423_ = v___x_4377_;
v___y_4424_ = v___x_4267_;
goto v___jp_4410_;
}
else
{
v___y_4441_ = v___x_4409_;
goto v___jp_4440_;
}
}
else
{
v___y_4441_ = v___x_4461_;
goto v___jp_4440_;
}
v___jp_4228_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = l_Lean_MessageData_toString(v_msg_4229_);
v___x_4231_ = lean_mk_io_user_error(v___x_4230_);
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
v___jp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_mk_io_user_error(v_a_4234_);
v___x_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
return v___x_4236_;
}
v___jp_4237_:
{
if (lean_obj_tag(v_a_4238_) == 0)
{
lean_object* v_msg_4239_; 
v_msg_4239_ = lean_ctor_get(v_a_4238_, 1);
lean_inc_ref(v_msg_4239_);
lean_dec_ref_known(v_a_4238_, 2);
v_msg_4229_ = v_msg_4239_;
goto v___jp_4228_;
}
else
{
lean_object* v_id_4240_; lean_object* v___x_4241_; 
v_id_4240_ = lean_ctor_get(v_a_4238_, 0);
lean_inc(v_id_4240_);
lean_dec_ref_known(v_a_4238_, 2);
v___x_4241_ = l_Lean_InternalExceptionId_getName(v_id_4240_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_dec(v_id_4240_);
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4244_ = 1;
v___x_4245_ = l_Lean_Name_toString(v_a_4242_, v___x_4244_);
v___x_4246_ = lean_string_append(v___x_4243_, v___x_4245_);
lean_dec_ref(v___x_4245_);
v_a_4234_ = v___x_4246_;
goto v___jp_4233_;
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
lean_dec_ref_known(v___x_4241_, 1);
v___x_4247_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4248_ = l_Nat_reprFast(v_id_4240_);
v___x_4249_ = lean_string_append(v___x_4247_, v___x_4248_);
lean_dec_ref(v___x_4248_);
v___x_4250_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4251_ = lean_string_append(v___x_4249_, v___x_4250_);
v_a_4234_ = v___x_4251_;
goto v___jp_4233_;
}
}
}
v___jp_4268_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4270_ = lean_st_ref_get(v___x_4267_);
lean_dec(v___x_4267_);
lean_dec(v___x_4270_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_a_4269_);
return v___x_4271_;
}
v___jp_4272_:
{
lean_object* v_a_4274_; 
v_a_4274_ = lean_ctor_get(v___y_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref(v___y_4273_);
v_a_4269_ = v_a_4274_;
goto v___jp_4268_;
}
v___jp_4275_:
{
switch(v___y_4281_)
{
case 0:
{
lean_dec(v_sp_4224_);
if (v___y_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4277_);
v___x_4284_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4285_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4226_, v___x_4263_);
v___x_4286_ = lean_string_append(v___x_4284_, v___x_4285_);
lean_dec_ref(v___x_4285_);
v___x_4287_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4288_ = lean_string_append(v___x_4286_, v___x_4287_);
v___x_4289_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4288_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4291_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
v___x_4291_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4283_, v_a_4290_, v___y_4282_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4282_);
v___y_4273_ = v___x_4291_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4301_; 
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4279_);
lean_dec(v___x_4267_);
v_a_4292_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4294_ = v___x_4289_;
v_isShared_4295_ = v_isSharedCheck_4301_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4289_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4301_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4298_; 
v___x_4296_ = lean_io_error_to_string(v_a_4292_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set_tag(v___x_4294_, 3);
lean_ctor_set(v___x_4294_, 0, v___x_4296_);
v___x_4298_ = v___x_4294_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_MessageData_ofFormat(v___x_4298_);
v_msg_4229_ = v___x_4299_;
goto v___jp_4228_;
}
}
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4302_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4226_, v___y_4283_);
v___x_4304_ = lean_string_append(v___x_4302_, v___x_4303_);
lean_dec_ref(v___x_4303_);
v___x_4305_ = lean_array_get_size(v___y_4280_);
lean_dec_ref(v___y_4280_);
v___x_4306_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4278_, v___y_4277_, v___x_4263_, v___x_4304_, v___x_4305_, v___x_4263_, v___y_4282_, v___y_4279_);
lean_dec_ref(v___y_4277_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_MessageData_toString(v_a_4307_);
v___x_4309_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4308_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4283_, v_a_4310_, v___y_4282_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4282_);
v___y_4273_ = v___x_4311_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4321_; 
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4279_);
lean_dec(v___x_4267_);
v_a_4312_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4314_ = v___x_4309_;
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4309_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4316_ = lean_io_error_to_string(v_a_4312_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 3);
lean_ctor_set(v___x_4314_, 0, v___x_4316_);
v___x_4318_ = v___x_4314_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_MessageData_ofFormat(v___x_4318_);
v_msg_4229_ = v___x_4319_;
goto v___jp_4228_;
}
}
}
}
else
{
lean_object* v_a_4322_; 
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4279_);
lean_dec(v___x_4267_);
v_a_4322_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4306_, 1);
v_a_4238_ = v_a_4322_;
goto v___jp_4237_;
}
}
}
case 1:
{
lean_object* v___x_4323_; lean_object* v_env_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; size_t v_sz_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v_mod_4226_);
v___x_4323_ = lean_st_ref_get(v___y_4279_);
v_env_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc_ref(v_env_4324_);
lean_dec(v___x_4323_);
v___x_4325_ = l_Lean_Environment_mainModule(v_env_4324_);
lean_dec_ref(v_env_4324_);
v___x_4326_ = lean_box(v___y_4276_);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4265_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v_sz_4328_ = lean_array_size(v___y_4278_);
v___x_4329_ = ((size_t)0ULL);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4224_, v___x_4325_, v___y_4278_, v_sz_4328_, v___x_4329_, v___x_4327_, v___y_4282_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4278_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v_fst_4332_; lean_object* v_snd_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v_fst_4332_ = lean_ctor_get(v_a_4331_, 0);
lean_inc(v_fst_4332_);
v_snd_4333_ = lean_ctor_get(v_a_4331_, 1);
lean_inc(v_snd_4333_);
lean_dec(v_a_4331_);
v___x_4334_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4334_, 0, v_fst_4332_);
v___x_4335_ = lean_unbox(v_snd_4333_);
lean_dec(v_snd_4333_);
lean_ctor_set_uint8(v___x_4334_, sizeof(void*)*1, v___x_4335_);
v_a_4269_ = v___x_4334_;
goto v___jp_4268_;
}
else
{
lean_object* v_a_4336_; 
lean_dec(v___x_4267_);
v_a_4336_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4330_, 1);
v_a_4238_ = v_a_4336_;
goto v___jp_4237_;
}
}
default: 
{
lean_object* v___x_4337_; lean_object* v_env_4338_; lean_object* v___x_4339_; size_t v_sz_4340_; size_t v___x_4341_; lean_object* v___x_4342_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v_mod_4226_);
lean_dec(v_sp_4224_);
v___x_4337_ = lean_st_ref_get(v___y_4279_);
v_env_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc_ref(v_env_4338_);
lean_dec(v___x_4337_);
v___x_4339_ = l_Lean_Environment_mainModule(v_env_4338_);
lean_dec_ref(v_env_4338_);
v_sz_4340_ = lean_array_size(v___y_4278_);
v___x_4341_ = ((size_t)0ULL);
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4339_, v___y_4278_, v_sz_4340_, v___x_4341_, v___x_4265_, v___y_4282_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4278_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 2);
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
v_a_4269_ = v___x_4348_;
goto v___jp_4268_;
}
}
}
else
{
lean_object* v_a_4351_; 
lean_dec(v___x_4267_);
v_a_4351_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4342_, 1);
v_a_4238_ = v_a_4351_;
goto v___jp_4237_;
}
}
}
}
v___jp_4352_:
{
lean_object* v___x_4359_; 
lean_inc_ref(v___y_4356_);
v___x_4359_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4353_, v___y_4356_, v___y_4357_, v___y_4354_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v___x_4361_ = lean_array_get_size(v_a_4360_);
v___x_4362_ = lean_nat_dec_lt(v___x_4252_, v___x_4361_);
if (v___x_4362_ == 0)
{
v___y_4276_ = v___y_4358_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4360_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4356_;
v___y_4281_ = v___y_4355_;
v___y_4282_ = v___y_4357_;
v___y_4283_ = v___x_4362_;
goto v___jp_4275_;
}
else
{
if (v___x_4362_ == 0)
{
v___y_4276_ = v___y_4358_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4360_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4356_;
v___y_4281_ = v___y_4355_;
v___y_4282_ = v___y_4357_;
v___y_4283_ = v___x_4362_;
goto v___jp_4275_;
}
else
{
size_t v___x_4363_; size_t v___x_4364_; uint8_t v___x_4365_; 
v___x_4363_ = ((size_t)0ULL);
v___x_4364_ = lean_usize_of_nat(v___x_4361_);
v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4358_, v_a_4360_, v___x_4363_, v___x_4364_);
v___y_4276_ = v___y_4358_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4360_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4356_;
v___y_4281_ = v___y_4355_;
v___y_4282_ = v___y_4357_;
v___y_4283_ = v___x_4365_;
goto v___jp_4275_;
}
}
}
else
{
lean_object* v_a_4366_; 
lean_dec_ref(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___x_4267_);
lean_dec(v_mod_4226_);
lean_dec(v_sp_4224_);
v_a_4366_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4359_, 1);
v_a_4238_ = v_a_4366_;
goto v___jp_4237_;
}
}
v___jp_4378_:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4383_, v___y_4382_, v___y_4380_);
lean_dec(v___y_4383_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_array_get_size(v_a_4385_);
v___x_4387_ = lean_nat_dec_eq(v___x_4386_, v___x_4252_);
if (v___x_4387_ == 0)
{
v___y_4353_ = v___y_4379_;
v___y_4354_ = v___y_4380_;
v___y_4355_ = v___y_4381_;
v___y_4356_ = v_a_4385_;
v___y_4357_ = v___y_4382_;
v___y_4358_ = v___x_4387_;
goto v___jp_4352_;
}
else
{
uint8_t v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = 0;
v___x_4389_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4381_, v___x_4388_);
if (v___x_4389_ == 0)
{
v___y_4353_ = v___y_4379_;
v___y_4354_ = v___y_4380_;
v___y_4355_ = v___y_4381_;
v___y_4356_ = v_a_4385_;
v___y_4357_ = v___y_4382_;
v___y_4358_ = v___x_4389_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec(v_a_4385_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v_sp_4224_);
v___x_4390_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4391_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4226_, v___x_4389_);
v___x_4392_ = lean_string_append(v___x_4390_, v___x_4391_);
lean_dec_ref(v___x_4391_);
v___x_4393_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4394_ = lean_string_append(v___x_4392_, v___x_4393_);
v___x_4395_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4394_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v___x_4396_; 
lean_dec_ref_known(v___x_4395_, 1);
v___x_4396_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4269_ = v___x_4396_;
goto v___jp_4268_;
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v___x_4267_);
v_a_4397_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4399_ = v___x_4395_;
v_isShared_4400_ = v_isSharedCheck_4406_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4395_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4406_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4401_ = lean_io_error_to_string(v_a_4397_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set_tag(v___x_4399_, 3);
lean_ctor_set(v___x_4399_, 0, v___x_4401_);
v___x_4403_ = v___x_4399_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_MessageData_ofFormat(v___x_4403_);
v_msg_4229_ = v___x_4404_;
goto v___jp_4228_;
}
}
}
}
}
}
else
{
lean_object* v_a_4407_; 
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___x_4267_);
lean_dec(v_mod_4226_);
lean_dec(v_sp_4224_);
v_a_4407_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4384_, 1);
v_a_4238_ = v_a_4407_;
goto v___jp_4237_;
}
}
v___jp_4410_:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4408_, v___y_4424_);
lean_dec(v___x_4408_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4438_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4438_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4438_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
uint8_t v_lintOnly_4430_; uint8_t v_mode_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v_lintOnly_4430_ = lean_ctor_get_uint8(v_args_4222_, sizeof(void*)*4);
v_mode_4431_ = lean_ctor_get_uint8(v_args_4222_, sizeof(void*)*4 + 1);
v___x_4432_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4418_);
lean_inc(v_quotContext_4417_);
lean_inc(v_maxHeartbeats_4416_);
lean_inc(v_openDecls_4414_);
lean_inc(v_currNamespace_4413_);
lean_inc_ref(v_fileMap_4412_);
lean_inc_ref(v_fileName_4411_);
v___x_4433_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4433_, 0, v_fileName_4411_);
lean_ctor_set(v___x_4433_, 1, v_fileMap_4412_);
lean_ctor_set(v___x_4433_, 2, v___x_4373_);
lean_ctor_set(v___x_4433_, 3, v___x_4432_);
lean_ctor_set(v___x_4433_, 4, v_currNamespace_4413_);
lean_ctor_set(v___x_4433_, 5, v_openDecls_4414_);
lean_ctor_set(v___x_4433_, 6, v_initHeartbeats_4415_);
lean_ctor_set(v___x_4433_, 7, v_maxHeartbeats_4416_);
lean_ctor_set(v___x_4433_, 8, v_quotContext_4417_);
lean_ctor_set(v___x_4433_, 9, v_currMacroScope_4418_);
lean_ctor_set(v___x_4433_, 10, v_cancelTk_x3f_4419_);
lean_ctor_set(v___x_4433_, 11, v_inheritedTraceOptions_4420_);
lean_inc(v_ref_4422_);
v___x_4434_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
lean_ctor_set(v___x_4434_, 1, v_currRecDepth_4421_);
lean_ctor_set(v___x_4434_, 2, v_ref_4422_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3, v___x_4409_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3 + 1, v_suppressElabErrors_4423_);
if (v_lintOnly_4430_ == 0)
{
lean_del_object(v___x_4428_);
lean_dec_ref(v_linterOpts_4223_);
v___y_4379_ = v_a_4426_;
v___y_4380_ = v___y_4424_;
v___y_4381_ = v_mode_4431_;
v___y_4382_ = v___x_4434_;
v___y_4383_ = v___x_4375_;
goto v___jp_4378_;
}
else
{
lean_object* v___x_4436_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 1);
lean_ctor_set(v___x_4428_, 0, v_linterOpts_4223_);
v___x_4436_ = v___x_4428_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_linterOpts_4223_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
v___y_4379_ = v_a_4426_;
v___y_4380_ = v___y_4424_;
v___y_4381_ = v_mode_4431_;
v___y_4382_ = v___x_4434_;
v___y_4383_ = v___x_4436_;
goto v___jp_4378_;
}
}
}
}
else
{
lean_object* v_a_4439_; 
lean_dec(v___y_4424_);
lean_dec(v_currRecDepth_4421_);
lean_dec_ref(v_inheritedTraceOptions_4420_);
lean_dec(v_cancelTk_x3f_4419_);
lean_dec(v_initHeartbeats_4415_);
lean_dec(v___x_4267_);
lean_dec(v_mod_4226_);
lean_dec(v_sp_4224_);
lean_dec_ref(v_linterOpts_4223_);
v_a_4439_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4425_, 1);
v_a_4238_ = v_a_4439_;
goto v___jp_4237_;
}
}
v___jp_4440_:
{
if (v___y_4441_ == 0)
{
lean_object* v___x_4442_; lean_object* v_env_4443_; lean_object* v_nextMacroScope_4444_; lean_object* v_ngen_4445_; lean_object* v_auxDeclNGen_4446_; lean_object* v_traceState_4447_; lean_object* v_messages_4448_; lean_object* v_infoState_4449_; lean_object* v_snapshotTasks_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4459_; 
v___x_4442_ = lean_st_ref_take(v___x_4267_);
v_env_4443_ = lean_ctor_get(v___x_4442_, 0);
v_nextMacroScope_4444_ = lean_ctor_get(v___x_4442_, 1);
v_ngen_4445_ = lean_ctor_get(v___x_4442_, 2);
v_auxDeclNGen_4446_ = lean_ctor_get(v___x_4442_, 3);
v_traceState_4447_ = lean_ctor_get(v___x_4442_, 4);
v_messages_4448_ = lean_ctor_get(v___x_4442_, 6);
v_infoState_4449_ = lean_ctor_get(v___x_4442_, 7);
v_snapshotTasks_4450_ = lean_ctor_get(v___x_4442_, 8);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v___x_4442_, 5);
lean_dec(v_unused_4460_);
v___x_4452_ = v___x_4442_;
v_isShared_4453_ = v_isSharedCheck_4459_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_snapshotTasks_4450_);
lean_inc(v_infoState_4449_);
lean_inc(v_messages_4448_);
lean_inc(v_traceState_4447_);
lean_inc(v_auxDeclNGen_4446_);
lean_inc(v_ngen_4445_);
lean_inc(v_nextMacroScope_4444_);
lean_inc(v_env_4443_);
lean_dec(v___x_4442_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4459_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4454_ = l_Lean_Kernel_enableDiag(v_env_4443_, v___x_4409_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 5, v___x_4253_);
lean_ctor_set(v___x_4452_, 0, v___x_4454_);
v___x_4456_ = v___x_4452_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_nextMacroScope_4444_);
lean_ctor_set(v_reuseFailAlloc_4458_, 2, v_ngen_4445_);
lean_ctor_set(v_reuseFailAlloc_4458_, 3, v_auxDeclNGen_4446_);
lean_ctor_set(v_reuseFailAlloc_4458_, 4, v_traceState_4447_);
lean_ctor_set(v_reuseFailAlloc_4458_, 5, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4458_, 6, v_messages_4448_);
lean_ctor_set(v_reuseFailAlloc_4458_, 7, v_infoState_4449_);
lean_ctor_set(v_reuseFailAlloc_4458_, 8, v_snapshotTasks_4450_);
v___x_4456_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_st_ref_put(v___x_4267_, v___x_4456_);
lean_inc(v___x_4267_);
v_fileName_4411_ = v___x_4371_;
v_fileMap_4412_ = v___x_4372_;
v_currNamespace_4413_ = v___x_4259_;
v_openDecls_4414_ = v___x_4260_;
v_initHeartbeats_4415_ = v___x_4255_;
v_maxHeartbeats_4416_ = v___x_4374_;
v_quotContext_4417_ = v___x_4259_;
v_currMacroScope_4418_ = v___x_4256_;
v_cancelTk_x3f_4419_ = v___x_4375_;
v_inheritedTraceOptions_4420_ = v___x_4368_;
v_currRecDepth_4421_ = v___x_4252_;
v_ref_4422_ = v___x_4376_;
v_suppressElabErrors_4423_ = v___x_4377_;
v___y_4424_ = v___x_4267_;
goto v___jp_4410_;
}
}
}
else
{
lean_inc(v___x_4267_);
v_fileName_4411_ = v___x_4371_;
v_fileMap_4412_ = v___x_4372_;
v_currNamespace_4413_ = v___x_4259_;
v_openDecls_4414_ = v___x_4260_;
v_initHeartbeats_4415_ = v___x_4255_;
v_maxHeartbeats_4416_ = v___x_4374_;
v_quotContext_4417_ = v___x_4259_;
v_currMacroScope_4418_ = v___x_4256_;
v_cancelTk_x3f_4419_ = v___x_4375_;
v_inheritedTraceOptions_4420_ = v___x_4368_;
v_currRecDepth_4421_ = v___x_4252_;
v_ref_4422_ = v___x_4376_;
v_suppressElabErrors_4423_ = v___x_4377_;
v___y_4424_ = v___x_4267_;
goto v___jp_4410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4462_, lean_object* v_linterOpts_4463_, lean_object* v_sp_4464_, lean_object* v_env_4465_, lean_object* v_mod_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4462_, v_linterOpts_4463_, v_sp_4464_, v_env_4465_, v_mod_4466_);
lean_dec_ref(v_args_4462_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4469_, lean_object* v_t_4470_, lean_object* v_k_4471_, lean_object* v_fallback_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4470_, v_k_4471_, v_fallback_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4474_, lean_object* v_t_4475_, lean_object* v_k_4476_, lean_object* v_fallback_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4474_, v_t_4475_, v_k_4476_, v_fallback_4477_);
lean_dec(v_fallback_4477_);
lean_dec_ref(v_k_4476_);
lean_dec(v_t_4475_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4479_, lean_object* v_k_4480_, lean_object* v_v_4481_, lean_object* v_t_4482_, lean_object* v_hl_4483_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4480_, v_v_4481_, v_t_4482_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4485_, lean_object* v_init_4486_, lean_object* v_x_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4485_, v_init_4486_, v_x_4487_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4492_, lean_object* v_init_4493_, lean_object* v_x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4492_, v_init_4493_, v_x_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4499_, lean_object* v_constName_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4500_, v___y_4501_, v___y_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4505_, lean_object* v_constName_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4505_, v_constName_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4511_, lean_object* v_ref_4512_, lean_object* v_constName_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4512_, v_constName_4513_, v___y_4514_, v___y_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4518_, lean_object* v_ref_4519_, lean_object* v_constName_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4518_, v_ref_4519_, v_constName_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v_ref_4519_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4525_, lean_object* v_ref_4526_, lean_object* v_msg_4527_, lean_object* v_declHint_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4526_, v_msg_4527_, v_declHint_4528_, v___y_4529_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4533_, lean_object* v_ref_4534_, lean_object* v_msg_4535_, lean_object* v_declHint_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4533_, v_ref_4534_, v_msg_4535_, v_declHint_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v_ref_4534_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4541_, lean_object* v_declHint_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4541_, v_declHint_4542_, v___y_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4547_, lean_object* v_declHint_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4547_, v_declHint_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4553_, lean_object* v_ref_4554_, lean_object* v_msg_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4554_, v_msg_4555_, v___y_4556_, v___y_4557_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4560_, lean_object* v_ref_4561_, lean_object* v_msg_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4560_, v_ref_4561_, v_msg_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v_ref_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4567_, lean_object* v_msg_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4568_, v___y_4569_, v___y_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4573_, lean_object* v_msg_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4573_, v_msg_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; uint32_t v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4581_ = l_Std_Format_defWidth;
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = l_Std_Format_pretty(v_s_4579_, v___x_4581_, v___x_4582_, v___x_4582_);
v___x_4584_ = 10;
v___x_4585_ = lean_string_push(v___x_4583_, v___x_4584_);
v___x_4586_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4585_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4587_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4590_, size_t v_sz_4591_, size_t v_i_4592_, lean_object* v_b_4593_, lean_object* v___y_4594_){
_start:
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_usize_dec_lt(v_i_4592_, v_sz_4591_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v_b_4593_);
return v___x_4597_;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v_a_4598_ = lean_array_uget_borrowed(v_as_4590_, v_i_4592_);
v___x_4599_ = lean_box(0);
lean_inc(v_a_4598_);
v___x_4600_ = l_Lean_MessageData_format(v_a_4598_, v___x_4599_);
v___x_4601_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4600_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v___x_4602_; size_t v___x_4603_; size_t v___x_4604_; 
lean_dec_ref_known(v___x_4601_, 1);
v___x_4602_ = lean_box(0);
v___x_4603_ = ((size_t)1ULL);
v___x_4604_ = lean_usize_add(v_i_4592_, v___x_4603_);
v_i_4592_ = v___x_4604_;
v_b_4593_ = v___x_4602_;
goto _start;
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4618_; 
v_a_4606_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4608_ = v___x_4601_;
v_isShared_4609_ = v_isSharedCheck_4618_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4601_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4618_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v_ref_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4616_; 
v_ref_4610_ = lean_ctor_get(v___y_4594_, 2);
v___x_4611_ = lean_io_error_to_string(v_a_4606_);
v___x_4612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
v___x_4613_ = l_Lean_MessageData_ofFormat(v___x_4612_);
lean_inc(v_ref_4610_);
v___x_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4614_, 0, v_ref_4610_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4614_);
v___x_4616_ = v___x_4608_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4619_, lean_object* v_sz_4620_, lean_object* v_i_4621_, lean_object* v_b_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
size_t v_sz_boxed_4625_; size_t v_i_boxed_4626_; lean_object* v_res_4627_; 
v_sz_boxed_4625_ = lean_unbox_usize(v_sz_4620_);
lean_dec(v_sz_4620_);
v_i_boxed_4626_ = lean_unbox_usize(v_i_4621_);
lean_dec(v_i_4621_);
v_res_4627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4619_, v_sz_boxed_4625_, v_i_boxed_4626_, v_b_4622_, v___y_4623_);
lean_dec_ref(v___y_4623_);
lean_dec_ref(v_as_4619_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4628_, lean_object* v_entries_4629_, lean_object* v_____r_4630_, uint8_t v_anyFailed_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; size_t v_sz_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v___x_4635_ = lean_box(0);
v_sz_4636_ = lean_array_size(v_errors_4628_);
v___x_4637_ = ((size_t)0ULL);
v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4628_, v_sz_4636_, v___x_4637_, v___x_4635_, v___y_4632_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4647_; 
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; 
v_unused_4648_ = lean_ctor_get(v___x_4638_, 0);
lean_dec(v_unused_4648_);
v___x_4640_ = v___x_4638_;
v_isShared_4641_ = v_isSharedCheck_4647_;
goto v_resetjp_4639_;
}
else
{
lean_dec(v___x_4638_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4647_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4645_; 
v___x_4642_ = lean_box(v_anyFailed_4631_);
v___x_4643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4643_, 0, v_entries_4629_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 0, v___x_4643_);
v___x_4645_ = v___x_4640_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
lean_dec_ref(v_entries_4629_);
v_a_4649_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4638_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4638_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4657_, lean_object* v_entries_4658_, lean_object* v_____r_4659_, lean_object* v_anyFailed_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
uint8_t v_anyFailed_boxed_4664_; lean_object* v_res_4665_; 
v_anyFailed_boxed_4664_ = lean_unbox(v_anyFailed_4660_);
v_res_4665_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4657_, v_entries_4658_, v_____r_4659_, v_anyFailed_boxed_4664_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v_errors_4657_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4666_, lean_object* v_env_4667_, lean_object* v_mod_4668_){
_start:
{
lean_object* v_a_4671_; lean_object* v_a_4675_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___y_4711_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v_env_4729_; uint8_t v_anyFailed_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; lean_object* v_fileName_4739_; lean_object* v_fileMap_4740_; lean_object* v_currNamespace_4741_; lean_object* v_openDecls_4742_; lean_object* v_initHeartbeats_4743_; lean_object* v_maxHeartbeats_4744_; lean_object* v_quotContext_4745_; lean_object* v_currMacroScope_4746_; lean_object* v_cancelTk_x3f_4747_; lean_object* v_inheritedTraceOptions_4748_; lean_object* v_currRecDepth_4749_; lean_object* v_ref_4750_; uint8_t v_suppressElabErrors_4751_; lean_object* v___y_4752_; uint8_t v___y_4772_; uint8_t v___x_4792_; 
v___x_4692_ = lean_unsigned_to_nat(0u);
v___x_4693_ = lean_unsigned_to_nat(32u);
v___x_4694_ = lean_mk_empty_array_with_capacity(v___x_4693_);
lean_dec_ref(v___x_4694_);
v___x_4695_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4696_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4697_ = lean_io_get_num_heartbeats();
v___x_4698_ = l_Lean_firstFrontendMacroScope;
v___x_4699_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4700_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_box(0);
v___x_4703_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4704_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4705_ = 1;
v___x_4706_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4707_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4708_, 0, v_env_4667_);
lean_ctor_set(v___x_4708_, 1, v___x_4699_);
lean_ctor_set(v___x_4708_, 2, v___x_4700_);
lean_ctor_set(v___x_4708_, 3, v___x_4703_);
lean_ctor_set(v___x_4708_, 4, v___x_4704_);
lean_ctor_set(v___x_4708_, 5, v___x_4695_);
lean_ctor_set(v___x_4708_, 6, v___x_4696_);
lean_ctor_set(v___x_4708_, 7, v___x_4706_);
lean_ctor_set(v___x_4708_, 8, v___x_4707_);
v___x_4709_ = lean_st_mk_ref(v___x_4708_);
v___x_4726_ = l_Lean_inheritedTraceOptions;
v___x_4727_ = lean_st_ref_get(v___x_4726_);
v___x_4728_ = lean_st_ref_get(v___x_4709_);
v_env_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc_ref(v_env_4729_);
lean_dec(v___x_4728_);
v_anyFailed_4730_ = 0;
v___x_4731_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4732_ = l_Lean_instInhabitedFileMap_default;
v___x_4733_ = l_Lean_Options_empty;
v___x_4734_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4735_ = lean_box(0);
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4792_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4729_);
lean_dec_ref(v_env_4729_);
if (v___x_4737_ == 0)
{
if (v___x_4792_ == 0)
{
lean_inc(v___x_4709_);
v_fileName_4739_ = v___x_4731_;
v_fileMap_4740_ = v___x_4732_;
v_currNamespace_4741_ = v___x_4701_;
v_openDecls_4742_ = v___x_4702_;
v_initHeartbeats_4743_ = v___x_4697_;
v_maxHeartbeats_4744_ = v___x_4734_;
v_quotContext_4745_ = v___x_4701_;
v_currMacroScope_4746_ = v___x_4698_;
v_cancelTk_x3f_4747_ = v___x_4735_;
v_inheritedTraceOptions_4748_ = v___x_4727_;
v_currRecDepth_4749_ = v___x_4692_;
v_ref_4750_ = v___x_4736_;
v_suppressElabErrors_4751_ = v_anyFailed_4730_;
v___y_4752_ = v___x_4709_;
goto v___jp_4738_;
}
else
{
v___y_4772_ = v___x_4737_;
goto v___jp_4771_;
}
}
else
{
v___y_4772_ = v___x_4792_;
goto v___jp_4771_;
}
v___jp_4670_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = lean_mk_io_user_error(v_a_4671_);
v___x_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
return v___x_4673_;
}
v___jp_4674_:
{
if (lean_obj_tag(v_a_4675_) == 0)
{
lean_object* v_msg_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_msg_4676_ = lean_ctor_get(v_a_4675_, 1);
lean_inc_ref(v_msg_4676_);
lean_dec_ref_known(v_a_4675_, 2);
v___x_4677_ = l_Lean_MessageData_toString(v_msg_4676_);
v___x_4678_ = lean_mk_io_user_error(v___x_4677_);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
else
{
lean_object* v_id_4680_; lean_object* v___x_4681_; 
v_id_4680_ = lean_ctor_get(v_a_4675_, 0);
lean_inc(v_id_4680_);
lean_dec_ref_known(v_a_4675_, 2);
v___x_4681_ = l_Lean_InternalExceptionId_getName(v_id_4680_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
lean_dec(v_id_4680_);
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v___x_4683_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4684_ = 1;
v___x_4685_ = l_Lean_Name_toString(v_a_4682_, v___x_4684_);
v___x_4686_ = lean_string_append(v___x_4683_, v___x_4685_);
lean_dec_ref(v___x_4685_);
v_a_4671_ = v___x_4686_;
goto v___jp_4670_;
}
else
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
lean_dec_ref_known(v___x_4681_, 1);
v___x_4687_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4688_ = l_Nat_reprFast(v_id_4680_);
v___x_4689_ = lean_string_append(v___x_4687_, v___x_4688_);
lean_dec_ref(v___x_4688_);
v___x_4690_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4691_ = lean_string_append(v___x_4689_, v___x_4690_);
v_a_4671_ = v___x_4691_;
goto v___jp_4670_;
}
}
}
v___jp_4710_:
{
if (lean_obj_tag(v___y_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4724_; 
v_a_4712_ = lean_ctor_get(v___y_4711_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___y_4711_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4714_ = v___y_4711_;
v_isShared_4715_ = v_isSharedCheck_4724_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___y_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4724_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v_fst_4717_; lean_object* v_snd_4718_; lean_object* v___x_4719_; uint8_t v___x_4720_; lean_object* v___x_4722_; 
v___x_4716_ = lean_st_ref_get(v___x_4709_);
lean_dec(v___x_4709_);
lean_dec(v___x_4716_);
v_fst_4717_ = lean_ctor_get(v_a_4712_, 0);
lean_inc(v_fst_4717_);
v_snd_4718_ = lean_ctor_get(v_a_4712_, 1);
lean_inc(v_snd_4718_);
lean_dec(v_a_4712_);
v___x_4719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4719_, 0, v_fst_4717_);
v___x_4720_ = lean_unbox(v_snd_4718_);
lean_dec(v_snd_4718_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*1, v___x_4720_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v___x_4719_);
v___x_4722_ = v___x_4714_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4719_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
else
{
lean_object* v_a_4725_; 
lean_dec(v___x_4709_);
v_a_4725_ = lean_ctor_get(v___y_4711_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___y_4711_, 1);
v_a_4675_ = v_a_4725_;
goto v___jp_4674_;
}
}
v___jp_4738_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4753_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4747_);
lean_inc(v_currMacroScope_4746_);
lean_inc(v_quotContext_4745_);
lean_inc(v_maxHeartbeats_4744_);
lean_inc(v_openDecls_4742_);
lean_inc(v_currNamespace_4741_);
lean_inc_ref(v_fileMap_4740_);
lean_inc_ref(v_fileName_4739_);
v___x_4754_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4754_, 0, v_fileName_4739_);
lean_ctor_set(v___x_4754_, 1, v_fileMap_4740_);
lean_ctor_set(v___x_4754_, 2, v___x_4733_);
lean_ctor_set(v___x_4754_, 3, v___x_4753_);
lean_ctor_set(v___x_4754_, 4, v_currNamespace_4741_);
lean_ctor_set(v___x_4754_, 5, v_openDecls_4742_);
lean_ctor_set(v___x_4754_, 6, v_initHeartbeats_4743_);
lean_ctor_set(v___x_4754_, 7, v_maxHeartbeats_4744_);
lean_ctor_set(v___x_4754_, 8, v_quotContext_4745_);
lean_ctor_set(v___x_4754_, 9, v_currMacroScope_4746_);
lean_ctor_set(v___x_4754_, 10, v_cancelTk_x3f_4747_);
lean_ctor_set(v___x_4754_, 11, v_inheritedTraceOptions_4748_);
lean_inc(v_ref_4750_);
v___x_4755_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
lean_ctor_set(v___x_4755_, 1, v_currRecDepth_4749_);
lean_ctor_set(v___x_4755_, 2, v_ref_4750_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*3, v___x_4737_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*3 + 1, v_suppressElabErrors_4751_);
v___x_4756_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4755_, v___y_4752_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4756_, 1);
v___x_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4758_, 0, v_sp_4666_);
lean_ctor_set(v___x_4758_, 1, v_mod_4668_);
v___x_4759_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4757_, v___x_4758_, v___x_4755_, v___y_4752_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v_entries_4761_; lean_object* v_errors_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v_entries_4761_ = lean_ctor_get(v_a_4760_, 0);
lean_inc_ref(v_entries_4761_);
v_errors_4762_ = lean_ctor_get(v_a_4760_, 1);
lean_inc_ref(v_errors_4762_);
lean_dec(v_a_4760_);
v___x_4763_ = lean_array_get_size(v_errors_4762_);
v___x_4764_ = lean_nat_dec_eq(v___x_4763_, v___x_4692_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = lean_box(0);
v___x_4766_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4762_, v_entries_4761_, v___x_4765_, v___x_4705_, v___x_4755_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref_known(v___x_4755_, 3);
lean_dec_ref(v_errors_4762_);
v___y_4711_ = v___x_4766_;
goto v___jp_4710_;
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_box(0);
v___x_4768_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4762_, v_entries_4761_, v___x_4767_, v_anyFailed_4730_, v___x_4755_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref_known(v___x_4755_, 3);
lean_dec_ref(v_errors_4762_);
v___y_4711_ = v___x_4768_;
goto v___jp_4710_;
}
}
else
{
lean_object* v_a_4769_; 
lean_dec_ref_known(v___x_4755_, 3);
lean_dec(v___y_4752_);
lean_dec(v___x_4709_);
v_a_4769_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4759_, 1);
v_a_4675_ = v_a_4769_;
goto v___jp_4674_;
}
}
else
{
lean_object* v_a_4770_; 
lean_dec_ref_known(v___x_4755_, 3);
lean_dec(v___y_4752_);
lean_dec(v___x_4709_);
lean_dec(v_mod_4668_);
lean_dec(v_sp_4666_);
v_a_4770_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4756_, 1);
v_a_4675_ = v_a_4770_;
goto v___jp_4674_;
}
}
v___jp_4771_:
{
if (v___y_4772_ == 0)
{
lean_object* v___x_4773_; lean_object* v_env_4774_; lean_object* v_nextMacroScope_4775_; lean_object* v_ngen_4776_; lean_object* v_auxDeclNGen_4777_; lean_object* v_traceState_4778_; lean_object* v_messages_4779_; lean_object* v_infoState_4780_; lean_object* v_snapshotTasks_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4790_; 
v___x_4773_ = lean_st_ref_take(v___x_4709_);
v_env_4774_ = lean_ctor_get(v___x_4773_, 0);
v_nextMacroScope_4775_ = lean_ctor_get(v___x_4773_, 1);
v_ngen_4776_ = lean_ctor_get(v___x_4773_, 2);
v_auxDeclNGen_4777_ = lean_ctor_get(v___x_4773_, 3);
v_traceState_4778_ = lean_ctor_get(v___x_4773_, 4);
v_messages_4779_ = lean_ctor_get(v___x_4773_, 6);
v_infoState_4780_ = lean_ctor_get(v___x_4773_, 7);
v_snapshotTasks_4781_ = lean_ctor_get(v___x_4773_, 8);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v___x_4773_, 5);
lean_dec(v_unused_4791_);
v___x_4783_ = v___x_4773_;
v_isShared_4784_ = v_isSharedCheck_4790_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_snapshotTasks_4781_);
lean_inc(v_infoState_4780_);
lean_inc(v_messages_4779_);
lean_inc(v_traceState_4778_);
lean_inc(v_auxDeclNGen_4777_);
lean_inc(v_ngen_4776_);
lean_inc(v_nextMacroScope_4775_);
lean_inc(v_env_4774_);
lean_dec(v___x_4773_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4790_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4785_; lean_object* v___x_4787_; 
v___x_4785_ = l_Lean_Kernel_enableDiag(v_env_4774_, v___x_4737_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 5, v___x_4695_);
lean_ctor_set(v___x_4783_, 0, v___x_4785_);
v___x_4787_ = v___x_4783_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_nextMacroScope_4775_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_ngen_4776_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_auxDeclNGen_4777_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_traceState_4778_);
lean_ctor_set(v_reuseFailAlloc_4789_, 5, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4789_, 6, v_messages_4779_);
lean_ctor_set(v_reuseFailAlloc_4789_, 7, v_infoState_4780_);
lean_ctor_set(v_reuseFailAlloc_4789_, 8, v_snapshotTasks_4781_);
v___x_4787_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4788_; 
v___x_4788_ = lean_st_ref_put(v___x_4709_, v___x_4787_);
lean_inc(v___x_4709_);
v_fileName_4739_ = v___x_4731_;
v_fileMap_4740_ = v___x_4732_;
v_currNamespace_4741_ = v___x_4701_;
v_openDecls_4742_ = v___x_4702_;
v_initHeartbeats_4743_ = v___x_4697_;
v_maxHeartbeats_4744_ = v___x_4734_;
v_quotContext_4745_ = v___x_4701_;
v_currMacroScope_4746_ = v___x_4698_;
v_cancelTk_x3f_4747_ = v___x_4735_;
v_inheritedTraceOptions_4748_ = v___x_4727_;
v_currRecDepth_4749_ = v___x_4692_;
v_ref_4750_ = v___x_4736_;
v_suppressElabErrors_4751_ = v_anyFailed_4730_;
v___y_4752_ = v___x_4709_;
goto v___jp_4738_;
}
}
}
else
{
lean_inc(v___x_4709_);
v_fileName_4739_ = v___x_4731_;
v_fileMap_4740_ = v___x_4732_;
v_currNamespace_4741_ = v___x_4701_;
v_openDecls_4742_ = v___x_4702_;
v_initHeartbeats_4743_ = v___x_4697_;
v_maxHeartbeats_4744_ = v___x_4734_;
v_quotContext_4745_ = v___x_4701_;
v_currMacroScope_4746_ = v___x_4698_;
v_cancelTk_x3f_4747_ = v___x_4735_;
v_inheritedTraceOptions_4748_ = v___x_4727_;
v_currRecDepth_4749_ = v___x_4692_;
v_ref_4750_ = v___x_4736_;
v_suppressElabErrors_4751_ = v_anyFailed_4730_;
v___y_4752_ = v___x_4709_;
goto v___jp_4738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4793_, lean_object* v_env_4794_, lean_object* v_mod_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4793_, v_env_4794_, v_mod_4795_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4798_, size_t v_sz_4799_, size_t v_i_4800_, lean_object* v_b_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v___x_4805_; 
v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4798_, v_sz_4799_, v_i_4800_, v_b_4801_, v___y_4802_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4806_, lean_object* v_sz_4807_, lean_object* v_i_4808_, lean_object* v_b_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
size_t v_sz_boxed_4813_; size_t v_i_boxed_4814_; lean_object* v_res_4815_; 
v_sz_boxed_4813_ = lean_unbox_usize(v_sz_4807_);
lean_dec(v_sz_4807_);
v_i_boxed_4814_ = lean_unbox_usize(v_i_4808_);
lean_dec(v_i_4808_);
v_res_4815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4806_, v_sz_boxed_4813_, v_i_boxed_4814_, v_b_4809_, v___y_4810_, v___y_4811_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v_as_4806_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_enable_initializer_execution();
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4820_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_compacted_region_free(v_region_4820_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4823_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4829_, lean_object* v_k_4830_, uint8_t v_v_4831_){
_start:
{
lean_object* v_map_4832_; uint8_t v_hasTrace_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4847_; 
v_map_4832_ = lean_ctor_get(v_o_4829_, 0);
v_hasTrace_4833_ = lean_ctor_get_uint8(v_o_4829_, sizeof(void*)*1);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_o_4829_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4835_ = v_o_4829_;
v_isShared_4836_ = v_isSharedCheck_4847_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_map_4832_);
lean_dec(v_o_4829_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4847_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4837_, 0, v_v_4831_);
lean_inc(v_k_4830_);
v___x_4838_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4830_, v___x_4837_, v_map_4832_);
if (v_hasTrace_4833_ == 0)
{
lean_object* v___x_4839_; uint8_t v___x_4840_; lean_object* v___x_4842_; 
v___x_4839_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4840_ = l_Lean_Name_isPrefixOf(v___x_4839_, v_k_4830_);
lean_dec(v_k_4830_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4838_);
v___x_4842_ = v___x_4835_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4838_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1, v___x_4840_);
return v___x_4842_;
}
}
else
{
lean_object* v___x_4845_; 
lean_dec(v_k_4830_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4838_);
v___x_4845_ = v___x_4835_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4838_);
lean_ctor_set_uint8(v_reuseFailAlloc_4846_, sizeof(void*)*1, v_hasTrace_4833_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4848_, lean_object* v_k_4849_, lean_object* v_v_4850_){
_start:
{
uint8_t v_v_boxed_4851_; lean_object* v_res_4852_; 
v_v_boxed_4851_ = lean_unbox(v_v_4850_);
v_res_4852_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4848_, v_k_4849_, v_v_boxed_4851_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; uint32_t v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4855_ = lean_unsigned_to_nat(80u);
v___x_4856_ = l_Lean_Json_pretty(v_s_4853_, v___x_4855_);
v___x_4857_ = 10;
v___x_4858_ = lean_string_push(v___x_4856_, v___x_4857_);
v___x_4859_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4860_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4863_, size_t v_sz_4864_, size_t v_i_4865_, lean_object* v_b_4866_){
_start:
{
uint8_t v___x_4868_; 
v___x_4868_ = lean_usize_dec_lt(v_i_4865_, v_sz_4864_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_b_4866_);
return v___x_4869_;
}
else
{
lean_object* v_a_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v_a_4870_ = lean_array_uget_borrowed(v_as_4863_, v_i_4865_);
lean_inc(v_a_4870_);
v___x_4871_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4870_);
v___x_4872_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4871_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v___x_4873_; size_t v___x_4874_; size_t v___x_4875_; 
lean_dec_ref_known(v___x_4872_, 1);
v___x_4873_ = lean_box(0);
v___x_4874_ = ((size_t)1ULL);
v___x_4875_ = lean_usize_add(v_i_4865_, v___x_4874_);
v_i_4865_ = v___x_4875_;
v_b_4866_ = v___x_4873_;
goto _start;
}
else
{
return v___x_4872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4877_, lean_object* v_sz_4878_, lean_object* v_i_4879_, lean_object* v_b_4880_, lean_object* v___y_4881_){
_start:
{
size_t v_sz_boxed_4882_; size_t v_i_boxed_4883_; lean_object* v_res_4884_; 
v_sz_boxed_4882_ = lean_unbox_usize(v_sz_4878_);
lean_dec(v_sz_4878_);
v_i_boxed_4883_ = lean_unbox_usize(v_i_4879_);
lean_dec(v_i_4879_);
v_res_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4877_, v_sz_boxed_4882_, v_i_boxed_4883_, v_b_4880_);
lean_dec_ref(v_as_4877_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4885_, size_t v_sz_4886_, size_t v_i_4887_, lean_object* v_bs_4888_){
_start:
{
uint8_t v_anyUnlocated_4889_; 
v_anyUnlocated_4889_ = lean_usize_dec_lt(v_i_4887_, v_sz_4886_);
if (v_anyUnlocated_4889_ == 0)
{
return v_bs_4888_;
}
else
{
lean_object* v___x_4890_; uint8_t v_anyFailed_4891_; lean_object* v_v_4892_; lean_object* v_bs_x27_4893_; lean_object* v___x_4894_; size_t v___x_4895_; size_t v___x_4896_; lean_object* v___x_4897_; 
v___x_4890_ = lean_unsigned_to_nat(0u);
v_anyFailed_4891_ = lean_nat_dec_eq(v___x_4885_, v___x_4890_);
v_v_4892_ = lean_array_uget(v_bs_4888_, v_i_4887_);
v_bs_x27_4893_ = lean_array_uset(v_bs_4888_, v_i_4887_, v___x_4890_);
v___x_4894_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4894_, 0, v_v_4892_);
lean_ctor_set_uint8(v___x_4894_, sizeof(void*)*1, v_anyFailed_4891_);
lean_ctor_set_uint8(v___x_4894_, sizeof(void*)*1 + 1, v_anyUnlocated_4889_);
lean_ctor_set_uint8(v___x_4894_, sizeof(void*)*1 + 2, v_anyFailed_4891_);
v___x_4895_ = ((size_t)1ULL);
v___x_4896_ = lean_usize_add(v_i_4887_, v___x_4895_);
v___x_4897_ = lean_array_uset(v_bs_x27_4893_, v_i_4887_, v___x_4894_);
v_i_4887_ = v___x_4896_;
v_bs_4888_ = v___x_4897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4899_, lean_object* v_sz_4900_, lean_object* v_i_4901_, lean_object* v_bs_4902_){
_start:
{
size_t v_sz_boxed_4903_; size_t v_i_boxed_4904_; lean_object* v_res_4905_; 
v_sz_boxed_4903_ = lean_unbox_usize(v_sz_4900_);
lean_dec(v_sz_4900_);
v_i_boxed_4904_ = lean_unbox_usize(v_i_4901_);
lean_dec(v_i_4901_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4899_, v_sz_boxed_4903_, v_i_boxed_4904_, v_bs_4902_);
lean_dec(v___x_4899_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4906_, size_t v_i_4907_, size_t v_stop_4908_, lean_object* v_b_4909_){
_start:
{
uint8_t v___x_4910_; 
v___x_4910_ = lean_usize_dec_eq(v_i_4907_, v_stop_4908_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; lean_object* v_fst_4912_; lean_object* v_snd_4913_; uint8_t v___x_4914_; lean_object* v___x_4915_; size_t v___x_4916_; size_t v___x_4917_; 
v___x_4911_ = lean_array_uget_borrowed(v_as_4906_, v_i_4907_);
v_fst_4912_ = lean_ctor_get(v___x_4911_, 0);
v_snd_4913_ = lean_ctor_get(v___x_4911_, 1);
v___x_4914_ = lean_unbox(v_snd_4913_);
lean_inc(v_fst_4912_);
v___x_4915_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4909_, v_fst_4912_, v___x_4914_);
v___x_4916_ = ((size_t)1ULL);
v___x_4917_ = lean_usize_add(v_i_4907_, v___x_4916_);
v_i_4907_ = v___x_4917_;
v_b_4909_ = v___x_4915_;
goto _start;
}
else
{
return v_b_4909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4919_, lean_object* v_i_4920_, lean_object* v_stop_4921_, lean_object* v_b_4922_){
_start:
{
size_t v_i_boxed_4923_; size_t v_stop_boxed_4924_; lean_object* v_res_4925_; 
v_i_boxed_4923_ = lean_unbox_usize(v_i_4920_);
lean_dec(v_i_4920_);
v_stop_boxed_4924_ = lean_unbox_usize(v_stop_4921_);
lean_dec(v_stop_4921_);
v_res_4925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4919_, v_i_boxed_4923_, v_stop_boxed_4924_, v_b_4922_);
lean_dec_ref(v_as_4919_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4935_, lean_object* v_checkImports_4936_, lean_object* v_args_4937_, lean_object* v___x_4938_, lean_object* v_as_4939_, size_t v_sz_4940_, size_t v_i_4941_, lean_object* v_b_4942_){
_start:
{
lean_object* v_a_4945_; lean_object* v___x_4949_; uint8_t v_anyFailed_4950_; uint8_t v_anyUnlocated_4951_; lean_object* v___x_4952_; lean_object* v_envLinterModule_4953_; uint8_t v___x_4954_; 
v___x_4949_ = lean_unsigned_to_nat(0u);
v_anyFailed_4950_ = lean_nat_dec_eq(v___x_4935_, v___x_4949_);
v_anyUnlocated_4951_ = 1;
v___x_4952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4953_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4953_, 0, v___x_4952_);
lean_ctor_set_uint8(v_envLinterModule_4953_, sizeof(void*)*1, v_anyFailed_4950_);
lean_ctor_set_uint8(v_envLinterModule_4953_, sizeof(void*)*1 + 1, v_anyUnlocated_4951_);
lean_ctor_set_uint8(v_envLinterModule_4953_, sizeof(void*)*1 + 2, v_anyFailed_4950_);
v___x_4954_ = lean_usize_dec_lt(v_i_4941_, v_sz_4940_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; 
lean_dec_ref_known(v_envLinterModule_4953_, 1);
lean_dec(v___x_4938_);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_b_4942_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; lean_object* v_a_4957_; lean_object* v___x_4958_; 
v___x_4956_ = lean_enable_initializer_execution();
v_a_4957_ = lean_array_uget_borrowed(v_as_4939_, v_i_4941_);
lean_inc(v_a_4957_);
v___x_4958_ = l_Lean_findOLean(v_a_4957_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4960_ = l_Lean_readModuleData(v_a_4959_);
lean_dec(v_a_4959_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v_fst_4962_; lean_object* v_snd_4963_; uint8_t v___x_4964_; lean_object* v_snd_4965_; lean_object* v_snd_4966_; lean_object* v_snd_4967_; lean_object* v_snd_4968_; lean_object* v_fst_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_5257_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v_fst_4962_ = lean_ctor_get(v_a_4961_, 0);
lean_inc(v_fst_4962_);
v_snd_4963_ = lean_ctor_get(v_a_4961_, 1);
lean_inc(v_snd_4963_);
lean_dec(v_a_4961_);
v___x_4964_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4962_);
lean_dec(v_fst_4962_);
v_snd_4965_ = lean_ctor_get(v_b_4942_, 1);
lean_inc(v_snd_4965_);
v_snd_4966_ = lean_ctor_get(v_snd_4965_, 1);
lean_inc(v_snd_4966_);
v_snd_4967_ = lean_ctor_get(v_snd_4966_, 1);
lean_inc(v_snd_4967_);
v_snd_4968_ = lean_ctor_get(v_snd_4967_, 1);
lean_inc(v_snd_4968_);
v_fst_4969_ = lean_ctor_get(v_b_4942_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_b_4942_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v_b_4942_, 1);
lean_dec(v_unused_5258_);
v___x_4971_ = v_b_4942_;
v_isShared_4972_ = v_isSharedCheck_5257_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_fst_4969_);
lean_dec(v_b_4942_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_5257_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v_fst_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_5255_; 
v_fst_4973_ = lean_ctor_get(v_snd_4965_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_snd_4965_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; 
v_unused_5256_ = lean_ctor_get(v_snd_4965_, 1);
lean_dec(v_unused_5256_);
v___x_4975_ = v_snd_4965_;
v_isShared_4976_ = v_isSharedCheck_5255_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_fst_4973_);
lean_dec(v_snd_4965_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_5255_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v_fst_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_5253_; 
v_fst_4977_ = lean_ctor_get(v_snd_4966_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_snd_4966_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v_snd_4966_, 1);
lean_dec(v_unused_5254_);
v___x_4979_ = v_snd_4966_;
v_isShared_4980_ = v_isSharedCheck_5253_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_fst_4977_);
lean_dec(v_snd_4966_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_5253_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v_fst_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_5251_; 
v_fst_4981_ = lean_ctor_get(v_snd_4967_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v_snd_4967_);
if (v_isSharedCheck_5251_ == 0)
{
lean_object* v_unused_5252_; 
v_unused_5252_ = lean_ctor_get(v_snd_4967_, 1);
lean_dec(v_unused_5252_);
v___x_4983_ = v_snd_4967_;
v_isShared_4984_ = v_isSharedCheck_5251_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_fst_4981_);
lean_dec(v_snd_4967_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_5251_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v_fst_4985_; lean_object* v_snd_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5250_; 
v_fst_4985_ = lean_ctor_get(v_snd_4968_, 0);
v_snd_4986_ = lean_ctor_get(v_snd_4968_, 1);
v_isSharedCheck_5250_ = !lean_is_exclusive(v_snd_4968_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_4988_ = v_snd_4968_;
v_isShared_4989_ = v_isSharedCheck_5250_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_snd_4986_);
lean_inc(v_fst_4985_);
lean_dec(v_snd_4968_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5250_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___y_4991_; lean_object* v___y_4992_; uint8_t v_anyFailed_4993_; uint8_t v_anyUnlocated_4994_; lean_object* v_records_4995_; lean_object* v_codeQualityEntries_4996_; lean_object* v___y_5143_; lean_object* v___y_5144_; uint8_t v_anyFailed_5145_; uint8_t v_anyUnlocated_5146_; lean_object* v_records_5147_; lean_object* v_codeQualityEntries_5148_; lean_object* v___x_5165_; lean_object* v___y_5167_; lean_object* v___y_5168_; uint8_t v___y_5208_; 
v___x_5165_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
if (v___x_4964_ == 0)
{
uint8_t v___x_5248_; 
v___x_5248_ = 2;
v___y_5208_ = v___x_5248_;
goto v___jp_5207_;
}
else
{
uint8_t v___x_5249_; 
v___x_5249_ = 1;
v___y_5208_ = v___x_5249_;
goto v___jp_5207_;
}
v___jp_4990_:
{
uint8_t v_mode_4997_; uint8_t v___x_4998_; uint8_t v___x_4999_; 
v_mode_4997_ = lean_ctor_get_uint8(v_args_4937_, sizeof(void*)*4 + 1);
v___x_4998_ = 2;
v___x_4999_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4997_, v___x_4998_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = l_Lean_Name_getRoot(v_a_4957_);
lean_inc(v___x_4938_);
v___x_5001_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4937_, v___y_4992_, v___x_4938_, v___y_4991_, v___x_5000_, v_fst_4985_);
lean_dec_ref(v___y_4992_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v_outcome_5003_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc(v_a_5002_);
lean_dec_ref_known(v___x_5001_, 1);
v_outcome_5003_ = lean_ctor_get(v_a_5002_, 0);
if (lean_obj_tag(v_outcome_5003_) == 0)
{
uint8_t v_failed_5004_; 
v_failed_5004_ = lean_ctor_get_uint8(v_outcome_5003_, 0);
if (v_failed_5004_ == 0)
{
lean_object* v_checkedModules_5005_; lean_object* v___x_5007_; 
v_checkedModules_5005_ = lean_ctor_get(v_a_5002_, 1);
lean_inc(v_checkedModules_5005_);
lean_dec(v_a_5002_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_checkedModules_5005_);
v___x_5007_ = v___x_4988_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_checkedModules_5005_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_snd_4986_);
v___x_5007_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5009_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5007_);
lean_ctor_set(v___x_4983_, 0, v_codeQualityEntries_4996_);
v___x_5009_ = v___x_4983_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_codeQualityEntries_4996_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5011_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5009_);
lean_ctor_set(v___x_4979_, 0, v_records_4995_);
v___x_5011_ = v___x_4979_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_records_4995_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5012_ = lean_box(v_anyUnlocated_4994_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5011_);
lean_ctor_set(v___x_4975_, 0, v___x_5012_);
v___x_5014_ = v___x_4975_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5012_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5011_);
v___x_5014_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
v___x_5015_ = lean_box(v_anyFailed_4993_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5014_);
lean_ctor_set(v___x_4971_, 0, v___x_5015_);
v___x_5017_ = v___x_4971_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5014_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
v_a_4945_ = v___x_5017_;
goto v___jp_4944_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5023_; lean_object* v___x_5025_; 
v_checkedModules_5023_ = lean_ctor_get(v_a_5002_, 1);
lean_inc(v_checkedModules_5023_);
lean_dec(v_a_5002_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_checkedModules_5023_);
v___x_5025_ = v___x_4988_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_checkedModules_5023_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v_snd_4986_);
v___x_5025_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5027_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5025_);
lean_ctor_set(v___x_4983_, 0, v_codeQualityEntries_4996_);
v___x_5027_ = v___x_4983_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_codeQualityEntries_4996_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5029_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5027_);
lean_ctor_set(v___x_4979_, 0, v_records_4995_);
v___x_5029_ = v___x_4979_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_records_4995_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5030_ = lean_box(v_anyUnlocated_4994_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5029_);
lean_ctor_set(v___x_4975_, 0, v___x_5030_);
v___x_5032_ = v___x_4975_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5029_);
v___x_5032_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5033_; lean_object* v___x_5035_; 
v___x_5033_ = lean_box(v_anyUnlocated_4951_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5032_);
lean_ctor_set(v___x_4971_, 0, v___x_5033_);
v___x_5035_ = v___x_4971_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5032_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
v_a_4945_ = v___x_5035_;
goto v___jp_4944_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5041_; lean_object* v_records_5042_; uint8_t v_unlocated_5043_; lean_object* v___x_5044_; 
lean_inc_ref(v_outcome_5003_);
v_checkedModules_5041_ = lean_ctor_get(v_a_5002_, 1);
lean_inc(v_checkedModules_5041_);
lean_dec(v_a_5002_);
v_records_5042_ = lean_ctor_get(v_outcome_5003_, 0);
lean_inc_ref(v_records_5042_);
v_unlocated_5043_ = lean_ctor_get_uint8(v_outcome_5003_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_5003_, 1);
v___x_5044_ = l_Array_append___redArg(v_records_4995_, v_records_5042_);
lean_dec_ref(v_records_5042_);
if (v_unlocated_5043_ == 0)
{
lean_object* v___x_5046_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_checkedModules_5041_);
v___x_5046_ = v___x_4988_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_checkedModules_5041_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v_snd_4986_);
v___x_5046_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5048_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5046_);
lean_ctor_set(v___x_4983_, 0, v_codeQualityEntries_4996_);
v___x_5048_ = v___x_4983_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_codeQualityEntries_4996_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v___x_5046_);
v___x_5048_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5050_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5048_);
lean_ctor_set(v___x_4979_, 0, v___x_5044_);
v___x_5050_ = v___x_4979_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5051_; lean_object* v___x_5053_; 
v___x_5051_ = lean_box(v_anyUnlocated_4994_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5050_);
lean_ctor_set(v___x_4975_, 0, v___x_5051_);
v___x_5053_ = v___x_4975_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5051_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v___x_5050_);
v___x_5053_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
lean_object* v___x_5054_; lean_object* v___x_5056_; 
v___x_5054_ = lean_box(v_anyFailed_4993_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5053_);
lean_ctor_set(v___x_4971_, 0, v___x_5054_);
v___x_5056_ = v___x_4971_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5054_);
lean_ctor_set(v_reuseFailAlloc_5057_, 1, v___x_5053_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
v_a_4945_ = v___x_5056_;
goto v___jp_4944_;
}
}
}
}
}
}
else
{
lean_object* v___x_5063_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_checkedModules_5041_);
v___x_5063_ = v___x_4988_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_checkedModules_5041_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v_snd_4986_);
v___x_5063_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
lean_object* v___x_5065_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5063_);
lean_ctor_set(v___x_4983_, 0, v_codeQualityEntries_4996_);
v___x_5065_ = v___x_4983_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_codeQualityEntries_4996_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5063_);
v___x_5065_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
lean_object* v___x_5067_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5065_);
lean_ctor_set(v___x_4979_, 0, v___x_5044_);
v___x_5067_ = v___x_4979_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5068_ = lean_box(v_anyUnlocated_4951_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5067_);
lean_ctor_set(v___x_4975_, 0, v___x_5068_);
v___x_5070_ = v___x_4975_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v___x_5067_);
v___x_5070_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; lean_object* v___x_5073_; 
v___x_5071_ = lean_box(v_anyFailed_4993_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5070_);
lean_ctor_set(v___x_4971_, 0, v___x_5071_);
v___x_5073_ = v___x_4971_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5074_, 1, v___x_5070_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
v_a_4945_ = v___x_5073_;
goto v___jp_4944_;
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
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec_ref(v_codeQualityEntries_4996_);
lean_dec_ref(v_records_4995_);
lean_del_object(v___x_4988_);
lean_dec(v_snd_4986_);
lean_del_object(v___x_4983_);
lean_del_object(v___x_4979_);
lean_del_object(v___x_4975_);
lean_del_object(v___x_4971_);
lean_dec(v___x_4938_);
v_a_5079_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5001_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5001_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
else
{
lean_object* v___x_5087_; lean_object* v_fst_5088_; lean_object* v_snd_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5141_; 
lean_del_object(v___x_4971_);
v___x_5087_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4937_, v___y_4992_, v___y_4991_, v_a_4957_, v_snd_4986_);
lean_dec_ref(v___y_4992_);
v_fst_5088_ = lean_ctor_get(v___x_5087_, 0);
v_snd_5089_ = lean_ctor_get(v___x_5087_, 1);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5091_ = v___x_5087_;
v_isShared_5092_ = v_isSharedCheck_5141_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_snd_5089_);
lean_inc(v_fst_5088_);
lean_dec(v___x_5087_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5141_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; 
lean_inc(v_a_4957_);
lean_inc(v___x_4938_);
v___x_5093_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4938_, v___y_4991_, v_a_4957_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v_entries_5095_; uint8_t v_failed_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5093_, 1);
v_entries_5095_ = lean_ctor_get(v_a_5094_, 0);
lean_inc_ref(v_entries_5095_);
v_failed_5096_ = lean_ctor_get_uint8(v_a_5094_, sizeof(void*)*1);
lean_dec(v_a_5094_);
v___x_5097_ = l_Array_append___redArg(v_codeQualityEntries_4996_, v_fst_5088_);
lean_dec(v_fst_5088_);
v___x_5098_ = l_Array_append___redArg(v___x_5097_, v_entries_5095_);
lean_dec_ref(v_entries_5095_);
if (v_failed_5096_ == 0)
{
lean_object* v___x_5100_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v_fst_4985_);
v___x_5100_ = v___x_5091_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_fst_4985_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v_snd_5089_);
v___x_5100_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5102_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5100_);
lean_ctor_set(v___x_4988_, 0, v___x_5098_);
v___x_5102_ = v___x_4988_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v___x_5098_);
lean_ctor_set(v_reuseFailAlloc_5114_, 1, v___x_5100_);
v___x_5102_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5104_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5102_);
lean_ctor_set(v___x_4983_, 0, v_records_4995_);
v___x_5104_ = v___x_4983_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_records_4995_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5105_; lean_object* v___x_5107_; 
v___x_5105_ = lean_box(v_anyUnlocated_4994_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5104_);
lean_ctor_set(v___x_4979_, 0, v___x_5105_);
v___x_5107_ = v___x_4979_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v___x_5104_);
v___x_5107_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5108_; lean_object* v___x_5110_; 
v___x_5108_ = lean_box(v_anyFailed_4993_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5107_);
lean_ctor_set(v___x_4975_, 0, v___x_5108_);
v___x_5110_ = v___x_4975_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v___x_5107_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
v_a_4945_ = v___x_5110_;
goto v___jp_4944_;
}
}
}
}
}
}
else
{
lean_object* v___x_5117_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v_fst_4985_);
v___x_5117_ = v___x_5091_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_fst_4985_);
lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_snd_5089_);
v___x_5117_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5119_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___x_5117_);
lean_ctor_set(v___x_4988_, 0, v___x_5098_);
v___x_5119_ = v___x_4988_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5098_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v___x_5117_);
v___x_5119_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
lean_object* v___x_5121_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v___x_5119_);
lean_ctor_set(v___x_4983_, 0, v_records_4995_);
v___x_5121_ = v___x_4983_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_records_4995_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5122_; lean_object* v___x_5124_; 
v___x_5122_ = lean_box(v_anyUnlocated_4994_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v___x_5121_);
lean_ctor_set(v___x_4979_, 0, v___x_5122_);
v___x_5124_ = v___x_4979_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5122_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5121_);
v___x_5124_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5127_; 
v___x_5125_ = lean_box(v_anyUnlocated_4951_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5124_);
lean_ctor_set(v___x_4975_, 0, v___x_5125_);
v___x_5127_ = v___x_4975_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v___x_5124_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
v_a_4945_ = v___x_5127_;
goto v___jp_4944_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
lean_del_object(v___x_5091_);
lean_dec(v_snd_5089_);
lean_dec(v_fst_5088_);
lean_dec_ref(v_codeQualityEntries_4996_);
lean_dec_ref(v_records_4995_);
lean_del_object(v___x_4988_);
lean_dec(v_fst_4985_);
lean_del_object(v___x_4983_);
lean_del_object(v___x_4979_);
lean_del_object(v___x_4975_);
lean_dec(v___x_4938_);
v_a_5133_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5093_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5093_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
}
}
v___jp_5142_:
{
lean_object* v___x_5149_; 
lean_inc(v_a_4957_);
lean_inc_ref(v___y_5143_);
lean_inc(v___x_4938_);
lean_inc_ref(v___y_5144_);
v___x_5149_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4937_, v___y_5144_, v___x_4938_, v___y_5143_, v_a_4957_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
switch(lean_obj_tag(v_a_5150_))
{
case 0:
{
uint8_t v_failed_5151_; 
v_failed_5151_ = lean_ctor_get_uint8(v_a_5150_, 0);
lean_dec_ref_known(v_a_5150_, 0);
if (v_failed_5151_ == 0)
{
v___y_4991_ = v___y_5143_;
v___y_4992_ = v___y_5144_;
v_anyFailed_4993_ = v_anyFailed_5145_;
v_anyUnlocated_4994_ = v_anyUnlocated_5146_;
v_records_4995_ = v_records_5147_;
v_codeQualityEntries_4996_ = v_codeQualityEntries_5148_;
goto v___jp_4990_;
}
else
{
v___y_4991_ = v___y_5143_;
v___y_4992_ = v___y_5144_;
v_anyFailed_4993_ = v_anyUnlocated_4951_;
v_anyUnlocated_4994_ = v_anyUnlocated_5146_;
v_records_4995_ = v_records_5147_;
v_codeQualityEntries_4996_ = v_codeQualityEntries_5148_;
goto v___jp_4990_;
}
}
case 1:
{
lean_object* v_records_5152_; uint8_t v_unlocated_5153_; lean_object* v___x_5154_; 
v_records_5152_ = lean_ctor_get(v_a_5150_, 0);
lean_inc_ref(v_records_5152_);
v_unlocated_5153_ = lean_ctor_get_uint8(v_a_5150_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5150_, 1);
v___x_5154_ = l_Array_append___redArg(v_records_5147_, v_records_5152_);
lean_dec_ref(v_records_5152_);
if (v_unlocated_5153_ == 0)
{
v___y_4991_ = v___y_5143_;
v___y_4992_ = v___y_5144_;
v_anyFailed_4993_ = v_anyFailed_5145_;
v_anyUnlocated_4994_ = v_anyUnlocated_5146_;
v_records_4995_ = v___x_5154_;
v_codeQualityEntries_4996_ = v_codeQualityEntries_5148_;
goto v___jp_4990_;
}
else
{
v___y_4991_ = v___y_5143_;
v___y_4992_ = v___y_5144_;
v_anyFailed_4993_ = v_anyFailed_5145_;
v_anyUnlocated_4994_ = v_anyUnlocated_4951_;
v_records_4995_ = v___x_5154_;
v_codeQualityEntries_4996_ = v_codeQualityEntries_5148_;
goto v___jp_4990_;
}
}
default: 
{
lean_object* v_entries_5155_; lean_object* v___x_5156_; 
v_entries_5155_ = lean_ctor_get(v_a_5150_, 0);
lean_inc_ref(v_entries_5155_);
lean_dec_ref_known(v_a_5150_, 1);
v___x_5156_ = l_Array_append___redArg(v_codeQualityEntries_5148_, v_entries_5155_);
lean_dec_ref(v_entries_5155_);
v___y_4991_ = v___y_5143_;
v___y_4992_ = v___y_5144_;
v_anyFailed_4993_ = v_anyFailed_5145_;
v_anyUnlocated_4994_ = v_anyUnlocated_5146_;
v_records_4995_ = v_records_5147_;
v_codeQualityEntries_4996_ = v___x_5156_;
goto v___jp_4990_;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v_codeQualityEntries_5148_);
lean_dec_ref(v_records_5147_);
lean_dec_ref(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_del_object(v___x_4988_);
lean_dec(v_snd_4986_);
lean_dec(v_fst_4985_);
lean_del_object(v___x_4983_);
lean_del_object(v___x_4979_);
lean_del_object(v___x_4975_);
lean_del_object(v___x_4971_);
lean_dec(v___x_4938_);
v_a_5157_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5149_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5149_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
v___jp_5166_:
{
lean_object* v___x_5169_; lean_object* v_toEnvExtension_5170_; lean_object* v_asyncMode_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v_merged_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5205_; 
v___x_5169_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5170_ = lean_ctor_get(v___x_5169_, 0);
v_asyncMode_5171_ = lean_ctor_get(v_toEnvExtension_5170_, 2);
v___x_5172_ = lean_box(0);
lean_inc_ref(v___y_5167_);
v___x_5173_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5165_, v___x_5169_, v___y_5167_, v_asyncMode_5171_, v___x_5172_);
v_merged_5174_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5205_ == 0)
{
lean_object* v_unused_5206_; 
v_unused_5206_ = lean_ctor_get(v___x_5173_, 1);
lean_dec(v_unused_5206_);
v___x_5176_ = v___x_5173_;
v_isShared_5177_ = v_isSharedCheck_5205_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_merged_5174_);
lean_dec(v___x_5173_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5205_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
lean_ctor_set(v___x_5176_, 1, v_merged_5174_);
lean_ctor_set(v___x_5176_, 0, v___y_5168_);
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___y_5168_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_merged_5174_);
v___x_5179_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; 
v___x_5180_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4937_, v___x_5179_, v___y_5167_, v_a_4957_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc(v_a_5181_);
lean_dec_ref_known(v___x_5180_, 1);
switch(lean_obj_tag(v_a_5181_))
{
case 0:
{
uint8_t v___x_5182_; 
v___x_5182_ = lean_unbox(v_fst_4969_);
lean_dec(v_fst_4969_);
if (v___x_5182_ == 0)
{
uint8_t v_failed_5183_; uint8_t v___x_5184_; 
v_failed_5183_ = lean_ctor_get_uint8(v_a_5181_, 0);
lean_dec_ref_known(v_a_5181_, 0);
v___x_5184_ = lean_unbox(v_fst_4973_);
lean_dec(v_fst_4973_);
v___y_5143_ = v___y_5167_;
v___y_5144_ = v___x_5179_;
v_anyFailed_5145_ = v_failed_5183_;
v_anyUnlocated_5146_ = v___x_5184_;
v_records_5147_ = v_fst_4977_;
v_codeQualityEntries_5148_ = v_fst_4981_;
goto v___jp_5142_;
}
else
{
uint8_t v___x_5185_; 
lean_dec_ref_known(v_a_5181_, 0);
v___x_5185_ = lean_unbox(v_fst_4973_);
lean_dec(v_fst_4973_);
v___y_5143_ = v___y_5167_;
v___y_5144_ = v___x_5179_;
v_anyFailed_5145_ = v_anyUnlocated_4951_;
v_anyUnlocated_5146_ = v___x_5185_;
v_records_5147_ = v_fst_4977_;
v_codeQualityEntries_5148_ = v_fst_4981_;
goto v___jp_5142_;
}
}
case 1:
{
lean_object* v_records_5186_; uint8_t v_unlocated_5187_; lean_object* v___x_5188_; 
v_records_5186_ = lean_ctor_get(v_a_5181_, 0);
lean_inc_ref(v_records_5186_);
v_unlocated_5187_ = lean_ctor_get_uint8(v_a_5181_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5181_, 1);
v___x_5188_ = l_Array_append___redArg(v_fst_4977_, v_records_5186_);
lean_dec_ref(v_records_5186_);
if (v_unlocated_5187_ == 0)
{
uint8_t v___x_5189_; uint8_t v___x_5190_; 
v___x_5189_ = lean_unbox(v_fst_4969_);
lean_dec(v_fst_4969_);
v___x_5190_ = lean_unbox(v_fst_4973_);
lean_dec(v_fst_4973_);
v___y_5143_ = v___y_5167_;
v___y_5144_ = v___x_5179_;
v_anyFailed_5145_ = v___x_5189_;
v_anyUnlocated_5146_ = v___x_5190_;
v_records_5147_ = v___x_5188_;
v_codeQualityEntries_5148_ = v_fst_4981_;
goto v___jp_5142_;
}
else
{
uint8_t v___x_5191_; 
lean_dec(v_fst_4973_);
v___x_5191_ = lean_unbox(v_fst_4969_);
lean_dec(v_fst_4969_);
v___y_5143_ = v___y_5167_;
v___y_5144_ = v___x_5179_;
v_anyFailed_5145_ = v___x_5191_;
v_anyUnlocated_5146_ = v_anyUnlocated_4951_;
v_records_5147_ = v___x_5188_;
v_codeQualityEntries_5148_ = v_fst_4981_;
goto v___jp_5142_;
}
}
default: 
{
lean_object* v_entries_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; uint8_t v___x_5195_; 
v_entries_5192_ = lean_ctor_get(v_a_5181_, 0);
lean_inc_ref(v_entries_5192_);
lean_dec_ref_known(v_a_5181_, 1);
v___x_5193_ = l_Array_append___redArg(v_fst_4981_, v_entries_5192_);
lean_dec_ref(v_entries_5192_);
v___x_5194_ = lean_unbox(v_fst_4969_);
lean_dec(v_fst_4969_);
v___x_5195_ = lean_unbox(v_fst_4973_);
lean_dec(v_fst_4973_);
v___y_5143_ = v___y_5167_;
v___y_5144_ = v___x_5179_;
v_anyFailed_5145_ = v___x_5194_;
v_anyUnlocated_5146_ = v___x_5195_;
v_records_5147_ = v_fst_4977_;
v_codeQualityEntries_5148_ = v___x_5193_;
goto v___jp_5142_;
}
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_dec_ref(v___x_5179_);
lean_dec_ref(v___y_5167_);
lean_del_object(v___x_4988_);
lean_dec(v_snd_4986_);
lean_dec(v_fst_4985_);
lean_del_object(v___x_4983_);
lean_dec(v_fst_4981_);
lean_del_object(v___x_4979_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4975_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_dec(v___x_4938_);
v_a_5196_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5180_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5180_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
}
}
v___jp_5207_:
{
lean_object* v___x_5209_; 
v___x_5209_ = lean_compacted_region_free(v_snd_4963_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; uint32_t v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
lean_dec_ref_known(v___x_5209_, 1);
lean_inc(v_a_4957_);
v___x_5210_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5210_, 0, v_a_4957_);
lean_ctor_set_uint8(v___x_5210_, sizeof(void*)*1, v_anyFailed_4950_);
lean_ctor_set_uint8(v___x_5210_, sizeof(void*)*1 + 1, v_anyUnlocated_4951_);
lean_ctor_set_uint8(v___x_5210_, sizeof(void*)*1 + 2, v_anyFailed_4950_);
v___x_5211_ = lean_unsigned_to_nat(2u);
v___x_5212_ = lean_mk_empty_array_with_capacity(v___x_5211_);
v___x_5213_ = lean_array_push(v___x_5212_, v___x_5210_);
v___x_5214_ = lean_array_push(v___x_5213_, v_envLinterModule_4953_);
v___x_5215_ = l_Array_append___redArg(v___x_5214_, v_checkImports_4936_);
v___x_5216_ = l_Lean_Options_empty;
v___x_5217_ = 1024;
v___x_5218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5219_ = lean_box(1);
v___x_5220_ = l_Lean_importModules(v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v_anyFailed_4950_, v_anyUnlocated_4951_, v___y_5208_, v___x_5219_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; lean_object* v_linterOverrides_5222_; lean_object* v___x_5223_; uint8_t v___x_5224_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref_known(v___x_5220_, 1);
v_linterOverrides_5222_ = lean_ctor_get(v_args_4937_, 0);
v___x_5223_ = lean_array_get_size(v_linterOverrides_5222_);
v___x_5224_ = lean_nat_dec_lt(v___x_4949_, v___x_5223_);
if (v___x_5224_ == 0)
{
v___y_5167_ = v_a_5221_;
v___y_5168_ = v___x_5216_;
goto v___jp_5166_;
}
else
{
uint8_t v___x_5225_; 
v___x_5225_ = lean_nat_dec_le(v___x_5223_, v___x_5223_);
if (v___x_5225_ == 0)
{
if (v___x_5224_ == 0)
{
v___y_5167_ = v_a_5221_;
v___y_5168_ = v___x_5216_;
goto v___jp_5166_;
}
else
{
size_t v___x_5226_; size_t v___x_5227_; lean_object* v___x_5228_; 
v___x_5226_ = ((size_t)0ULL);
v___x_5227_ = lean_usize_of_nat(v___x_5223_);
v___x_5228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5222_, v___x_5226_, v___x_5227_, v___x_5216_);
v___y_5167_ = v_a_5221_;
v___y_5168_ = v___x_5228_;
goto v___jp_5166_;
}
}
else
{
size_t v___x_5229_; size_t v___x_5230_; lean_object* v___x_5231_; 
v___x_5229_ = ((size_t)0ULL);
v___x_5230_ = lean_usize_of_nat(v___x_5223_);
v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5222_, v___x_5229_, v___x_5230_, v___x_5216_);
v___y_5167_ = v_a_5221_;
v___y_5168_ = v___x_5231_;
goto v___jp_5166_;
}
}
}
else
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5239_; 
lean_del_object(v___x_4988_);
lean_dec(v_snd_4986_);
lean_dec(v_fst_4985_);
lean_del_object(v___x_4983_);
lean_dec(v_fst_4981_);
lean_del_object(v___x_4979_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4975_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_dec(v___x_4938_);
v_a_5232_ = lean_ctor_get(v___x_5220_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5234_ = v___x_5220_;
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5220_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5237_; 
if (v_isShared_5235_ == 0)
{
v___x_5237_ = v___x_5234_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5232_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
lean_del_object(v___x_4988_);
lean_dec(v_snd_4986_);
lean_dec(v_fst_4985_);
lean_del_object(v___x_4983_);
lean_dec(v_fst_4981_);
lean_del_object(v___x_4979_);
lean_dec(v_fst_4977_);
lean_del_object(v___x_4975_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_dec_ref_known(v_envLinterModule_4953_, 1);
lean_dec(v___x_4938_);
v_a_5240_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5209_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5209_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
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
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec_ref_known(v_envLinterModule_4953_, 1);
lean_dec_ref(v_b_4942_);
lean_dec(v___x_4938_);
v_a_5259_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_4960_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_4960_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref_known(v_envLinterModule_4953_, 1);
lean_dec_ref(v_b_4942_);
lean_dec(v___x_4938_);
v_a_5267_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_4958_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_4958_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
v___jp_4944_:
{
size_t v___x_4946_; size_t v___x_4947_; 
v___x_4946_ = ((size_t)1ULL);
v___x_4947_ = lean_usize_add(v_i_4941_, v___x_4946_);
v_i_4941_ = v___x_4947_;
v_b_4942_ = v_a_4945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5275_, lean_object* v_checkImports_5276_, lean_object* v_args_5277_, lean_object* v___x_5278_, lean_object* v_as_5279_, lean_object* v_sz_5280_, lean_object* v_i_5281_, lean_object* v_b_5282_, lean_object* v___y_5283_){
_start:
{
size_t v_sz_boxed_5284_; size_t v_i_boxed_5285_; lean_object* v_res_5286_; 
v_sz_boxed_5284_ = lean_unbox_usize(v_sz_5280_);
lean_dec(v_sz_5280_);
v_i_boxed_5285_ = lean_unbox_usize(v_i_5281_);
lean_dec(v_i_5281_);
v_res_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5275_, v_checkImports_5276_, v_args_5277_, v___x_5278_, v_as_5279_, v_sz_boxed_5284_, v_i_boxed_5285_, v_b_5282_);
lean_dec_ref(v_as_5279_);
lean_dec_ref(v_args_5277_);
lean_dec_ref(v_checkImports_5276_);
lean_dec(v___x_5275_);
return v_res_5286_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = l_Lean_NameSet_empty;
v___x_5288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5287_);
lean_ctor_set(v___x_5288_, 1, v___x_5287_);
return v___x_5288_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5289_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5290_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5290_);
lean_ctor_set(v___x_5291_, 1, v___x_5289_);
return v___x_5291_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5292_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5293_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
lean_ctor_set(v___x_5294_, 1, v___x_5292_);
return v___x_5294_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5296_; lean_object* v___x_5297_; 
v___x_5296_ = 0;
v___x_5297_ = lean_box_uint32(v___x_5296_);
return v___x_5297_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = 1;
v___x_5299_ = lean_box_uint32(v___x_5298_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5300_){
_start:
{
lean_object* v_mods_5302_; uint8_t v_mode_5303_; lean_object* v_checks_5304_; lean_object* v_srcSearchPath_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; uint8_t v_anyFailed_5308_; 
v_mods_5302_ = lean_ctor_get(v_args_5300_, 1);
lean_inc_ref(v_mods_5302_);
v_mode_5303_ = lean_ctor_get_uint8(v_args_5300_, sizeof(void*)*4 + 1);
v_checks_5304_ = lean_ctor_get(v_args_5300_, 2);
v_srcSearchPath_5305_ = lean_ctor_get(v_args_5300_, 3);
v___x_5306_ = lean_array_get_size(v_mods_5302_);
v___x_5307_ = lean_unsigned_to_nat(0u);
v_anyFailed_5308_ = lean_nat_dec_eq(v___x_5306_, v___x_5307_);
if (v_anyFailed_5308_ == 0)
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; size_t v_sz_5311_; size_t v___x_5312_; lean_object* v_checkImports_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; size_t v_sz_5320_; lean_object* v___x_5321_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref_known(v___x_5309_, 1);
v_sz_5311_ = lean_array_size(v_checks_5304_);
v___x_5312_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5304_);
v_checkImports_5313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5306_, v_sz_5311_, v___x_5312_, v_checks_5304_);
lean_inc(v_srcSearchPath_5305_);
v___x_5314_ = l_List_appendTR___redArg(v_srcSearchPath_5305_, v_a_5310_);
v___x_5315_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5316_ = lean_box(v_anyFailed_5308_);
v___x_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5316_);
lean_ctor_set(v___x_5317_, 1, v___x_5315_);
v___x_5318_ = lean_box(v_anyFailed_5308_);
v___x_5319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
lean_ctor_set(v___x_5319_, 1, v___x_5317_);
v_sz_5320_ = lean_array_size(v_mods_5302_);
v___x_5321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5306_, v_checkImports_5313_, v_args_5300_, v___x_5314_, v_mods_5302_, v_sz_5320_, v___x_5312_, v___x_5319_);
lean_dec_ref(v_mods_5302_);
lean_dec_ref(v_args_5300_);
lean_dec_ref(v_checkImports_5313_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5393_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5393_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5393_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
switch(v_mode_5303_)
{
case 0:
{
lean_object* v_fst_5326_; uint8_t v___x_5327_; 
v_fst_5326_ = lean_ctor_get(v_a_5322_, 0);
lean_inc(v_fst_5326_);
lean_dec(v_a_5322_);
v___x_5327_ = lean_unbox(v_fst_5326_);
lean_dec(v_fst_5326_);
if (v___x_5327_ == 0)
{
lean_object* v___x_5328_; lean_object* v___x_5330_; 
v___x_5328_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v___x_5328_);
v___x_5330_ = v___x_5324_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
else
{
lean_object* v___x_5332_; lean_object* v___x_5334_; 
v___x_5332_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v___x_5332_);
v___x_5334_ = v___x_5324_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
case 1:
{
lean_object* v_snd_5336_; lean_object* v_snd_5337_; lean_object* v_fst_5338_; lean_object* v_fst_5339_; lean_object* v___x_5340_; 
v_snd_5336_ = lean_ctor_get(v_a_5322_, 1);
lean_inc(v_snd_5336_);
lean_del_object(v___x_5324_);
lean_dec(v_a_5322_);
v_snd_5337_ = lean_ctor_get(v_snd_5336_, 1);
lean_inc(v_snd_5337_);
v_fst_5338_ = lean_ctor_get(v_snd_5336_, 0);
lean_inc(v_fst_5338_);
lean_dec(v_snd_5336_);
v_fst_5339_ = lean_ctor_get(v_snd_5337_, 0);
lean_inc(v_fst_5339_);
lean_dec(v_snd_5337_);
v___x_5340_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5339_);
lean_dec(v_fst_5339_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5353_; 
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v___x_5340_, 0);
lean_dec(v_unused_5354_);
v___x_5342_ = v___x_5340_;
v_isShared_5343_ = v_isSharedCheck_5353_;
goto v_resetjp_5341_;
}
else
{
lean_dec(v___x_5340_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5353_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
uint8_t v___x_5344_; 
v___x_5344_ = lean_unbox(v_fst_5338_);
lean_dec(v_fst_5338_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; lean_object* v___x_5347_; 
v___x_5345_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 0, v___x_5345_);
v___x_5347_ = v___x_5342_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
else
{
lean_object* v___x_5349_; lean_object* v___x_5351_; 
v___x_5349_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 0, v___x_5349_);
v___x_5351_ = v___x_5342_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
lean_dec(v_fst_5338_);
v_a_5355_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5340_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5340_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
default: 
{
lean_object* v_snd_5363_; lean_object* v_snd_5364_; lean_object* v_snd_5365_; lean_object* v_fst_5366_; lean_object* v_fst_5367_; lean_object* v___x_5368_; size_t v_sz_5369_; lean_object* v___x_5370_; 
v_snd_5363_ = lean_ctor_get(v_a_5322_, 1);
lean_del_object(v___x_5324_);
v_snd_5364_ = lean_ctor_get(v_snd_5363_, 1);
v_snd_5365_ = lean_ctor_get(v_snd_5364_, 1);
lean_inc(v_snd_5365_);
v_fst_5366_ = lean_ctor_get(v_a_5322_, 0);
lean_inc(v_fst_5366_);
lean_dec(v_a_5322_);
v_fst_5367_ = lean_ctor_get(v_snd_5365_, 0);
lean_inc(v_fst_5367_);
lean_dec(v_snd_5365_);
v___x_5368_ = lean_box(0);
v_sz_5369_ = lean_array_size(v_fst_5367_);
v___x_5370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5367_, v_sz_5369_, v___x_5312_, v___x_5368_);
lean_dec(v_fst_5367_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5383_; 
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5383_ == 0)
{
lean_object* v_unused_5384_; 
v_unused_5384_ = lean_ctor_get(v___x_5370_, 0);
lean_dec(v_unused_5384_);
v___x_5372_ = v___x_5370_;
v_isShared_5373_ = v_isSharedCheck_5383_;
goto v_resetjp_5371_;
}
else
{
lean_dec(v___x_5370_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5383_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
uint8_t v___x_5374_; 
v___x_5374_ = lean_unbox(v_fst_5366_);
lean_dec(v_fst_5366_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
v___x_5375_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 0, v___x_5375_);
v___x_5377_ = v___x_5372_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
else
{
lean_object* v___x_5379_; lean_object* v___x_5381_; 
v___x_5379_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 0, v___x_5379_);
v___x_5381_ = v___x_5372_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5379_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec(v_fst_5366_);
v_a_5385_ = lean_ctor_get(v___x_5370_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5370_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5370_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
v_a_5394_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5321_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5321_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec_ref(v_mods_5302_);
lean_dec_ref(v_args_5300_);
v_a_5402_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5309_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5309_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
else
{
lean_object* v___x_5410_; lean_object* v___x_5411_; 
lean_dec_ref(v_mods_5302_);
lean_dec_ref(v_args_5300_);
v___x_5410_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5411_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5410_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5419_; 
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; 
v_unused_5420_ = lean_ctor_get(v___x_5411_, 0);
lean_dec(v_unused_5420_);
v___x_5413_ = v___x_5411_;
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
else
{
lean_dec(v___x_5411_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5415_; lean_object* v___x_5417_; 
v___x_5415_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 0, v___x_5415_);
v___x_5417_ = v___x_5413_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5415_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
v_a_5421_ = lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5411_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5411_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Lake_BuiltinLint_run(v_args_5429_);
return v_res_5431_;
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
