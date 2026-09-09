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
v_ref_2094_ = lean_ctor_get(v___y_2046_, 4);
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
v_ref_2139_ = lean_ctor_get(v___y_2046_, 4);
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
v_ref_2164_ = lean_ctor_get(v___y_2046_, 4);
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
v_ref_2256_ = lean_ctor_get(v___y_2214_, 4);
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
v_ref_2285_ = lean_ctor_get(v___y_2214_, 4);
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
v_ref_2303_ = lean_ctor_get(v___y_2214_, 4);
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
lean_object* v___y_2419_; lean_object* v_a_2420_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2449_; lean_object* v_a_2453_; uint8_t v___y_2457_; lean_object* v_a_2458_; uint8_t v_lintOnly_2474_; uint8_t v_mode_2475_; lean_object* v___f_2476_; lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v_toCold_2485_; lean_object* v_currRecDepth_2486_; lean_object* v_ref_2487_; lean_object* v_currNamespace_2488_; lean_object* v_openDecls_2489_; lean_object* v_initHeartbeats_2490_; lean_object* v_maxHeartbeats_2491_; lean_object* v_currMacroScope_2492_; uint8_t v_suppressElabErrors_2493_; lean_object* v___y_2494_; lean_object* v___y_2523_; lean_object* v___y_2524_; uint8_t v___y_2525_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2542_; lean_object* v___y_2543_; uint8_t v___y_2544_; lean_object* v___y_2545_; uint8_t v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___y_2550_; uint8_t v___y_2551_; uint8_t v___y_2572_; 
v_lintOnly_2474_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4);
v_mode_2475_ = lean_ctor_get_uint8(v_args_2411_, sizeof(void*)*4 + 1);
v___f_2476_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2474_ == 0)
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = l_Lean_linter_doc_deferred;
v___x_2612_ = l_Lean_Linter_getLinterValue(v___x_2611_, v_linterOpts_2412_);
v___y_2572_ = v___x_2612_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2613_; lean_object* v_name_2614_; uint8_t v___x_2615_; 
v___x_2613_ = l_Lean_linter_doc_deferred;
v_name_2614_ = lean_ctor_get(v___x_2613_, 0);
v___x_2615_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2614_, v_linterOpts_2412_);
v___y_2572_ = v___x_2615_;
goto v___jp_2571_;
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
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2495_ = l_Lean_maxRecDepth;
v___x_2496_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2478_, v___x_2495_);
lean_inc_ref(v___y_2478_);
v___x_2497_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2497_, 0, v_toCold_2485_);
lean_ctor_set(v___x_2497_, 1, v___y_2478_);
lean_ctor_set(v___x_2497_, 2, v_currRecDepth_2486_);
lean_ctor_set(v___x_2497_, 3, v___x_2496_);
lean_ctor_set(v___x_2497_, 4, v_ref_2487_);
lean_ctor_set(v___x_2497_, 5, v_currNamespace_2488_);
lean_ctor_set(v___x_2497_, 6, v_openDecls_2489_);
lean_ctor_set(v___x_2497_, 7, v_initHeartbeats_2490_);
lean_ctor_set(v___x_2497_, 8, v_maxHeartbeats_2491_);
lean_ctor_set(v___x_2497_, 9, v_currMacroScope_2492_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*10, v___y_2484_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*10 + 1, v_suppressElabErrors_2493_);
v___x_2498_ = l_Lean_Doc_DeferredCheck_run(v___y_2483_, v___f_2476_, v___x_2497_, v___y_2494_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; uint8_t v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = 1;
v___x_2501_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; size_t v_sz_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v___y_2494_);
v___x_2502_ = lean_box(0);
v_sz_2503_ = lean_array_size(v_a_2499_);
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2413_, v___y_2482_, v_a_2499_, v_sz_2503_, v___x_2504_, v___x_2502_, v___x_2497_);
lean_dec_ref_known(v___x_2497_, 10);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; uint8_t v___x_2507_; 
lean_dec_ref_known(v___x_2505_, 1);
v___x_2506_ = lean_array_get_size(v_a_2499_);
lean_dec(v_a_2499_);
v___x_2507_ = lean_nat_dec_eq(v___x_2506_, v___y_2481_);
lean_dec(v___y_2481_);
if (v___x_2507_ == 0)
{
v___y_2445_ = v___y_2479_;
v___y_2446_ = v___y_2482_;
goto v___jp_2444_;
}
else
{
v___y_2445_ = v___y_2479_;
v___y_2446_ = v___x_2501_;
goto v___jp_2444_;
}
}
else
{
lean_object* v_a_2508_; 
lean_dec(v_a_2499_);
lean_dec(v___y_2481_);
lean_dec(v___y_2479_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2508_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2505_, 1);
v___y_2457_ = v___y_2482_;
v_a_2458_ = v_a_2508_;
goto v___jp_2456_;
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; size_t v_sz_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2509_ = lean_mk_empty_array_with_capacity(v___y_2481_);
lean_dec(v___y_2481_);
v___x_2510_ = lean_box(v___y_2480_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v_sz_2512_ = lean_array_size(v_a_2499_);
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2501_, v_sp_2413_, v_a_2499_, v_sz_2512_, v___x_2513_, v___x_2511_, v___x_2497_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref_known(v___x_2497_, 10);
lean_dec(v_a_2499_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v_fst_2516_; lean_object* v_snd_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_fst_2516_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_fst_2516_);
v_snd_2517_ = lean_ctor_get(v_a_2515_, 1);
lean_inc(v_snd_2517_);
lean_dec(v_a_2515_);
v___x_2518_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2518_, 0, v_fst_2516_);
v___x_2519_ = lean_unbox(v_snd_2517_);
lean_dec(v_snd_2517_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*1, v___x_2519_);
v___y_2419_ = v___y_2479_;
v_a_2420_ = v___x_2518_;
goto v___jp_2418_;
}
else
{
lean_object* v_a_2520_; 
lean_dec(v___y_2479_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
v_a_2520_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2457_ = v___y_2482_;
v_a_2458_ = v_a_2520_;
goto v___jp_2456_;
}
}
}
else
{
lean_object* v_a_2521_; 
lean_dec_ref_known(v___x_2497_, 10);
lean_dec(v___y_2494_);
lean_dec(v___y_2481_);
lean_dec(v___y_2479_);
lean_dec(v_docCheckedModules_2416_);
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v_a_2521_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2498_, 1);
v___y_2457_ = v___y_2482_;
v_a_2458_ = v_a_2521_;
goto v___jp_2456_;
}
}
v___jp_2522_:
{
lean_object* v_toCold_2532_; lean_object* v_currRecDepth_2533_; lean_object* v_ref_2534_; lean_object* v_currNamespace_2535_; lean_object* v_openDecls_2536_; lean_object* v_initHeartbeats_2537_; lean_object* v_maxHeartbeats_2538_; lean_object* v_currMacroScope_2539_; uint8_t v_suppressElabErrors_2540_; 
v_toCold_2532_ = lean_ctor_get(v___y_2530_, 0);
lean_inc_ref(v_toCold_2532_);
v_currRecDepth_2533_ = lean_ctor_get(v___y_2530_, 2);
lean_inc(v_currRecDepth_2533_);
v_ref_2534_ = lean_ctor_get(v___y_2530_, 4);
lean_inc(v_ref_2534_);
v_currNamespace_2535_ = lean_ctor_get(v___y_2530_, 5);
lean_inc(v_currNamespace_2535_);
v_openDecls_2536_ = lean_ctor_get(v___y_2530_, 6);
lean_inc(v_openDecls_2536_);
v_initHeartbeats_2537_ = lean_ctor_get(v___y_2530_, 7);
lean_inc(v_initHeartbeats_2537_);
v_maxHeartbeats_2538_ = lean_ctor_get(v___y_2530_, 8);
lean_inc(v_maxHeartbeats_2538_);
v_currMacroScope_2539_ = lean_ctor_get(v___y_2530_, 9);
lean_inc(v_currMacroScope_2539_);
v_suppressElabErrors_2540_ = lean_ctor_get_uint8(v___y_2530_, sizeof(void*)*10 + 1);
lean_dec_ref(v___y_2530_);
v___y_2478_ = v___y_2523_;
v___y_2479_ = v___y_2524_;
v___y_2480_ = v___y_2525_;
v___y_2481_ = v___y_2526_;
v___y_2482_ = v___y_2527_;
v___y_2483_ = v___y_2528_;
v___y_2484_ = v___y_2529_;
v_toCold_2485_ = v_toCold_2532_;
v_currRecDepth_2486_ = v_currRecDepth_2533_;
v_ref_2487_ = v_ref_2534_;
v_currNamespace_2488_ = v_currNamespace_2535_;
v_openDecls_2489_ = v_openDecls_2536_;
v_initHeartbeats_2490_ = v_initHeartbeats_2537_;
v_maxHeartbeats_2491_ = v_maxHeartbeats_2538_;
v_currMacroScope_2492_ = v_currMacroScope_2539_;
v_suppressElabErrors_2493_ = v_suppressElabErrors_2540_;
v___y_2494_ = v___y_2531_;
goto v___jp_2477_;
}
v___jp_2541_:
{
if (v___y_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v_env_2553_; lean_object* v_nextMacroScope_2554_; lean_object* v_ngen_2555_; lean_object* v_auxDeclNGen_2556_; lean_object* v_traceState_2557_; lean_object* v_messages_2558_; lean_object* v_infoState_2559_; lean_object* v_snapshotTasks_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
v___x_2552_ = lean_st_ref_take(v___y_2543_);
v_env_2553_ = lean_ctor_get(v___x_2552_, 0);
v_nextMacroScope_2554_ = lean_ctor_get(v___x_2552_, 1);
v_ngen_2555_ = lean_ctor_get(v___x_2552_, 2);
v_auxDeclNGen_2556_ = lean_ctor_get(v___x_2552_, 3);
v_traceState_2557_ = lean_ctor_get(v___x_2552_, 4);
v_messages_2558_ = lean_ctor_get(v___x_2552_, 6);
v_infoState_2559_ = lean_ctor_get(v___x_2552_, 7);
v_snapshotTasks_2560_ = lean_ctor_get(v___x_2552_, 8);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v___x_2552_, 5);
lean_dec(v_unused_2570_);
v___x_2562_ = v___x_2552_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snapshotTasks_2560_);
lean_inc(v_infoState_2559_);
lean_inc(v_messages_2558_);
lean_inc(v_traceState_2557_);
lean_inc(v_auxDeclNGen_2556_);
lean_inc(v_ngen_2555_);
lean_inc(v_nextMacroScope_2554_);
lean_inc(v_env_2553_);
lean_dec(v___x_2552_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_Kernel_enableDiag(v_env_2553_, v___y_2550_);
lean_inc_ref(v___y_2548_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 5, v___y_2548_);
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_nextMacroScope_2554_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_ngen_2555_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v_auxDeclNGen_2556_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_traceState_2557_);
lean_ctor_set(v_reuseFailAlloc_2568_, 5, v___y_2548_);
lean_ctor_set(v_reuseFailAlloc_2568_, 6, v_messages_2558_);
lean_ctor_set(v_reuseFailAlloc_2568_, 7, v_infoState_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 8, v_snapshotTasks_2560_);
v___x_2566_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_st_ref_put(v___y_2543_, v___x_2566_);
lean_inc(v___y_2543_);
v___y_2523_ = v___y_2542_;
v___y_2524_ = v___y_2543_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2545_;
v___y_2527_ = v___y_2544_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2550_;
v___y_2530_ = v___y_2547_;
v___y_2531_ = v___y_2543_;
goto v___jp_2522_;
}
}
}
else
{
lean_inc(v___y_2543_);
v___y_2523_ = v___y_2542_;
v___y_2524_ = v___y_2543_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2545_;
v___y_2527_ = v___y_2544_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2550_;
v___y_2530_ = v___y_2547_;
v___y_2531_ = v___y_2543_;
goto v___jp_2522_;
}
}
v___jp_2571_:
{
if (v___y_2572_ == 0)
{
uint8_t v___x_2573_; uint8_t v___x_2574_; 
lean_dec(v_pkgRoot_2415_);
lean_dec_ref(v_env_2414_);
lean_dec(v_sp_2413_);
v___x_2573_ = 1;
v___x_2574_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2475_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2575_, 0, v___x_2574_);
v___y_2449_ = v___x_2575_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2577_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*1, v___y_2572_);
v___y_2449_ = v___x_2577_;
goto v___jp_2448_;
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_env_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; uint8_t v___x_2609_; uint8_t v___x_2610_; 
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2580_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2581_ = lean_io_get_num_heartbeats();
v___x_2582_ = l_Lean_firstFrontendMacroScope;
v___x_2583_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2584_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_box(0);
v___x_2587_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2588_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2589_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2590_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2414_);
v___x_2591_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2591_, 0, v_env_2414_);
lean_ctor_set(v___x_2591_, 1, v___x_2583_);
lean_ctor_set(v___x_2591_, 2, v___x_2584_);
lean_ctor_set(v___x_2591_, 3, v___x_2587_);
lean_ctor_set(v___x_2591_, 4, v___x_2588_);
lean_ctor_set(v___x_2591_, 5, v___x_2579_);
lean_ctor_set(v___x_2591_, 6, v___x_2580_);
lean_ctor_set(v___x_2591_, 7, v___x_2589_);
lean_ctor_set(v___x_2591_, 8, v___x_2590_);
v___x_2592_ = lean_st_mk_ref(v___x_2591_);
v___x_2593_ = l_Lean_inheritedTraceOptions;
v___x_2594_ = lean_st_ref_get(v___x_2593_);
v___x_2595_ = lean_st_ref_get(v___x_2592_);
v___x_2596_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2597_ = l_Lean_instInhabitedFileMap_default;
v___x_2598_ = lean_box(0);
v___x_2599_ = l_Lean_Options_empty;
v___x_2600_ = lean_unsigned_to_nat(1000u);
v___x_2601_ = lean_box(0);
v___x_2602_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2603_ = 0;
v___x_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2596_);
lean_ctor_set(v___x_2604_, 1, v___x_2597_);
lean_ctor_set(v___x_2604_, 2, v___x_2585_);
lean_ctor_set(v___x_2604_, 3, v___x_2598_);
lean_ctor_set(v___x_2604_, 4, v___x_2594_);
lean_inc(v___x_2581_);
lean_inc_ref(v___x_2604_);
v___x_2605_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___x_2599_);
lean_ctor_set(v___x_2605_, 2, v___x_2578_);
lean_ctor_set(v___x_2605_, 3, v___x_2600_);
lean_ctor_set(v___x_2605_, 4, v___x_2601_);
lean_ctor_set(v___x_2605_, 5, v___x_2585_);
lean_ctor_set(v___x_2605_, 6, v___x_2586_);
lean_ctor_set(v___x_2605_, 7, v___x_2581_);
lean_ctor_set(v___x_2605_, 8, v___x_2602_);
lean_ctor_set(v___x_2605_, 9, v___x_2582_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*10, v___x_2603_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*10 + 1, v___x_2603_);
v_env_2606_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_env_2606_);
lean_dec(v___x_2595_);
v___x_2607_ = lean_box(v___y_2572_);
lean_inc(v_docCheckedModules_2416_);
lean_inc(v_pkgRoot_2415_);
v___f_2608_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2608_, 0, v_pkgRoot_2415_);
lean_closure_set(v___f_2608_, 1, v_docCheckedModules_2416_);
lean_closure_set(v___f_2608_, 2, v___x_2607_);
v___x_2609_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2610_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2606_);
lean_dec_ref(v_env_2606_);
if (v___x_2609_ == 0)
{
if (v___x_2610_ == 0)
{
lean_dec_ref_known(v___x_2605_, 10);
lean_inc(v___x_2592_);
v___y_2478_ = v___x_2599_;
v___y_2479_ = v___x_2592_;
v___y_2480_ = v___x_2603_;
v___y_2481_ = v___x_2578_;
v___y_2482_ = v___y_2572_;
v___y_2483_ = v___f_2608_;
v___y_2484_ = v___x_2609_;
v_toCold_2485_ = v___x_2604_;
v_currRecDepth_2486_ = v___x_2578_;
v_ref_2487_ = v___x_2601_;
v_currNamespace_2488_ = v___x_2585_;
v_openDecls_2489_ = v___x_2586_;
v_initHeartbeats_2490_ = v___x_2581_;
v_maxHeartbeats_2491_ = v___x_2602_;
v_currMacroScope_2492_ = v___x_2582_;
v_suppressElabErrors_2493_ = v___x_2603_;
v___y_2494_ = v___x_2592_;
goto v___jp_2477_;
}
else
{
lean_dec_ref_known(v___x_2604_, 5);
lean_dec(v___x_2581_);
v___y_2542_ = v___x_2599_;
v___y_2543_ = v___x_2592_;
v___y_2544_ = v___y_2572_;
v___y_2545_ = v___x_2578_;
v___y_2546_ = v___x_2603_;
v___y_2547_ = v___x_2605_;
v___y_2548_ = v___x_2579_;
v___y_2549_ = v___f_2608_;
v___y_2550_ = v___x_2609_;
v___y_2551_ = v___x_2609_;
goto v___jp_2541_;
}
}
else
{
lean_dec_ref_known(v___x_2604_, 5);
lean_dec(v___x_2581_);
v___y_2542_ = v___x_2599_;
v___y_2543_ = v___x_2592_;
v___y_2544_ = v___y_2572_;
v___y_2545_ = v___x_2578_;
v___y_2546_ = v___x_2603_;
v___y_2547_ = v___x_2605_;
v___y_2548_ = v___x_2579_;
v___y_2549_ = v___f_2608_;
v___y_2550_ = v___x_2609_;
v___y_2551_ = v___x_2610_;
goto v___jp_2541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2616_, lean_object* v_linterOpts_2617_, lean_object* v_sp_2618_, lean_object* v_env_2619_, lean_object* v_pkgRoot_2620_, lean_object* v_docCheckedModules_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2616_, v_linterOpts_2617_, v_sp_2618_, v_env_2619_, v_pkgRoot_2620_, v_docCheckedModules_2621_);
lean_dec_ref(v_linterOpts_2617_);
lean_dec_ref(v_args_2616_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2624_, uint8_t v___y_2625_, lean_object* v_as_2626_, size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2624_, v___y_2625_, v_as_2626_, v_sz_2627_, v_i_2628_, v_b_2629_, v___y_2630_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2634_, lean_object* v___y_2635_, lean_object* v_as_2636_, lean_object* v_sz_2637_, lean_object* v_i_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___y_8064__boxed_2643_; size_t v_sz_boxed_2644_; size_t v_i_boxed_2645_; lean_object* v_res_2646_; 
v___y_8064__boxed_2643_ = lean_unbox(v___y_2635_);
v_sz_boxed_2644_ = lean_unbox_usize(v_sz_2637_);
lean_dec(v_sz_2637_);
v_i_boxed_2645_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2634_, v___y_8064__boxed_2643_, v_as_2636_, v_sz_boxed_2644_, v_i_boxed_2645_, v_b_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v_as_2636_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2647_, lean_object* v_as_2648_, size_t v_i_2649_, size_t v_stop_2650_, lean_object* v_b_2651_){
_start:
{
lean_object* v___y_2653_; uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_eq(v_i_2649_, v_stop_2650_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v_linter_2659_; uint8_t v___x_2660_; 
v___x_2658_ = lean_array_uget_borrowed(v_as_2648_, v_i_2649_);
v_linter_2659_ = lean_ctor_get(v___x_2658_, 0);
v___x_2660_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2659_, v_linterOpts_2647_);
if (v___x_2660_ == 0)
{
v___y_2653_ = v_b_2651_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2661_; 
lean_inc(v___x_2658_);
v___x_2661_ = lean_array_push(v_b_2651_, v___x_2658_);
v___y_2653_ = v___x_2661_;
goto v___jp_2652_;
}
}
else
{
return v_b_2651_;
}
v___jp_2652_:
{
size_t v___x_2654_; size_t v___x_2655_; 
v___x_2654_ = ((size_t)1ULL);
v___x_2655_ = lean_usize_add(v_i_2649_, v___x_2654_);
v_i_2649_ = v___x_2655_;
v_b_2651_ = v___y_2653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2662_, lean_object* v_as_2663_, lean_object* v_i_2664_, lean_object* v_stop_2665_, lean_object* v_b_2666_){
_start:
{
size_t v_i_boxed_2667_; size_t v_stop_boxed_2668_; lean_object* v_res_2669_; 
v_i_boxed_2667_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_stop_boxed_2668_ = lean_unbox_usize(v_stop_2665_);
lean_dec(v_stop_2665_);
v_res_2669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2662_, v_as_2663_, v_i_boxed_2667_, v_stop_boxed_2668_, v_b_2666_);
lean_dec_ref(v_as_2663_);
lean_dec_ref(v_linterOpts_2662_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2672_, lean_object* v_as_2673_, size_t v_i_2674_, size_t v_stop_2675_, lean_object* v_b_2676_){
_start:
{
lean_object* v___y_2678_; uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_eq(v_i_2674_, v_stop_2675_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v_fst_2684_; lean_object* v_snd_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2709_; 
v___x_2683_ = lean_array_uget(v_as_2673_, v_i_2674_);
v_fst_2684_ = lean_ctor_get(v___x_2683_, 0);
v_snd_2685_ = lean_ctor_get(v___x_2683_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2687_ = v___x_2683_;
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2685_);
lean_inc(v_fst_2684_);
lean_dec(v___x_2683_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___y_2690_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_array_get_size(v_snd_2685_);
v___x_2700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2701_ = lean_nat_dec_lt(v___x_2698_, v___x_2699_);
if (v___x_2701_ == 0)
{
lean_dec(v_snd_2685_);
v___y_2690_ = v___x_2700_;
goto v___jp_2689_;
}
else
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_nat_dec_le(v___x_2699_, v___x_2699_);
if (v___x_2702_ == 0)
{
if (v___x_2701_ == 0)
{
lean_dec(v_snd_2685_);
v___y_2690_ = v___x_2700_;
goto v___jp_2689_;
}
else
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = ((size_t)0ULL);
v___x_2704_ = lean_usize_of_nat(v___x_2699_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2672_, v_snd_2685_, v___x_2703_, v___x_2704_, v___x_2700_);
lean_dec(v_snd_2685_);
v___y_2690_ = v___x_2705_;
goto v___jp_2689_;
}
}
else
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = lean_usize_of_nat(v___x_2699_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2672_, v_snd_2685_, v___x_2706_, v___x_2707_, v___x_2700_);
lean_dec(v_snd_2685_);
v___y_2690_ = v___x_2708_;
goto v___jp_2689_;
}
}
v___jp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2691_ = lean_array_get_size(v___y_2690_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_nat_dec_eq(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2695_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___y_2690_);
v___x_2695_ = v___x_2687_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_fst_2684_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___y_2690_);
v___x_2695_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_array_push(v_b_2676_, v___x_2695_);
v___y_2678_ = v___x_2696_;
goto v___jp_2677_;
}
}
else
{
lean_dec_ref(v___y_2690_);
lean_del_object(v___x_2687_);
lean_dec(v_fst_2684_);
v___y_2678_ = v_b_2676_;
goto v___jp_2677_;
}
}
}
}
else
{
return v_b_2676_;
}
v___jp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2674_, v___x_2679_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___y_2678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2710_, lean_object* v_as_2711_, lean_object* v_i_2712_, lean_object* v_stop_2713_, lean_object* v_b_2714_){
_start:
{
size_t v_i_boxed_2715_; size_t v_stop_boxed_2716_; lean_object* v_res_2717_; 
v_i_boxed_2715_ = lean_unbox_usize(v_i_2712_);
lean_dec(v_i_2712_);
v_stop_boxed_2716_ = lean_unbox_usize(v_stop_2713_);
lean_dec(v_stop_2713_);
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2710_, v_as_2711_, v_i_boxed_2715_, v_stop_boxed_2716_, v_b_2714_);
lean_dec_ref(v_as_2711_);
lean_dec_ref(v_linterOpts_2710_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2718_, lean_object* v_as_2719_, lean_object* v_start_2720_, lean_object* v_stop_2721_){
_start:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2723_ = lean_nat_dec_lt(v_start_2720_, v_stop_2721_);
if (v___x_2723_ == 0)
{
return v___x_2722_;
}
else
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = lean_array_get_size(v_as_2719_);
v___x_2725_ = lean_nat_dec_le(v_stop_2721_, v___x_2724_);
if (v___x_2725_ == 0)
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_nat_dec_lt(v_start_2720_, v___x_2724_);
if (v___x_2726_ == 0)
{
return v___x_2722_;
}
else
{
size_t v___x_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_usize_of_nat(v_start_2720_);
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2718_, v_as_2719_, v___x_2727_, v___x_2728_, v___x_2722_);
return v___x_2729_;
}
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_usize_of_nat(v_start_2720_);
v___x_2731_ = lean_usize_of_nat(v_stop_2721_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2718_, v_as_2719_, v___x_2730_, v___x_2731_, v___x_2722_);
return v___x_2732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2733_, lean_object* v_as_2734_, lean_object* v_start_2735_, lean_object* v_stop_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2733_, v_as_2734_, v_start_2735_, v_stop_2736_);
lean_dec(v_stop_2736_);
lean_dec(v_start_2735_);
lean_dec_ref(v_as_2734_);
lean_dec_ref(v_linterOpts_2733_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2738_, lean_object* v_init_2739_, lean_object* v_x_2740_){
_start:
{
if (lean_obj_tag(v_x_2740_) == 0)
{
lean_object* v_k_2742_; lean_object* v_v_2743_; lean_object* v_l_2744_; lean_object* v_r_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2762_; 
v_k_2742_ = lean_ctor_get(v_x_2740_, 1);
lean_inc(v_k_2742_);
v_v_2743_ = lean_ctor_get(v_x_2740_, 2);
lean_inc(v_v_2743_);
v_l_2744_ = lean_ctor_get(v_x_2740_, 3);
lean_inc(v_l_2744_);
v_r_2745_ = lean_ctor_get(v_x_2740_, 4);
lean_inc(v_r_2745_);
lean_dec_ref_known(v_x_2740_, 5);
lean_inc(v_fst_2738_);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2738_, v_init_2739_, v_l_2744_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v_a_2748_ = lean_ctor_get(v_a_2747_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2750_ = v_a_2747_;
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v_a_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
uint8_t v_anyUnlocated_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v_anyUnlocated_2752_ = 1;
v___x_2753_ = l_Lean_Name_toString(v_k_2742_, v_anyUnlocated_2752_);
lean_inc(v_fst_2738_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 0);
lean_ctor_set(v___x_2750_, 0, v_fst_2738_);
v___x_2755_ = v___x_2750_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_fst_2738_);
v___x_2755_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
double v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2756_ = lean_float_of_nat(v_v_2743_);
v___x_2757_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2757_, 0, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2753_);
lean_ctor_set(v___x_2758_, 1, v___x_2755_);
lean_ctor_set(v___x_2758_, 2, v___x_2757_);
v___x_2759_ = lean_array_push(v_a_2748_, v___x_2758_);
v_init_2739_ = v___x_2759_;
v_x_2740_ = v_r_2745_;
goto _start;
}
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_fst_2738_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_init_2739_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2765_, lean_object* v_init_2766_, lean_object* v_x_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2765_, v_init_2766_, v_x_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2770_, lean_object* v_k_2771_, lean_object* v_fallback_2772_){
_start:
{
if (lean_obj_tag(v_t_2770_) == 0)
{
lean_object* v_k_2773_; lean_object* v_v_2774_; lean_object* v_l_2775_; lean_object* v_r_2776_; uint8_t v___x_2777_; 
v_k_2773_ = lean_ctor_get(v_t_2770_, 1);
v_v_2774_ = lean_ctor_get(v_t_2770_, 2);
v_l_2775_ = lean_ctor_get(v_t_2770_, 3);
v_r_2776_ = lean_ctor_get(v_t_2770_, 4);
v___x_2777_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2771_, v_k_2773_);
switch(v___x_2777_)
{
case 0:
{
v_t_2770_ = v_l_2775_;
goto _start;
}
case 1:
{
lean_inc(v_v_2774_);
return v_v_2774_;
}
default: 
{
v_t_2770_ = v_r_2776_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2772_);
return v_fallback_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2780_, lean_object* v_k_2781_, lean_object* v_fallback_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2780_, v_k_2781_, v_fallback_2782_);
lean_dec(v_fallback_2782_);
lean_dec(v_k_2781_);
lean_dec(v_t_2780_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2784_, size_t v_i_2785_, size_t v_stop_2786_, lean_object* v_b_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_eq(v_i_2785_, v_stop_2786_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v_linter_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; 
v___x_2789_ = lean_array_uget_borrowed(v_as_2784_, v_i_2785_);
v_linter_2790_ = lean_ctor_get(v___x_2789_, 0);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2787_, v_linter_2790_, v___x_2791_);
v___x_2793_ = lean_unsigned_to_nat(1u);
v___x_2794_ = lean_nat_add(v___x_2792_, v___x_2793_);
lean_dec(v___x_2792_);
lean_inc(v_linter_2790_);
v___x_2795_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2790_, v___x_2794_, v_b_2787_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2785_, v___x_2796_);
v_i_2785_ = v___x_2797_;
v_b_2787_ = v___x_2795_;
goto _start;
}
else
{
return v_b_2787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2799_, lean_object* v_i_2800_, lean_object* v_stop_2801_, lean_object* v_b_2802_){
_start:
{
size_t v_i_boxed_2803_; size_t v_stop_boxed_2804_; lean_object* v_res_2805_; 
v_i_boxed_2803_ = lean_unbox_usize(v_i_2800_);
lean_dec(v_i_2800_);
v_stop_boxed_2804_ = lean_unbox_usize(v_stop_2801_);
lean_dec(v_stop_2801_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2799_, v_i_boxed_2803_, v_stop_boxed_2804_, v_b_2802_);
lean_dec_ref(v_as_2799_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2806_, size_t v_sz_2807_, size_t v_i_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v_a_2812_; uint8_t v___x_2816_; 
v___x_2816_ = lean_usize_dec_lt(v_i_2808_, v_sz_2807_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_b_2809_);
return v___x_2817_;
}
else
{
lean_object* v_a_2818_; lean_object* v_fst_2819_; lean_object* v_snd_2820_; lean_object* v___y_2822_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v_a_2818_ = lean_array_uget_borrowed(v_as_2806_, v_i_2808_);
v_fst_2819_ = lean_ctor_get(v_a_2818_, 0);
v_snd_2820_ = lean_ctor_get(v_a_2818_, 1);
v___x_2844_ = lean_box(1);
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_array_get_size(v_snd_2820_);
v___x_2847_ = lean_nat_dec_lt(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
v___y_2822_ = v___x_2844_;
goto v___jp_2821_;
}
else
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_nat_dec_le(v___x_2846_, v___x_2846_);
if (v___x_2848_ == 0)
{
if (v___x_2847_ == 0)
{
v___y_2822_ = v___x_2844_;
goto v___jp_2821_;
}
else
{
size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = lean_usize_of_nat(v___x_2846_);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2820_, v___x_2849_, v___x_2850_, v___x_2844_);
v___y_2822_ = v___x_2851_;
goto v___jp_2821_;
}
}
else
{
size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = ((size_t)0ULL);
v___x_2853_ = lean_usize_of_nat(v___x_2846_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2820_, v___x_2852_, v___x_2853_, v___x_2844_);
v___y_2822_ = v___x_2854_;
goto v___jp_2821_;
}
}
v___jp_2821_:
{
lean_object* v___x_2823_; 
lean_inc(v_fst_2819_);
v___x_2823_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2819_, v_b_2809_, v___y_2822_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v_a_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v_a_2825_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_a_2825_);
lean_dec(v_a_2824_);
v_a_2812_ = v_a_2825_;
goto v___jp_2811_;
}
else
{
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2835_; 
v_a_2826_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2828_ = v___x_2823_;
v_isShared_2829_ = v_isSharedCheck_2835_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2823_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2835_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
if (lean_obj_tag(v_a_2826_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v_a_2826_, 1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v_a_2834_; 
lean_del_object(v___x_2828_);
v_a_2834_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v_a_2826_, 1);
v_a_2812_ = v_a_2834_;
goto v___jp_2811_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2823_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2823_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
}
v___jp_2811_:
{
size_t v___x_2813_; size_t v___x_2814_; 
v___x_2813_ = ((size_t)1ULL);
v___x_2814_ = lean_usize_add(v_i_2808_, v___x_2813_);
v_i_2808_ = v___x_2814_;
v_b_2809_ = v_a_2812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2855_, lean_object* v_sz_2856_, lean_object* v_i_2857_, lean_object* v_b_2858_, lean_object* v___y_2859_){
_start:
{
size_t v_sz_boxed_2860_; size_t v_i_boxed_2861_; lean_object* v_res_2862_; 
v_sz_boxed_2860_ = lean_unbox_usize(v_sz_2856_);
lean_dec(v_sz_2856_);
v_i_boxed_2861_ = lean_unbox_usize(v_i_2857_);
lean_dec(v_i_2857_);
v_res_2862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2855_, v_sz_boxed_2860_, v_i_boxed_2861_, v_b_2858_);
lean_dec_ref(v_as_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2866_, lean_object* v_as_2867_, size_t v_sz_2868_, size_t v_i_2869_, lean_object* v_b_2870_){
_start:
{
lean_object* v_a_2873_; uint8_t v_anyUnlocated_2877_; 
v_anyUnlocated_2877_ = lean_usize_dec_lt(v_i_2869_, v_sz_2868_);
if (v_anyUnlocated_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec(v_fst_2866_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_b_2870_);
return v___x_2878_;
}
else
{
lean_object* v_fst_2879_; lean_object* v_snd_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2917_; 
v_fst_2879_ = lean_ctor_get(v_b_2870_, 0);
v_snd_2880_ = lean_ctor_get(v_b_2870_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_b_2870_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2882_ = v_b_2870_;
v_isShared_2883_ = v_isSharedCheck_2917_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_snd_2880_);
lean_inc(v_fst_2879_);
lean_dec(v_b_2870_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2917_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_a_2884_; lean_object* v_position_x3f_2885_; 
v_a_2884_ = lean_array_uget_borrowed(v_as_2867_, v_i_2869_);
v_position_x3f_2885_ = lean_ctor_get(v_a_2884_, 2);
if (lean_obj_tag(v_position_x3f_2885_) == 0)
{
lean_object* v_linter_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec(v_snd_2880_);
v_linter_2886_ = lean_ctor_get(v_a_2884_, 0);
v___x_2887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2886_);
v___x_2888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2886_, v_anyUnlocated_2877_);
v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
lean_inc(v_fst_2866_);
v___x_2892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2866_, v_anyUnlocated_2877_);
v___x_2893_ = lean_string_append(v___x_2891_, v___x_2892_);
lean_dec_ref(v___x_2892_);
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2895_ = lean_string_append(v___x_2893_, v___x_2894_);
v___x_2896_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_dec_ref_known(v___x_2896_, 1);
v___x_2897_ = lean_box(v_anyUnlocated_2877_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2897_);
v___x_2899_ = v___x_2882_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_fst_2879_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2873_ = v___x_2899_;
goto v___jp_2872_;
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2882_);
lean_dec(v_fst_2879_);
lean_dec(v_fst_2866_);
v_a_2901_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2896_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2896_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_linter_2909_; lean_object* v_file_2910_; lean_object* v_val_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v_linter_2909_ = lean_ctor_get(v_a_2884_, 0);
v_file_2910_ = lean_ctor_get(v_a_2884_, 3);
v_val_2911_ = lean_ctor_get(v_position_x3f_2885_, 0);
lean_inc(v_linter_2909_);
lean_inc(v_val_2911_);
lean_inc_ref(v_file_2910_);
v___x_2912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2912_, 0, v_file_2910_);
lean_ctor_set(v___x_2912_, 1, v_val_2911_);
lean_ctor_set(v___x_2912_, 2, v_linter_2909_);
v___x_2913_ = lean_array_push(v_fst_2879_, v___x_2912_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2913_);
v___x_2915_ = v___x_2882_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_snd_2880_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v_a_2873_ = v___x_2915_;
goto v___jp_2872_;
}
}
}
}
v___jp_2872_:
{
size_t v___x_2874_; size_t v___x_2875_; 
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2869_, v___x_2874_);
v_i_2869_ = v___x_2875_;
v_b_2870_ = v_a_2873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2918_, lean_object* v_as_2919_, lean_object* v_sz_2920_, lean_object* v_i_2921_, lean_object* v_b_2922_, lean_object* v___y_2923_){
_start:
{
size_t v_sz_boxed_2924_; size_t v_i_boxed_2925_; lean_object* v_res_2926_; 
v_sz_boxed_2924_ = lean_unbox_usize(v_sz_2920_);
lean_dec(v_sz_2920_);
v_i_boxed_2925_ = lean_unbox_usize(v_i_2921_);
lean_dec(v_i_2921_);
v_res_2926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2918_, v_as_2919_, v_sz_boxed_2924_, v_i_boxed_2925_, v_b_2922_);
lean_dec_ref(v_as_2919_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2927_, size_t v_sz_2928_, size_t v_i_2929_, lean_object* v_b_2930_){
_start:
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_usize_dec_lt(v_i_2929_, v_sz_2928_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_b_2930_);
return v___x_2933_;
}
else
{
lean_object* v_a_2934_; lean_object* v_fst_2935_; lean_object* v_snd_2936_; lean_object* v_fst_2937_; lean_object* v_snd_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2961_; 
v_a_2934_ = lean_array_uget_borrowed(v_as_2927_, v_i_2929_);
v_fst_2935_ = lean_ctor_get(v_a_2934_, 0);
v_snd_2936_ = lean_ctor_get(v_a_2934_, 1);
v_fst_2937_ = lean_ctor_get(v_b_2930_, 0);
v_snd_2938_ = lean_ctor_get(v_b_2930_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_b_2930_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2940_ = v_b_2930_;
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_snd_2938_);
lean_inc(v_fst_2937_);
lean_dec(v_b_2930_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2961_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_snd_2938_);
v___x_2943_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
size_t v_sz_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v_sz_2944_ = lean_array_size(v_snd_2936_);
v___x_2945_ = ((size_t)0ULL);
lean_inc(v_fst_2935_);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2935_, v_snd_2936_, v_sz_2944_, v___x_2945_, v___x_2943_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2959_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v_fst_2948_ = lean_ctor_get(v_a_2947_, 0);
v_snd_2949_ = lean_ctor_get(v_a_2947_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2951_ = v_a_2947_;
v_isShared_2952_ = v_isSharedCheck_2959_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snd_2949_);
lean_inc(v_fst_2948_);
lean_dec(v_a_2947_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2959_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_fst_2948_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_snd_2949_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
size_t v___x_2955_; size_t v___x_2956_; 
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2929_, v___x_2955_);
v_i_2929_ = v___x_2956_;
v_b_2930_ = v___x_2954_;
goto _start;
}
}
}
else
{
return v___x_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2962_, lean_object* v_sz_2963_, lean_object* v_i_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_){
_start:
{
size_t v_sz_boxed_2967_; size_t v_i_boxed_2968_; lean_object* v_res_2969_; 
v_sz_boxed_2967_ = lean_unbox_usize(v_sz_2963_);
lean_dec(v_sz_2963_);
v_i_boxed_2968_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2962_, v_sz_boxed_2967_, v_i_boxed_2968_, v_b_2965_);
lean_dec_ref(v_as_2962_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2970_, size_t v_sz_2971_, size_t v_i_2972_, lean_object* v_b_2973_){
_start:
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_usize_dec_lt(v_i_2972_, v_sz_2971_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_b_2973_);
return v___x_2976_;
}
else
{
lean_object* v_a_2977_; lean_object* v_message_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_a_2977_ = lean_array_uget_borrowed(v_as_2970_, v_i_2972_);
v_message_2978_ = lean_ctor_get(v_a_2977_, 1);
v___x_2979_ = 0;
lean_inc_ref(v_message_2978_);
v___x_2980_ = l_Lean_SerialMessage_toString(v_message_2978_, v___x_2979_);
v___x_2981_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2982_; size_t v___x_2983_; size_t v___x_2984_; 
lean_dec_ref_known(v___x_2981_, 1);
v___x_2982_ = lean_box(0);
v___x_2983_ = ((size_t)1ULL);
v___x_2984_ = lean_usize_add(v_i_2972_, v___x_2983_);
v_i_2972_ = v___x_2984_;
v_b_2973_ = v___x_2982_;
goto _start;
}
else
{
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2986_, lean_object* v_sz_2987_, lean_object* v_i_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_){
_start:
{
size_t v_sz_boxed_2991_; size_t v_i_boxed_2992_; lean_object* v_res_2993_; 
v_sz_boxed_2991_ = lean_unbox_usize(v_sz_2987_);
lean_dec(v_sz_2987_);
v_i_boxed_2992_ = lean_unbox_usize(v_i_2988_);
lean_dec(v_i_2988_);
v_res_2993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2986_, v_sz_boxed_2991_, v_i_boxed_2992_, v_b_2989_);
lean_dec_ref(v_as_2986_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2996_, size_t v_sz_2997_, size_t v_i_2998_, lean_object* v_b_2999_){
_start:
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_usize_dec_lt(v_i_2998_, v_sz_2997_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_b_2999_);
return v___x_3002_;
}
else
{
lean_object* v_a_3003_; lean_object* v_fst_3004_; lean_object* v_snd_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_a_3003_ = lean_array_uget_borrowed(v_as_2996_, v_i_2998_);
v_fst_3004_ = lean_ctor_get(v_a_3003_, 0);
v_snd_3005_ = lean_ctor_get(v_a_3003_, 1);
v___x_3006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3004_);
v___x_3007_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3004_, v___x_3001_);
v___x_3008_ = lean_string_append(v___x_3006_, v___x_3007_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3010_ = lean_string_append(v___x_3008_, v___x_3009_);
v___x_3011_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v___x_3012_; size_t v_sz_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref_known(v___x_3011_, 1);
v___x_3012_ = lean_box(0);
v_sz_3013_ = lean_array_size(v_snd_3005_);
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3005_, v_sz_3013_, v___x_3014_, v___x_3012_);
if (lean_obj_tag(v___x_3015_) == 0)
{
size_t v___x_3016_; size_t v___x_3017_; 
lean_dec_ref_known(v___x_3015_, 1);
v___x_3016_ = ((size_t)1ULL);
v___x_3017_ = lean_usize_add(v_i_2998_, v___x_3016_);
v_i_2998_ = v___x_3017_;
v_b_2999_ = v___x_3012_;
goto _start;
}
else
{
return v___x_3015_;
}
}
else
{
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3019_, lean_object* v_sz_3020_, lean_object* v_i_3021_, lean_object* v_b_3022_, lean_object* v___y_3023_){
_start:
{
size_t v_sz_boxed_3024_; size_t v_i_boxed_3025_; lean_object* v_res_3026_; 
v_sz_boxed_3024_ = lean_unbox_usize(v_sz_3020_);
lean_dec(v_sz_3020_);
v_i_boxed_3025_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3019_, v_sz_boxed_3024_, v_i_boxed_3025_, v_b_3022_);
lean_dec_ref(v_as_3019_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3031_, lean_object* v_linterOpts_3032_, lean_object* v_env_3033_, lean_object* v_mod_3034_){
_start:
{
uint8_t v_lintOnly_3036_; uint8_t v_mode_3037_; lean_object* v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3108_; lean_object* v___x_3114_; lean_object* v_textGroups_3115_; 
v_lintOnly_3036_ = lean_ctor_get_uint8(v_args_3031_, sizeof(void*)*4);
v_mode_3037_ = lean_ctor_get_uint8(v_args_3031_, sizeof(void*)*4 + 1);
v___x_3114_ = l_Lean_Name_getRoot(v_mod_3034_);
v_textGroups_3115_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3033_, v___x_3114_);
lean_dec(v___x_3114_);
if (v_lintOnly_3036_ == 0)
{
v___y_3108_ = v_textGroups_3115_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_array_get_size(v_textGroups_3115_);
v___x_3118_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3032_, v_textGroups_3115_, v___x_3116_, v___x_3117_);
lean_dec_ref(v_textGroups_3115_);
v___y_3108_ = v___x_3118_;
goto v___jp_3107_;
}
v___jp_3038_:
{
switch(v_mode_3037_)
{
case 0:
{
lean_object* v___x_3041_; size_t v_sz_3042_; size_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3041_ = lean_box(0);
v_sz_3042_ = lean_array_size(v___y_3039_);
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3039_, v_sz_3042_, v___x_3043_, v___x_3041_);
lean_dec_ref(v___y_3039_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_3044_, 0);
lean_dec(v_unused_3053_);
v___x_3046_ = v___x_3044_;
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___x_3044_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3048_, 0, v___y_3040_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3044_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3044_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
case 1:
{
lean_object* v___x_3062_; size_t v_sz_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3062_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3063_ = lean_array_size(v___y_3039_);
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3039_, v_sz_3063_, v___x_3064_, v___x_3062_);
lean_dec_ref(v___y_3039_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3077_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3077_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3077_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v_fst_3070_; lean_object* v_snd_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3075_; 
v_fst_3070_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_fst_3070_);
v_snd_3071_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_snd_3071_);
lean_dec(v_a_3066_);
v___x_3072_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3072_, 0, v_fst_3070_);
v___x_3073_ = lean_unbox(v_snd_3071_);
lean_dec(v_snd_3071_);
lean_ctor_set_uint8(v___x_3072_, sizeof(void*)*1, v___x_3073_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3072_);
v___x_3075_ = v___x_3068_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3072_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
v_a_3078_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3065_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3065_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3086_; size_t v_sz_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v_codeQualityEntries_3086_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3087_ = lean_array_size(v___y_3039_);
v___x_3088_ = ((size_t)0ULL);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3039_, v_sz_3087_, v___x_3088_, v_codeQualityEntries_3086_);
lean_dec_ref(v___y_3039_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_a_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3089_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3089_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3109_ = lean_array_get_size(v___y_3108_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_nat_dec_eq(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
uint8_t v___x_3112_; 
v___x_3112_ = 1;
v___y_3039_ = v___y_3108_;
v___y_3040_ = v___x_3112_;
goto v___jp_3038_;
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = 0;
v___y_3039_ = v___y_3108_;
v___y_3040_ = v___x_3113_;
goto v___jp_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3119_, lean_object* v_linterOpts_3120_, lean_object* v_env_3121_, lean_object* v_mod_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3119_, v_linterOpts_3120_, v_env_3121_, v_mod_3122_);
lean_dec(v_mod_3122_);
lean_dec_ref(v_env_3121_);
lean_dec_ref(v_linterOpts_3120_);
lean_dec_ref(v_args_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3125_, lean_object* v_t_3126_, lean_object* v_k_3127_, lean_object* v_fallback_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3126_, v_k_3127_, v_fallback_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3130_, lean_object* v_t_3131_, lean_object* v_k_3132_, lean_object* v_fallback_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3130_, v_t_3131_, v_k_3132_, v_fallback_3133_);
lean_dec(v_fallback_3133_);
lean_dec(v_k_3132_);
lean_dec(v_t_3131_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3135_, lean_object* v_____r_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3140_, 0, v___y_3135_);
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3142_, lean_object* v_____r_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
uint8_t v___y_15681__boxed_3147_; lean_object* v_res_3148_; 
v___y_15681__boxed_3147_ = lean_unbox(v___y_3142_);
v_res_3148_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15681__boxed_3147_, v_____r_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
lean_ctor_set(v___x_3154_, 2, v___x_3153_);
lean_ctor_set(v___x_3154_, 3, v___x_3153_);
lean_ctor_set(v___x_3154_, 4, v___x_3152_);
lean_ctor_set(v___x_3154_, 5, v___x_3152_);
lean_ctor_set(v___x_3154_, 6, v___x_3152_);
lean_ctor_set(v___x_3154_, 7, v___x_3152_);
lean_ctor_set(v___x_3154_, 8, v___x_3152_);
lean_ctor_set(v___x_3154_, 9, v___x_3152_);
lean_ctor_set(v___x_3154_, 10, v___x_3152_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_unsigned_to_nat(32u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3158_ = ((size_t)5ULL);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_unsigned_to_nat(32u);
v___x_3161_ = lean_mk_empty_array_with_capacity(v___x_3160_);
v___x_3162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v___x_3161_);
lean_ctor_set(v___x_3163_, 2, v___x_3159_);
lean_ctor_set(v___x_3163_, 3, v___x_3159_);
lean_ctor_set_usize(v___x_3163_, 4, v___x_3158_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3164_ = lean_box(1);
v___x_3165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___x_3165_);
lean_ctor_set(v___x_3167_, 2, v___x_3164_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v_env_3173_; lean_object* v_options_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3172_ = lean_st_ref_get(v___y_3170_);
v_env_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc_ref(v_env_3173_);
lean_dec(v___x_3172_);
v_options_3174_ = lean_ctor_get(v___y_3169_, 1);
v___x_3175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3174_);
v___x_3177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3177_, 0, v_env_3173_);
lean_ctor_set(v___x_3177_, 1, v___x_3175_);
lean_ctor_set(v___x_3177_, 2, v___x_3176_);
lean_ctor_set(v___x_3177_, 3, v_options_3174_);
v___x_3178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_msgData_3168_);
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_ref_3189_; lean_object* v___x_3190_; lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_ref_3189_ = lean_ctor_get(v___y_3186_, 4);
v___x_3190_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3185_, v___y_3186_, v___y_3187_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_inc(v_ref_3189_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_ref_3189_);
lean_ctor_set(v___x_3195_, 1, v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 1);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3205_, lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_toCold_3210_; lean_object* v_options_3211_; lean_object* v_currRecDepth_3212_; lean_object* v_maxRecDepth_3213_; lean_object* v_ref_3214_; lean_object* v_currNamespace_3215_; lean_object* v_openDecls_3216_; lean_object* v_initHeartbeats_3217_; lean_object* v_maxHeartbeats_3218_; lean_object* v_currMacroScope_3219_; uint8_t v_diag_3220_; uint8_t v_suppressElabErrors_3221_; lean_object* v_ref_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_toCold_3210_ = lean_ctor_get(v___y_3207_, 0);
v_options_3211_ = lean_ctor_get(v___y_3207_, 1);
v_currRecDepth_3212_ = lean_ctor_get(v___y_3207_, 2);
v_maxRecDepth_3213_ = lean_ctor_get(v___y_3207_, 3);
v_ref_3214_ = lean_ctor_get(v___y_3207_, 4);
v_currNamespace_3215_ = lean_ctor_get(v___y_3207_, 5);
v_openDecls_3216_ = lean_ctor_get(v___y_3207_, 6);
v_initHeartbeats_3217_ = lean_ctor_get(v___y_3207_, 7);
v_maxHeartbeats_3218_ = lean_ctor_get(v___y_3207_, 8);
v_currMacroScope_3219_ = lean_ctor_get(v___y_3207_, 9);
v_diag_3220_ = lean_ctor_get_uint8(v___y_3207_, sizeof(void*)*10);
v_suppressElabErrors_3221_ = lean_ctor_get_uint8(v___y_3207_, sizeof(void*)*10 + 1);
v_ref_3222_ = l_Lean_replaceRef(v_ref_3205_, v_ref_3214_);
lean_inc(v_currMacroScope_3219_);
lean_inc(v_maxHeartbeats_3218_);
lean_inc(v_initHeartbeats_3217_);
lean_inc(v_openDecls_3216_);
lean_inc(v_currNamespace_3215_);
lean_inc(v_maxRecDepth_3213_);
lean_inc(v_currRecDepth_3212_);
lean_inc_ref(v_options_3211_);
lean_inc_ref(v_toCold_3210_);
v___x_3223_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3223_, 0, v_toCold_3210_);
lean_ctor_set(v___x_3223_, 1, v_options_3211_);
lean_ctor_set(v___x_3223_, 2, v_currRecDepth_3212_);
lean_ctor_set(v___x_3223_, 3, v_maxRecDepth_3213_);
lean_ctor_set(v___x_3223_, 4, v_ref_3222_);
lean_ctor_set(v___x_3223_, 5, v_currNamespace_3215_);
lean_ctor_set(v___x_3223_, 6, v_openDecls_3216_);
lean_ctor_set(v___x_3223_, 7, v_initHeartbeats_3217_);
lean_ctor_set(v___x_3223_, 8, v_maxHeartbeats_3218_);
lean_ctor_set(v___x_3223_, 9, v_currMacroScope_3219_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*10, v_diag_3220_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*10 + 1, v_suppressElabErrors_3221_);
v___x_3224_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3206_, v___x_3223_, v___y_3208_);
lean_dec_ref_known(v___x_3223_, 10);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3225_, lean_object* v_msg_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3225_, v_msg_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v_ref_3225_);
return v_res_3230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3233_ = l_Lean_stringToMessageData(v___x_3232_);
return v___x_3233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3236_ = l_Lean_stringToMessageData(v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3239_ = l_Lean_stringToMessageData(v___x_3238_);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3242_ = l_Lean_stringToMessageData(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3248_ = l_Lean_stringToMessageData(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3252_, lean_object* v_declHint_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v___x_3256_; lean_object* v_env_3257_; uint8_t v___x_3258_; 
v___x_3256_ = lean_st_ref_get(v___y_3254_);
v_env_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3257_);
lean_dec(v___x_3256_);
v___x_3258_ = l_Lean_Name_isAnonymous(v_declHint_3253_);
if (v___x_3258_ == 0)
{
uint8_t v_isExporting_3259_; 
v_isExporting_3259_ = lean_ctor_get_uint8(v_env_3257_, sizeof(void*)*8);
if (v_isExporting_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec_ref(v_env_3257_);
lean_dec(v_declHint_3253_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_msg_3252_);
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; uint8_t v___x_3262_; 
lean_inc_ref(v_env_3257_);
v___x_3261_ = l_Lean_Environment_setExporting(v_env_3257_, v___x_3258_);
lean_inc(v_declHint_3253_);
lean_inc_ref(v___x_3261_);
v___x_3262_ = l_Lean_Environment_contains(v___x_3261_, v_declHint_3253_, v_isExporting_3259_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec_ref(v___x_3261_);
lean_dec_ref(v_env_3257_);
lean_dec(v_declHint_3253_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_msg_3252_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_c_3269_; lean_object* v___x_3270_; 
v___x_3264_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3265_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3266_ = l_Lean_Options_empty;
v___x_3267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3261_);
lean_ctor_set(v___x_3267_, 1, v___x_3264_);
lean_ctor_set(v___x_3267_, 2, v___x_3265_);
lean_ctor_set(v___x_3267_, 3, v___x_3266_);
lean_inc(v_declHint_3253_);
v___x_3268_ = l_Lean_MessageData_ofConstName(v_declHint_3253_, v___x_3258_);
v_c_3269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3269_, 0, v___x_3267_);
lean_ctor_set(v_c_3269_, 1, v___x_3268_);
v___x_3270_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3257_, v_declHint_3253_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v_env_3257_);
lean_dec(v_declHint_3253_);
v___x_3271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v_c_3269_);
v___x_3273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_MessageData_note(v___x_3274_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_msg_3252_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
else
{
lean_object* v_val_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3313_; 
v_val_3278_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3280_ = v___x_3270_;
v_isShared_3281_ = v_isSharedCheck_3313_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_val_3278_);
lean_dec(v___x_3270_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3313_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v_mod_3285_; uint8_t v___x_3286_; 
v___x_3282_ = lean_box(0);
v___x_3283_ = l_Lean_Environment_header(v_env_3257_);
lean_dec_ref(v_env_3257_);
v___x_3284_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3283_);
v_mod_3285_ = lean_array_get(v___x_3282_, v___x_3284_, v_val_3278_);
lean_dec(v_val_3278_);
lean_dec_ref(v___x_3284_);
v___x_3286_ = l_Lean_isPrivateName(v_declHint_3253_);
lean_dec(v_declHint_3253_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3287_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v_c_3269_);
v___x_3289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_MessageData_ofName(v_mod_3285_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_MessageData_note(v___x_3294_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_msg_3252_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3296_);
v___x_3298_ = v___x_3280_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v_c_3269_);
v___x_3302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = l_Lean_MessageData_ofName(v_mod_3285_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_MessageData_note(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_msg_3252_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3309_);
v___x_3311_ = v___x_3280_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3314_; 
lean_dec_ref(v_env_3257_);
lean_dec(v_declHint_3253_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_msg_3252_);
return v___x_3314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3315_, lean_object* v_declHint_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3315_, v_declHint_3316_, v___y_3317_);
lean_dec(v___y_3317_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3320_, lean_object* v_declHint_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3335_; 
v___x_3325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3320_, v_declHint_3321_, v___y_3323_);
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3335_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3335_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3330_ = l_Lean_unknownIdentifierMessageTag;
v___x_3331_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v_a_3326_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3331_);
v___x_3333_ = v___x_3328_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3336_, lean_object* v_declHint_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3336_, v_declHint_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3342_, lean_object* v_msg_3343_, lean_object* v_declHint_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v_a_3349_; lean_object* v___x_3350_; 
v___x_3348_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3343_, v_declHint_3344_, v___y_3345_, v___y_3346_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3342_, v_a_3349_, v___y_3345_, v___y_3346_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3351_, lean_object* v_msg_3352_, lean_object* v_declHint_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3351_, v_msg_3352_, v_declHint_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v_ref_3351_);
return v_res_3357_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3360_ = l_Lean_stringToMessageData(v___x_3359_);
return v___x_3360_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3363_, lean_object* v_constName_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3368_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3369_ = 0;
lean_inc(v_constName_3364_);
v___x_3370_ = l_Lean_MessageData_ofConstName(v_constName_3364_, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3368_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3363_, v___x_3373_, v_constName_3364_, v___y_3365_, v___y_3366_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3375_, lean_object* v_constName_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3375_, v_constName_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v_ref_3375_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_ref_3385_; lean_object* v___x_3386_; 
v_ref_3385_ = lean_ctor_get(v___y_3382_, 4);
v___x_3386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3385_, v_constName_3381_, v___y_3382_, v___y_3383_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; lean_object* v_env_3397_; uint8_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3396_ = lean_st_ref_get(v___y_3394_);
v_env_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc_ref(v_env_3397_);
lean_dec(v___x_3396_);
v___x_3398_ = 0;
lean_inc(v_constName_3392_);
v___x_3399_ = l_Lean_Environment_find_x3f(v_env_3397_, v_constName_3392_, v___x_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3392_, v___y_3393_, v___y_3394_);
return v___x_3400_;
}
else
{
lean_object* v_val_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_constName_3392_);
v_val_3401_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3399_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_val_3401_);
lean_dec(v___x_3399_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 0);
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_val_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
lean_inc(v_declName_3414_);
v___x_3418_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3445_; 
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3418_, 0);
lean_dec(v_unused_3446_);
v___x_3420_ = v___x_3418_;
v_isShared_3421_ = v_isSharedCheck_3445_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3418_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3445_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_env_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_st_ref_get(v___y_3416_);
v_env_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3423_);
lean_dec(v___x_3422_);
v___x_3424_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3423_, v_declName_3414_);
lean_dec(v_declName_3414_);
lean_dec_ref(v_env_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3425_);
v___x_3427_ = v___x_3420_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
else
{
lean_object* v_val_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3444_; 
v_val_3429_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3431_ = v___x_3424_;
v_isShared_3432_ = v_isSharedCheck_3444_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_val_3429_);
lean_dec(v___x_3424_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3444_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v_env_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3433_ = lean_st_ref_get(v___y_3416_);
v_env_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3434_);
lean_dec(v___x_3433_);
v___x_3435_ = lean_box(0);
v___x_3436_ = l_Lean_Environment_allImportedModuleNames(v_env_3434_);
lean_dec_ref(v_env_3434_);
v___x_3437_ = lean_array_get(v___x_3435_, v___x_3436_, v_val_3429_);
lean_dec(v_val_3429_);
lean_dec_ref(v___x_3436_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3437_);
v___x_3439_ = v___x_3431_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3439_);
v___x_3441_ = v___x_3420_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_declName_3414_);
v_a_3447_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3418_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3418_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
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
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3461_, lean_object* v_sp_3462_, lean_object* v___x_3463_, lean_object* v_as_3464_, size_t v_sz_3465_, size_t v_i_3466_, lean_object* v_b_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_a_3472_; uint8_t v___x_3476_; 
v___x_3476_ = lean_usize_dec_lt(v_i_3466_, v_sz_3465_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_b_3467_);
return v___x_3477_;
}
else
{
lean_object* v_a_3478_; lean_object* v_fst_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3614_; 
v_a_3478_ = lean_array_uget(v_as_3464_, v_i_3466_);
v_fst_3479_ = lean_ctor_get(v_a_3478_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_a_3478_);
if (v_isSharedCheck_3614_ == 0)
{
lean_object* v_unused_3615_; 
v_unused_3615_ = lean_ctor_get(v_a_3478_, 1);
lean_dec(v_unused_3615_);
v___x_3481_ = v_a_3478_;
v_isShared_3482_ = v_isSharedCheck_3614_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_fst_3479_);
lean_dec(v_a_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3614_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; 
lean_inc(v_fst_3479_);
v___x_3483_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3479_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
if (lean_obj_tag(v_a_3484_) == 0)
{
lean_object* v_fst_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3519_; 
v_fst_3485_ = lean_ctor_get(v_b_3467_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_b_3467_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; 
v_unused_3520_ = lean_ctor_get(v_b_3467_, 1);
lean_dec(v_unused_3520_);
v___x_3487_ = v_b_3467_;
v_isShared_3488_ = v_isSharedCheck_3519_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_fst_3485_);
lean_dec(v_b_3467_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3519_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_optName_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_optName_3489_ = lean_ctor_get(v_fst_3461_, 1);
v___x_3490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3491_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3479_, v___x_3476_);
v___x_3492_ = lean_string_append(v___x_3490_, v___x_3491_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_inc(v_optName_3489_);
v___x_3495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3489_, v___x_3476_);
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3498_ = lean_string_append(v___x_3496_, v___x_3497_);
v___x_3499_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3498_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3499_, 1);
lean_del_object(v___x_3481_);
v___x_3500_ = lean_box(v___x_3476_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3500_);
v___x_3502_ = v___x_3487_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3485_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
v_a_3472_ = v___x_3502_;
goto v___jp_3471_;
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3518_; 
lean_del_object(v___x_3487_);
lean_dec(v_fst_3485_);
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v_a_3504_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3506_ = v___x_3499_;
v_isShared_3507_ = v_isSharedCheck_3518_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3518_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_ref_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v_ref_3508_ = lean_ctor_get(v___y_3468_, 4);
v___x_3509_ = lean_io_error_to_string(v_a_3504_);
v___x_3510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
v___x_3511_ = l_Lean_MessageData_ofFormat(v___x_3510_);
lean_inc(v_ref_3508_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3511_);
lean_ctor_set(v___x_3481_, 0, v_ref_3508_);
v___x_3513_ = v___x_3481_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_ref_3508_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3513_);
v___x_3515_ = v___x_3506_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3605_; 
v_fst_3521_ = lean_ctor_get(v_b_3467_, 0);
v_snd_3522_ = lean_ctor_get(v_b_3467_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_b_3467_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3524_ = v_b_3467_;
v_isShared_3525_ = v_isSharedCheck_3605_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_b_3467_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3605_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3604_; 
v_val_3526_ = lean_ctor_get(v_a_3484_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3484_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3528_ = v_a_3484_;
v_isShared_3529_ = v_isSharedCheck_3604_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_a_3484_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3604_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3479_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___y_3533_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
if (lean_obj_tag(v_a_3531_) == 0)
{
lean_inc(v___x_3463_);
v___y_3533_ = v___x_3463_;
goto v___jp_3532_;
}
else
{
lean_object* v_val_3595_; 
v_val_3595_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v_a_3531_, 1);
v___y_3533_ = v_val_3595_;
goto v___jp_3532_;
}
v___jp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3533_);
lean_inc(v_sp_3462_);
v___x_3535_ = l_Lean_SearchPath_findWithExt(v_sp_3462_, v___x_3534_, v___y_3533_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
if (lean_obj_tag(v_a_3536_) == 0)
{
lean_object* v_optName_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_dec(v_val_3526_);
lean_dec(v_snd_3522_);
v_optName_3537_ = lean_ctor_get(v_fst_3461_, 1);
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3539_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3533_, v___x_3476_);
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
lean_inc(v_optName_3537_);
v___x_3543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3537_, v___x_3476_);
v___x_3544_ = lean_string_append(v___x_3542_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
v___x_3547_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
lean_dec_ref_known(v___x_3547_, 1);
lean_del_object(v___x_3528_);
lean_del_object(v___x_3481_);
v___x_3548_ = lean_box(v___x_3476_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3548_);
v___x_3550_ = v___x_3524_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_fst_3521_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
v_a_3472_ = v___x_3550_;
goto v___jp_3471_;
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3568_; 
lean_del_object(v___x_3524_);
lean_dec(v_fst_3521_);
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v_a_3552_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3554_ = v___x_3547_;
v_isShared_3555_ = v_isSharedCheck_3568_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3547_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3568_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v_ref_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v_ref_3556_ = lean_ctor_get(v___y_3468_, 4);
v___x_3557_ = lean_io_error_to_string(v_a_3552_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set_tag(v___x_3528_, 3);
lean_ctor_set(v___x_3528_, 0, v___x_3557_);
v___x_3559_ = v___x_3528_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3560_ = l_Lean_MessageData_ofFormat(v___x_3559_);
lean_inc(v_ref_3556_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3560_);
lean_ctor_set(v___x_3481_, 0, v_ref_3556_);
v___x_3562_ = v___x_3481_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_ref_3556_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3562_);
v___x_3564_ = v___x_3554_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
else
{
lean_object* v_range_3569_; lean_object* v_val_3570_; lean_object* v_pos_3571_; lean_object* v_optName_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
lean_dec(v___y_3533_);
lean_del_object(v___x_3528_);
lean_del_object(v___x_3481_);
v_range_3569_ = lean_ctor_get(v_val_3526_, 0);
lean_inc_ref(v_range_3569_);
lean_dec(v_val_3526_);
v_val_3570_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_val_3570_);
lean_dec_ref_known(v_a_3536_, 1);
v_pos_3571_ = lean_ctor_get(v_range_3569_, 0);
lean_inc_ref(v_pos_3571_);
lean_dec_ref(v_range_3569_);
v_optName_3572_ = lean_ctor_get(v_fst_3461_, 1);
lean_inc(v_optName_3572_);
v___x_3573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3573_, 0, v_val_3570_);
lean_ctor_set(v___x_3573_, 1, v_pos_3571_);
lean_ctor_set(v___x_3573_, 2, v_optName_3572_);
v___x_3574_ = lean_array_push(v_fst_3521_, v___x_3573_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3574_);
v___x_3576_ = v___x_3524_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_snd_3522_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
v_a_3472_ = v___x_3576_;
goto v___jp_3471_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v___y_3533_);
lean_dec(v_val_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v_a_3578_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3580_ = v___x_3535_;
v_isShared_3581_ = v_isSharedCheck_3594_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3535_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3594_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_ref_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v_ref_3582_ = lean_ctor_get(v___y_3468_, 4);
v___x_3583_ = lean_io_error_to_string(v_a_3578_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set_tag(v___x_3528_, 3);
lean_ctor_set(v___x_3528_, 0, v___x_3583_);
v___x_3585_ = v___x_3528_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = l_Lean_MessageData_ofFormat(v___x_3585_);
lean_inc(v_ref_3582_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3586_);
lean_ctor_set(v___x_3481_, 0, v_ref_3582_);
v___x_3588_ = v___x_3481_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_ref_3582_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3588_);
v___x_3590_ = v___x_3580_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_del_object(v___x_3528_);
lean_dec(v_val_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_del_object(v___x_3481_);
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v_a_3596_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3530_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3530_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
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
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_del_object(v___x_3481_);
lean_dec(v_fst_3479_);
lean_dec_ref(v_b_3467_);
lean_dec(v___x_3463_);
lean_dec(v_sp_3462_);
lean_dec_ref(v_fst_3461_);
v_a_3606_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3483_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3483_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
v___jp_3471_:
{
size_t v___x_3473_; size_t v___x_3474_; 
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3466_, v___x_3473_);
v_i_3466_ = v___x_3474_;
v_b_3467_ = v_a_3472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3616_, lean_object* v_sp_3617_, lean_object* v___x_3618_, lean_object* v_as_3619_, lean_object* v_sz_3620_, lean_object* v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3620_);
lean_dec(v_sz_3620_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3616_, v_sp_3617_, v___x_3618_, v_as_3619_, v_sz_boxed_3626_, v_i_boxed_3627_, v_b_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_as_3619_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
if (lean_obj_tag(v_x_3630_) == 0)
{
return v_x_3629_;
}
else
{
lean_object* v_key_3631_; lean_object* v_value_3632_; lean_object* v_tail_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v_key_3631_ = lean_ctor_get(v_x_3630_, 0);
v_value_3632_ = lean_ctor_get(v_x_3630_, 1);
v_tail_3633_ = lean_ctor_get(v_x_3630_, 2);
lean_inc(v_value_3632_);
lean_inc(v_key_3631_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v_key_3631_);
lean_ctor_set(v___x_3634_, 1, v_value_3632_);
v___x_3635_ = lean_array_push(v_x_3629_, v___x_3634_);
v_x_3629_ = v___x_3635_;
v_x_3630_ = v_tail_3633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3637_, v_x_3638_);
lean_dec(v_x_3638_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3640_, size_t v_i_3641_, size_t v_stop_3642_, lean_object* v_b_3643_){
_start:
{
uint8_t v___x_3644_; 
v___x_3644_ = lean_usize_dec_eq(v_i_3641_, v_stop_3642_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; size_t v___x_3647_; size_t v___x_3648_; 
v___x_3645_ = lean_array_uget_borrowed(v_as_3640_, v_i_3641_);
v___x_3646_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3643_, v___x_3645_);
v___x_3647_ = ((size_t)1ULL);
v___x_3648_ = lean_usize_add(v_i_3641_, v___x_3647_);
v_i_3641_ = v___x_3648_;
v_b_3643_ = v___x_3646_;
goto _start;
}
else
{
return v_b_3643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3650_, lean_object* v_i_3651_, lean_object* v_stop_3652_, lean_object* v_b_3653_){
_start:
{
size_t v_i_boxed_3654_; size_t v_stop_boxed_3655_; lean_object* v_res_3656_; 
v_i_boxed_3654_ = lean_unbox_usize(v_i_3651_);
lean_dec(v_i_3651_);
v_stop_boxed_3655_ = lean_unbox_usize(v_stop_3652_);
lean_dec(v_stop_3652_);
v_res_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3650_, v_i_boxed_3654_, v_stop_boxed_3655_, v_b_3653_);
lean_dec_ref(v_as_3650_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3657_, lean_object* v___x_3658_, lean_object* v_as_3659_, size_t v_sz_3660_, size_t v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_usize_dec_lt(v_i_3661_, v_sz_3660_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; 
lean_dec(v___x_3658_);
lean_dec(v_sp_3657_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_b_3662_);
return v___x_3667_;
}
else
{
lean_object* v_a_3668_; lean_object* v_fst_3669_; lean_object* v_snd_3670_; lean_object* v_fst_3671_; lean_object* v_snd_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3706_; 
v_a_3668_ = lean_array_uget_borrowed(v_as_3659_, v_i_3661_);
v_fst_3669_ = lean_ctor_get(v_a_3668_, 0);
v_snd_3670_ = lean_ctor_get(v_a_3668_, 1);
v_fst_3671_ = lean_ctor_get(v_b_3662_, 0);
v_snd_3672_ = lean_ctor_get(v_b_3662_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_b_3662_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3674_ = v_b_3662_;
v_isShared_3675_ = v_isSharedCheck_3706_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_snd_3672_);
lean_inc(v_fst_3671_);
lean_dec(v_b_3662_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3706_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___y_3677_; lean_object* v_size_3697_; lean_object* v_buckets_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v_size_3697_ = lean_ctor_get(v_snd_3670_, 0);
v_buckets_3698_ = lean_ctor_get(v_snd_3670_, 1);
v___x_3699_ = lean_mk_empty_array_with_capacity(v_size_3697_);
v___x_3700_ = lean_unsigned_to_nat(0u);
v___x_3701_ = lean_array_get_size(v_buckets_3698_);
v___x_3702_ = lean_nat_dec_lt(v___x_3700_, v___x_3701_);
if (v___x_3702_ == 0)
{
v___y_3677_ = v___x_3699_;
goto v___jp_3676_;
}
else
{
size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = ((size_t)0ULL);
v___x_3704_ = lean_usize_of_nat(v___x_3701_);
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3698_, v___x_3703_, v___x_3704_, v___x_3699_);
v___y_3677_ = v___x_3705_;
goto v___jp_3676_;
}
v___jp_3676_:
{
lean_object* v___x_3679_; 
if (v_isShared_3675_ == 0)
{
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_fst_3671_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_snd_3672_);
v___x_3679_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
size_t v_sz_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v_sz_3680_ = lean_array_size(v___y_3677_);
v___x_3681_ = ((size_t)0ULL);
lean_inc(v___x_3658_);
lean_inc(v_sp_3657_);
lean_inc(v_fst_3669_);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3669_, v_sp_3657_, v___x_3658_, v___y_3677_, v_sz_3680_, v___x_3681_, v___x_3679_, v___y_3663_, v___y_3664_);
lean_dec_ref(v___y_3677_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_fst_3684_; lean_object* v_snd_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3695_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v_fst_3684_ = lean_ctor_get(v_a_3683_, 0);
v_snd_3685_ = lean_ctor_get(v_a_3683_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3687_ = v_a_3683_;
v_isShared_3688_ = v_isSharedCheck_3695_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_snd_3685_);
lean_inc(v_fst_3684_);
lean_dec(v_a_3683_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3695_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_fst_3684_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_snd_3685_);
v___x_3690_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
size_t v___x_3691_; size_t v___x_3692_; 
v___x_3691_ = ((size_t)1ULL);
v___x_3692_ = lean_usize_add(v_i_3661_, v___x_3691_);
v_i_3661_ = v___x_3692_;
v_b_3662_ = v___x_3690_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3658_);
lean_dec(v_sp_3657_);
return v___x_3682_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3707_, lean_object* v___x_3708_, lean_object* v_as_3709_, lean_object* v_sz_3710_, lean_object* v_i_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
size_t v_sz_boxed_3716_; size_t v_i_boxed_3717_; lean_object* v_res_3718_; 
v_sz_boxed_3716_ = lean_unbox_usize(v_sz_3710_);
lean_dec(v_sz_3710_);
v_i_boxed_3717_ = lean_unbox_usize(v_i_3711_);
lean_dec(v_i_3711_);
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3707_, v___x_3708_, v_as_3709_, v_sz_boxed_3716_, v_i_boxed_3717_, v_b_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec_ref(v_as_3709_);
return v_res_3718_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3719_, lean_object* v_as_3720_, size_t v_i_3721_, size_t v_stop_3722_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_usize_dec_eq(v_i_3721_, v_stop_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; lean_object* v_snd_3725_; lean_object* v_size_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3724_ = lean_array_uget_borrowed(v_as_3720_, v_i_3721_);
v_snd_3725_ = lean_ctor_get(v___x_3724_, 1);
v_size_3726_ = lean_ctor_get(v_snd_3725_, 0);
v___x_3727_ = 1;
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = lean_nat_dec_eq(v_size_3726_, v___x_3728_);
if (v___x_3729_ == 0)
{
return v___x_3727_;
}
else
{
if (v___y_3719_ == 0)
{
size_t v___x_3730_; size_t v___x_3731_; 
v___x_3730_ = ((size_t)1ULL);
v___x_3731_ = lean_usize_add(v_i_3721_, v___x_3730_);
v_i_3721_ = v___x_3731_;
goto _start;
}
else
{
return v___x_3727_;
}
}
}
else
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3734_, lean_object* v_as_3735_, lean_object* v_i_3736_, lean_object* v_stop_3737_){
_start:
{
uint8_t v___y_16665__boxed_3738_; size_t v_i_boxed_3739_; size_t v_stop_boxed_3740_; uint8_t v_res_3741_; lean_object* v_r_3742_; 
v___y_16665__boxed_3738_ = lean_unbox(v___y_3734_);
v_i_boxed_3739_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_stop_boxed_3740_ = lean_unbox_usize(v_stop_3737_);
lean_dec(v_stop_3737_);
v_res_3741_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16665__boxed_3738_, v_as_3735_, v_i_boxed_3739_, v_stop_boxed_3740_);
lean_dec_ref(v_as_3735_);
v_r_3742_ = lean_box(v_res_3741_);
return v_r_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3743_, lean_object* v_v_3744_, lean_object* v_t_3745_){
_start:
{
lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; 
if (lean_obj_tag(v_t_3745_) == 0)
{
lean_object* v_size_3760_; lean_object* v_k_3761_; lean_object* v_v_3762_; lean_object* v_l_3763_; lean_object* v_r_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_4024_; 
v_size_3760_ = lean_ctor_get(v_t_3745_, 0);
v_k_3761_ = lean_ctor_get(v_t_3745_, 1);
v_v_3762_ = lean_ctor_get(v_t_3745_, 2);
v_l_3763_ = lean_ctor_get(v_t_3745_, 3);
v_r_3764_ = lean_ctor_get(v_t_3745_, 4);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_t_3745_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_3766_ = v_t_3745_;
v_isShared_3767_ = v_isSharedCheck_4024_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_r_3764_);
lean_inc(v_l_3763_);
lean_inc(v_v_3762_);
lean_inc(v_k_3761_);
lean_inc(v_size_3760_);
lean_dec(v_t_3745_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_4024_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; uint8_t v___y_3818_; lean_object* v_fst_4018_; lean_object* v_snd_4019_; lean_object* v_fst_4020_; lean_object* v_snd_4021_; uint8_t v___x_4022_; 
v_fst_4018_ = lean_ctor_get(v_k_3743_, 0);
v_snd_4019_ = lean_ctor_get(v_k_3743_, 1);
v_fst_4020_ = lean_ctor_get(v_k_3761_, 0);
v_snd_4021_ = lean_ctor_get(v_k_3761_, 1);
v___x_4022_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4018_, v_fst_4020_);
if (v___x_4022_ == 1)
{
uint8_t v___x_4023_; 
v___x_4023_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4019_, v_snd_4021_);
v___y_3818_ = v___x_4023_;
goto v___jp_3817_;
}
else
{
v___y_3818_ = v___x_4022_;
goto v___jp_3817_;
}
v___jp_3768_:
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3776_ = lean_nat_add(v___y_3770_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec(v___y_3770_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 3, v___y_3774_);
lean_ctor_set(v___x_3766_, 0, v___x_3776_);
v___x_3778_ = v___x_3766_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v___y_3774_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_r_3764_);
v___x_3778_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3779_, 0, v___y_3773_);
lean_ctor_set(v___x_3779_, 1, v___y_3769_);
lean_ctor_set(v___x_3779_, 2, v___y_3771_);
lean_ctor_set(v___x_3779_, 3, v___y_3772_);
lean_ctor_set(v___x_3779_, 4, v___x_3778_);
return v___x_3779_;
}
}
v___jp_3781_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_nat_add(v___y_3782_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec(v___y_3782_);
v___x_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
lean_ctor_set(v___x_3795_, 1, v___y_3783_);
lean_ctor_set(v___x_3795_, 2, v___y_3789_);
lean_ctor_set(v___x_3795_, 3, v___y_3787_);
lean_ctor_set(v___x_3795_, 4, v___y_3784_);
v___x_3796_ = lean_nat_add(v___y_3786_, v___y_3790_);
lean_dec(v___y_3790_);
if (lean_obj_tag(v___y_3791_) == 0)
{
lean_object* v_size_3797_; 
v_size_3797_ = lean_ctor_get(v___y_3791_, 0);
lean_inc(v_size_3797_);
v___y_3769_ = v___y_3785_;
v___y_3770_ = v___x_3796_;
v___y_3771_ = v___y_3788_;
v___y_3772_ = v___x_3795_;
v___y_3773_ = v___y_3792_;
v___y_3774_ = v___y_3791_;
v___y_3775_ = v_size_3797_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_unsigned_to_nat(0u);
v___y_3769_ = v___y_3785_;
v___y_3770_ = v___x_3796_;
v___y_3771_ = v___y_3788_;
v___y_3772_ = v___x_3795_;
v___y_3773_ = v___y_3792_;
v___y_3774_ = v___y_3791_;
v___y_3775_ = v___x_3798_;
goto v___jp_3768_;
}
}
v___jp_3799_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3812_ = lean_nat_add(v___y_3806_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec(v___y_3806_);
v___x_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v_k_3761_);
lean_ctor_set(v___x_3813_, 2, v_v_3762_);
lean_ctor_set(v___x_3813_, 3, v_l_3763_);
lean_ctor_set(v___x_3813_, 4, v___y_3802_);
v___x_3814_ = lean_nat_add(v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
if (lean_obj_tag(v___y_3803_) == 0)
{
lean_object* v_size_3815_; 
v_size_3815_ = lean_ctor_get(v___y_3803_, 0);
lean_inc(v_size_3815_);
v___y_3747_ = v___y_3801_;
v___y_3748_ = v___y_3800_;
v___y_3749_ = v___y_3803_;
v___y_3750_ = v___y_3804_;
v___y_3751_ = v___y_3805_;
v___y_3752_ = v___y_3807_;
v___y_3753_ = v___x_3813_;
v___y_3754_ = v___y_3810_;
v___y_3755_ = v___x_3814_;
v___y_3756_ = v_size_3815_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = lean_unsigned_to_nat(0u);
v___y_3747_ = v___y_3801_;
v___y_3748_ = v___y_3800_;
v___y_3749_ = v___y_3803_;
v___y_3750_ = v___y_3804_;
v___y_3751_ = v___y_3805_;
v___y_3752_ = v___y_3807_;
v___y_3753_ = v___x_3813_;
v___y_3754_ = v___y_3810_;
v___y_3755_ = v___x_3814_;
v___y_3756_ = v___x_3816_;
goto v___jp_3746_;
}
}
v___jp_3817_:
{
switch(v___y_3818_)
{
case 0:
{
lean_object* v_impl_3819_; lean_object* v___x_3820_; 
lean_dec(v_size_3760_);
v_impl_3819_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3743_, v_v_3744_, v_l_3763_);
v___x_3820_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3764_) == 0)
{
lean_object* v_size_3821_; lean_object* v_size_3822_; lean_object* v_k_3823_; lean_object* v_v_3824_; lean_object* v_l_3825_; lean_object* v_r_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_size_3821_ = lean_ctor_get(v_r_3764_, 0);
v_size_3822_ = lean_ctor_get(v_impl_3819_, 0);
lean_inc(v_size_3822_);
v_k_3823_ = lean_ctor_get(v_impl_3819_, 1);
lean_inc(v_k_3823_);
v_v_3824_ = lean_ctor_get(v_impl_3819_, 2);
lean_inc(v_v_3824_);
v_l_3825_ = lean_ctor_get(v_impl_3819_, 3);
lean_inc(v_l_3825_);
v_r_3826_ = lean_ctor_get(v_impl_3819_, 4);
lean_inc(v_r_3826_);
v___x_3827_ = lean_unsigned_to_nat(3u);
v___x_3828_ = lean_nat_mul(v___x_3827_, v_size_3821_);
v___x_3829_ = lean_nat_dec_lt(v___x_3828_, v_size_3822_);
lean_dec(v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v_r_3826_);
lean_dec(v_l_3825_);
lean_dec(v_v_3824_);
lean_dec(v_k_3823_);
lean_del_object(v___x_3766_);
v___x_3830_ = lean_nat_add(v___x_3820_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3831_ = lean_nat_add(v___x_3830_, v_size_3821_);
lean_dec(v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v_k_3761_);
lean_ctor_set(v___x_3832_, 2, v_v_3762_);
lean_ctor_set(v___x_3832_, 3, v_impl_3819_);
lean_ctor_set(v___x_3832_, 4, v_r_3764_);
return v___x_3832_;
}
else
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3869_; 
v_isSharedCheck_3869_ = !lean_is_exclusive(v_impl_3819_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3870_ = lean_ctor_get(v_impl_3819_, 4);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_impl_3819_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_impl_3819_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_impl_3819_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_impl_3819_, 0);
lean_dec(v_unused_3874_);
v___x_3834_ = v_impl_3819_;
v_isShared_3835_ = v_isSharedCheck_3869_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_impl_3819_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3869_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_size_3836_; lean_object* v_size_3837_; lean_object* v_k_3838_; lean_object* v_v_3839_; lean_object* v_l_3840_; lean_object* v_r_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_size_3836_ = lean_ctor_get(v_l_3825_, 0);
v_size_3837_ = lean_ctor_get(v_r_3826_, 0);
v_k_3838_ = lean_ctor_get(v_r_3826_, 1);
v_v_3839_ = lean_ctor_get(v_r_3826_, 2);
v_l_3840_ = lean_ctor_get(v_r_3826_, 3);
v_r_3841_ = lean_ctor_get(v_r_3826_, 4);
v___x_3842_ = lean_unsigned_to_nat(2u);
v___x_3843_ = lean_nat_mul(v___x_3842_, v_size_3836_);
v___x_3844_ = lean_nat_dec_lt(v_size_3837_, v___x_3843_);
lean_dec(v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_inc(v_r_3841_);
lean_inc(v_l_3840_);
lean_inc(v_v_3839_);
lean_inc(v_k_3838_);
lean_del_object(v___x_3834_);
lean_dec(v_r_3826_);
v___x_3845_ = lean_nat_add(v___x_3820_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3846_ = lean_nat_add(v___x_3845_, v_size_3821_);
lean_dec(v___x_3845_);
v___x_3847_ = lean_nat_add(v___x_3820_, v_size_3836_);
if (lean_obj_tag(v_l_3840_) == 0)
{
lean_object* v_size_3848_; 
v_size_3848_ = lean_ctor_get(v_l_3840_, 0);
lean_inc(v_size_3848_);
lean_inc(v_size_3821_);
v___y_3782_ = v___x_3847_;
v___y_3783_ = v_k_3823_;
v___y_3784_ = v_l_3840_;
v___y_3785_ = v_k_3838_;
v___y_3786_ = v___x_3820_;
v___y_3787_ = v_l_3825_;
v___y_3788_ = v_v_3839_;
v___y_3789_ = v_v_3824_;
v___y_3790_ = v_size_3821_;
v___y_3791_ = v_r_3841_;
v___y_3792_ = v___x_3846_;
v___y_3793_ = v_size_3848_;
goto v___jp_3781_;
}
else
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3821_);
v___y_3782_ = v___x_3847_;
v___y_3783_ = v_k_3823_;
v___y_3784_ = v_l_3840_;
v___y_3785_ = v_k_3838_;
v___y_3786_ = v___x_3820_;
v___y_3787_ = v_l_3825_;
v___y_3788_ = v_v_3839_;
v___y_3789_ = v_v_3824_;
v___y_3790_ = v_size_3821_;
v___y_3791_ = v_r_3841_;
v___y_3792_ = v___x_3846_;
v___y_3793_ = v___x_3849_;
goto v___jp_3781_;
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_del_object(v___x_3766_);
v___x_3850_ = lean_nat_add(v___x_3820_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3851_ = lean_nat_add(v___x_3850_, v_size_3821_);
lean_dec(v___x_3850_);
v___x_3852_ = lean_nat_add(v___x_3820_, v_size_3821_);
v___x_3853_ = lean_nat_add(v___x_3852_, v_size_3837_);
lean_dec(v___x_3852_);
lean_inc_ref(v_r_3764_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 4, v_r_3764_);
lean_ctor_set(v___x_3834_, 3, v_r_3826_);
lean_ctor_set(v___x_3834_, 2, v_v_3762_);
lean_ctor_set(v___x_3834_, 1, v_k_3761_);
lean_ctor_set(v___x_3834_, 0, v___x_3853_);
v___x_3855_ = v___x_3834_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3868_, 3, v_r_3826_);
lean_ctor_set(v_reuseFailAlloc_3868_, 4, v_r_3764_);
v___x_3855_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v_isSharedCheck_3862_ = !lean_is_exclusive(v_r_3764_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; lean_object* v_unused_3867_; 
v_unused_3863_ = lean_ctor_get(v_r_3764_, 4);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_r_3764_, 3);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_r_3764_, 2);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_r_3764_, 1);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_r_3764_, 0);
lean_dec(v_unused_3867_);
v___x_3857_ = v_r_3764_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_r_3764_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 4, v___x_3855_);
lean_ctor_set(v___x_3857_, 3, v_l_3825_);
lean_ctor_set(v___x_3857_, 2, v_v_3824_);
lean_ctor_set(v___x_3857_, 1, v_k_3823_);
lean_ctor_set(v___x_3857_, 0, v___x_3851_);
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_k_3823_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_v_3824_);
lean_ctor_set(v_reuseFailAlloc_3861_, 3, v_l_3825_);
lean_ctor_set(v_reuseFailAlloc_3861_, 4, v___x_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3875_; 
lean_del_object(v___x_3766_);
v_l_3875_ = lean_ctor_get(v_impl_3819_, 3);
lean_inc(v_l_3875_);
if (lean_obj_tag(v_l_3875_) == 0)
{
lean_object* v_r_3876_; lean_object* v_k_3877_; lean_object* v_v_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3887_; 
v_r_3876_ = lean_ctor_get(v_impl_3819_, 4);
v_k_3877_ = lean_ctor_get(v_impl_3819_, 1);
v_v_3878_ = lean_ctor_get(v_impl_3819_, 2);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_impl_3819_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3888_ = lean_ctor_get(v_impl_3819_, 3);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_impl_3819_, 0);
lean_dec(v_unused_3889_);
v___x_3880_ = v_impl_3819_;
v_isShared_3881_ = v_isSharedCheck_3887_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_r_3876_);
lean_inc(v_v_3878_);
lean_inc(v_k_3877_);
lean_dec(v_impl_3819_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3887_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3882_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3876_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 3, v_r_3876_);
lean_ctor_set(v___x_3880_, 2, v_v_3762_);
lean_ctor_set(v___x_3880_, 1, v_k_3761_);
lean_ctor_set(v___x_3880_, 0, v___x_3820_);
v___x_3884_ = v___x_3880_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_r_3876_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v_r_3876_);
v___x_3884_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3882_);
lean_ctor_set(v___x_3885_, 1, v_k_3877_);
lean_ctor_set(v___x_3885_, 2, v_v_3878_);
lean_ctor_set(v___x_3885_, 3, v_l_3875_);
lean_ctor_set(v___x_3885_, 4, v___x_3884_);
return v___x_3885_;
}
}
}
else
{
lean_object* v_r_3890_; 
v_r_3890_ = lean_ctor_get(v_impl_3819_, 4);
lean_inc(v_r_3890_);
if (lean_obj_tag(v_r_3890_) == 0)
{
lean_object* v_k_3891_; lean_object* v_v_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3913_; 
v_k_3891_ = lean_ctor_get(v_impl_3819_, 1);
v_v_3892_ = lean_ctor_get(v_impl_3819_, 2);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_impl_3819_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3914_ = lean_ctor_get(v_impl_3819_, 4);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_impl_3819_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_impl_3819_, 0);
lean_dec(v_unused_3916_);
v___x_3894_ = v_impl_3819_;
v_isShared_3895_ = v_isSharedCheck_3913_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_v_3892_);
lean_inc(v_k_3891_);
lean_dec(v_impl_3819_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3913_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v_k_3896_; lean_object* v_v_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3909_; 
v_k_3896_ = lean_ctor_get(v_r_3890_, 1);
v_v_3897_ = lean_ctor_get(v_r_3890_, 2);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_r_3890_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; 
v_unused_3910_ = lean_ctor_get(v_r_3890_, 4);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_r_3890_, 3);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_r_3890_, 0);
lean_dec(v_unused_3912_);
v___x_3899_ = v_r_3890_;
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_v_3897_);
lean_inc(v_k_3896_);
lean_dec(v_r_3890_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_unsigned_to_nat(3u);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 4, v_l_3875_);
lean_ctor_set(v___x_3899_, 3, v_l_3875_);
lean_ctor_set(v___x_3899_, 2, v_v_3892_);
lean_ctor_set(v___x_3899_, 1, v_k_3891_);
lean_ctor_set(v___x_3899_, 0, v___x_3820_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_k_3891_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_v_3892_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_l_3875_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_l_3875_);
v___x_3903_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3905_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 4, v_l_3875_);
lean_ctor_set(v___x_3894_, 2, v_v_3762_);
lean_ctor_set(v___x_3894_, 1, v_k_3761_);
lean_ctor_set(v___x_3894_, 0, v___x_3820_);
v___x_3905_ = v___x_3894_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_l_3875_);
lean_ctor_set(v_reuseFailAlloc_3907_, 4, v_l_3875_);
v___x_3905_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3901_);
lean_ctor_set(v___x_3906_, 1, v_k_3896_);
lean_ctor_set(v___x_3906_, 2, v_v_3897_);
lean_ctor_set(v___x_3906_, 3, v___x_3903_);
lean_ctor_set(v___x_3906_, 4, v___x_3905_);
return v___x_3906_;
}
}
}
}
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_unsigned_to_nat(2u);
v___x_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v_k_3761_);
lean_ctor_set(v___x_3918_, 2, v_v_3762_);
lean_ctor_set(v___x_3918_, 3, v_impl_3819_);
lean_ctor_set(v___x_3918_, 4, v_r_3890_);
return v___x_3918_;
}
}
}
}
case 1:
{
lean_object* v___x_3919_; 
lean_del_object(v___x_3766_);
lean_dec(v_v_3762_);
lean_dec(v_k_3761_);
v___x_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3919_, 0, v_size_3760_);
lean_ctor_set(v___x_3919_, 1, v_k_3743_);
lean_ctor_set(v___x_3919_, 2, v_v_3744_);
lean_ctor_set(v___x_3919_, 3, v_l_3763_);
lean_ctor_set(v___x_3919_, 4, v_r_3764_);
return v___x_3919_;
}
default: 
{
lean_object* v_impl_3920_; lean_object* v___x_3921_; 
lean_del_object(v___x_3766_);
lean_dec(v_size_3760_);
v_impl_3920_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3743_, v_v_3744_, v_r_3764_);
v___x_3921_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3763_) == 0)
{
lean_object* v_size_3922_; lean_object* v_size_3923_; lean_object* v_k_3924_; lean_object* v_v_3925_; lean_object* v_l_3926_; lean_object* v_r_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v_size_3922_ = lean_ctor_get(v_l_3763_, 0);
v_size_3923_ = lean_ctor_get(v_impl_3920_, 0);
lean_inc(v_size_3923_);
v_k_3924_ = lean_ctor_get(v_impl_3920_, 1);
lean_inc(v_k_3924_);
v_v_3925_ = lean_ctor_get(v_impl_3920_, 2);
lean_inc(v_v_3925_);
v_l_3926_ = lean_ctor_get(v_impl_3920_, 3);
lean_inc(v_l_3926_);
v_r_3927_ = lean_ctor_get(v_impl_3920_, 4);
lean_inc(v_r_3927_);
v___x_3928_ = lean_unsigned_to_nat(3u);
v___x_3929_ = lean_nat_mul(v___x_3928_, v_size_3922_);
v___x_3930_ = lean_nat_dec_lt(v___x_3929_, v_size_3923_);
lean_dec(v___x_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v_r_3927_);
lean_dec(v_l_3926_);
lean_dec(v_v_3925_);
lean_dec(v_k_3924_);
v___x_3931_ = lean_nat_add(v___x_3921_, v_size_3922_);
v___x_3932_ = lean_nat_add(v___x_3931_, v_size_3923_);
lean_dec(v_size_3923_);
lean_dec(v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v_k_3761_);
lean_ctor_set(v___x_3933_, 2, v_v_3762_);
lean_ctor_set(v___x_3933_, 3, v_l_3763_);
lean_ctor_set(v___x_3933_, 4, v_impl_3920_);
return v___x_3933_;
}
else
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3968_; 
v_isSharedCheck_3968_ = !lean_is_exclusive(v_impl_3920_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; lean_object* v_unused_3973_; 
v_unused_3969_ = lean_ctor_get(v_impl_3920_, 4);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_impl_3920_, 3);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_impl_3920_, 2);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_impl_3920_, 1);
lean_dec(v_unused_3972_);
v_unused_3973_ = lean_ctor_get(v_impl_3920_, 0);
lean_dec(v_unused_3973_);
v___x_3935_ = v_impl_3920_;
v_isShared_3936_ = v_isSharedCheck_3968_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_impl_3920_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3968_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v_size_3937_; lean_object* v_k_3938_; lean_object* v_v_3939_; lean_object* v_l_3940_; lean_object* v_r_3941_; lean_object* v_size_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v_size_3937_ = lean_ctor_get(v_l_3926_, 0);
v_k_3938_ = lean_ctor_get(v_l_3926_, 1);
v_v_3939_ = lean_ctor_get(v_l_3926_, 2);
v_l_3940_ = lean_ctor_get(v_l_3926_, 3);
v_r_3941_ = lean_ctor_get(v_l_3926_, 4);
v_size_3942_ = lean_ctor_get(v_r_3927_, 0);
v___x_3943_ = lean_unsigned_to_nat(2u);
v___x_3944_ = lean_nat_mul(v___x_3943_, v_size_3942_);
v___x_3945_ = lean_nat_dec_lt(v_size_3937_, v___x_3944_);
lean_dec(v___x_3944_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_inc(v_size_3942_);
lean_inc(v_r_3941_);
lean_inc(v_l_3940_);
lean_inc(v_v_3939_);
lean_inc(v_k_3938_);
lean_del_object(v___x_3935_);
lean_dec(v_l_3926_);
v___x_3946_ = lean_nat_add(v___x_3921_, v_size_3922_);
v___x_3947_ = lean_nat_add(v___x_3946_, v_size_3923_);
lean_dec(v_size_3923_);
if (lean_obj_tag(v_l_3940_) == 0)
{
lean_object* v_size_3948_; 
v_size_3948_ = lean_ctor_get(v_l_3940_, 0);
lean_inc(v_size_3948_);
v___y_3800_ = v_k_3924_;
v___y_3801_ = v___x_3947_;
v___y_3802_ = v_l_3940_;
v___y_3803_ = v_r_3941_;
v___y_3804_ = v_k_3938_;
v___y_3805_ = v_v_3939_;
v___y_3806_ = v___x_3946_;
v___y_3807_ = v_v_3925_;
v___y_3808_ = v___x_3921_;
v___y_3809_ = v_size_3942_;
v___y_3810_ = v_r_3927_;
v___y_3811_ = v_size_3948_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_unsigned_to_nat(0u);
v___y_3800_ = v_k_3924_;
v___y_3801_ = v___x_3947_;
v___y_3802_ = v_l_3940_;
v___y_3803_ = v_r_3941_;
v___y_3804_ = v_k_3938_;
v___y_3805_ = v_v_3939_;
v___y_3806_ = v___x_3946_;
v___y_3807_ = v_v_3925_;
v___y_3808_ = v___x_3921_;
v___y_3809_ = v_size_3942_;
v___y_3810_ = v_r_3927_;
v___y_3811_ = v___x_3949_;
goto v___jp_3799_;
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3950_ = lean_nat_add(v___x_3921_, v_size_3922_);
v___x_3951_ = lean_nat_add(v___x_3950_, v_size_3923_);
lean_dec(v_size_3923_);
v___x_3952_ = lean_nat_add(v___x_3950_, v_size_3937_);
lean_dec(v___x_3950_);
lean_inc_ref(v_l_3763_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 4, v_l_3926_);
lean_ctor_set(v___x_3935_, 3, v_l_3763_);
lean_ctor_set(v___x_3935_, 2, v_v_3762_);
lean_ctor_set(v___x_3935_, 1, v_k_3761_);
lean_ctor_set(v___x_3935_, 0, v___x_3952_);
v___x_3954_ = v___x_3935_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_l_3763_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_l_3926_);
v___x_3954_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
v_isSharedCheck_3961_ = !lean_is_exclusive(v_l_3763_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; 
v_unused_3962_ = lean_ctor_get(v_l_3763_, 4);
lean_dec(v_unused_3962_);
v_unused_3963_ = lean_ctor_get(v_l_3763_, 3);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_l_3763_, 2);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_l_3763_, 1);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_l_3763_, 0);
lean_dec(v_unused_3966_);
v___x_3956_ = v_l_3763_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_dec(v_l_3763_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 4, v_r_3927_);
lean_ctor_set(v___x_3956_, 3, v___x_3954_);
lean_ctor_set(v___x_3956_, 2, v_v_3925_);
lean_ctor_set(v___x_3956_, 1, v_k_3924_);
lean_ctor_set(v___x_3956_, 0, v___x_3951_);
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_k_3924_);
lean_ctor_set(v_reuseFailAlloc_3960_, 2, v_v_3925_);
lean_ctor_set(v_reuseFailAlloc_3960_, 3, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3960_, 4, v_r_3927_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3974_; 
v_l_3974_ = lean_ctor_get(v_impl_3920_, 3);
lean_inc(v_l_3974_);
if (lean_obj_tag(v_l_3974_) == 0)
{
lean_object* v_r_3975_; lean_object* v_k_3976_; lean_object* v_v_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3998_; 
v_r_3975_ = lean_ctor_get(v_impl_3920_, 4);
v_k_3976_ = lean_ctor_get(v_impl_3920_, 1);
v_v_3977_ = lean_ctor_get(v_impl_3920_, 2);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_impl_3920_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; 
v_unused_3999_ = lean_ctor_get(v_impl_3920_, 3);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_impl_3920_, 0);
lean_dec(v_unused_4000_);
v___x_3979_ = v_impl_3920_;
v_isShared_3980_ = v_isSharedCheck_3998_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_r_3975_);
lean_inc(v_v_3977_);
lean_inc(v_k_3976_);
lean_dec(v_impl_3920_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3998_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_k_3981_; lean_object* v_v_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3994_; 
v_k_3981_ = lean_ctor_get(v_l_3974_, 1);
v_v_3982_ = lean_ctor_get(v_l_3974_, 2);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_l_3974_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; lean_object* v_unused_3996_; lean_object* v_unused_3997_; 
v_unused_3995_ = lean_ctor_get(v_l_3974_, 4);
lean_dec(v_unused_3995_);
v_unused_3996_ = lean_ctor_get(v_l_3974_, 3);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_l_3974_, 0);
lean_dec(v_unused_3997_);
v___x_3984_ = v_l_3974_;
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_v_3982_);
lean_inc(v_k_3981_);
lean_dec(v_l_3974_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3986_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3975_, 2);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 4, v_r_3975_);
lean_ctor_set(v___x_3984_, 3, v_r_3975_);
lean_ctor_set(v___x_3984_, 2, v_v_3762_);
lean_ctor_set(v___x_3984_, 1, v_k_3761_);
lean_ctor_set(v___x_3984_, 0, v___x_3921_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_r_3975_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v_r_3975_);
v___x_3988_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3990_; 
lean_inc(v_r_3975_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 3, v_r_3975_);
lean_ctor_set(v___x_3979_, 0, v___x_3921_);
v___x_3990_ = v___x_3979_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_k_3976_);
lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_v_3977_);
lean_ctor_set(v_reuseFailAlloc_3992_, 3, v_r_3975_);
lean_ctor_set(v_reuseFailAlloc_3992_, 4, v_r_3975_);
v___x_3990_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3986_);
lean_ctor_set(v___x_3991_, 1, v_k_3981_);
lean_ctor_set(v___x_3991_, 2, v_v_3982_);
lean_ctor_set(v___x_3991_, 3, v___x_3988_);
lean_ctor_set(v___x_3991_, 4, v___x_3990_);
return v___x_3991_;
}
}
}
}
}
else
{
lean_object* v_r_4001_; 
v_r_4001_ = lean_ctor_get(v_impl_3920_, 4);
lean_inc(v_r_4001_);
if (lean_obj_tag(v_r_4001_) == 0)
{
lean_object* v_k_4002_; lean_object* v_v_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4012_; 
v_k_4002_ = lean_ctor_get(v_impl_3920_, 1);
v_v_4003_ = lean_ctor_get(v_impl_3920_, 2);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_impl_3920_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; lean_object* v_unused_4014_; lean_object* v_unused_4015_; 
v_unused_4013_ = lean_ctor_get(v_impl_3920_, 4);
lean_dec(v_unused_4013_);
v_unused_4014_ = lean_ctor_get(v_impl_3920_, 3);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_impl_3920_, 0);
lean_dec(v_unused_4015_);
v___x_4005_ = v_impl_3920_;
v_isShared_4006_ = v_isSharedCheck_4012_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_v_4003_);
lean_inc(v_k_4002_);
lean_dec(v_impl_3920_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4012_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4007_ = lean_unsigned_to_nat(3u);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 4, v_l_3974_);
lean_ctor_set(v___x_4005_, 2, v_v_3762_);
lean_ctor_set(v___x_4005_, 1, v_k_3761_);
lean_ctor_set(v___x_4005_, 0, v___x_3921_);
v___x_4009_ = v___x_4005_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_l_3974_);
lean_ctor_set(v_reuseFailAlloc_4011_, 4, v_l_3974_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4007_);
lean_ctor_set(v___x_4010_, 1, v_k_4002_);
lean_ctor_set(v___x_4010_, 2, v_v_4003_);
lean_ctor_set(v___x_4010_, 3, v___x_4009_);
lean_ctor_set(v___x_4010_, 4, v_r_4001_);
return v___x_4010_;
}
}
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_unsigned_to_nat(2u);
v___x_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
lean_ctor_set(v___x_4017_, 1, v_k_3761_);
lean_ctor_set(v___x_4017_, 2, v_v_3762_);
lean_ctor_set(v___x_4017_, 3, v_r_4001_);
lean_ctor_set(v___x_4017_, 4, v_impl_3920_);
return v___x_4017_;
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
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_unsigned_to_nat(1u);
v___x_4026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
lean_ctor_set(v___x_4026_, 1, v_k_3743_);
lean_ctor_set(v___x_4026_, 2, v_v_3744_);
lean_ctor_set(v___x_4026_, 3, v_t_3745_);
lean_ctor_set(v___x_4026_, 4, v_t_3745_);
return v___x_4026_;
}
v___jp_3746_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_nat_add(v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec(v___y_3755_);
v___x_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set(v___x_3758_, 1, v___y_3748_);
lean_ctor_set(v___x_3758_, 2, v___y_3752_);
lean_ctor_set(v___x_3758_, 3, v___y_3749_);
lean_ctor_set(v___x_3758_, 4, v___y_3754_);
v___x_3759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3759_, 0, v___y_3747_);
lean_ctor_set(v___x_3759_, 1, v___y_3750_);
lean_ctor_set(v___x_3759_, 2, v___y_3751_);
lean_ctor_set(v___x_3759_, 3, v___y_3753_);
lean_ctor_set(v___x_3759_, 4, v___x_3758_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4027_, lean_object* v_k_4028_, lean_object* v_fallback_4029_){
_start:
{
if (lean_obj_tag(v_t_4027_) == 0)
{
lean_object* v_k_4030_; lean_object* v_v_4031_; lean_object* v_l_4032_; lean_object* v_r_4033_; uint8_t v___y_4035_; lean_object* v_fst_4038_; lean_object* v_snd_4039_; lean_object* v_fst_4040_; lean_object* v_snd_4041_; uint8_t v___x_4042_; 
v_k_4030_ = lean_ctor_get(v_t_4027_, 1);
v_v_4031_ = lean_ctor_get(v_t_4027_, 2);
v_l_4032_ = lean_ctor_get(v_t_4027_, 3);
v_r_4033_ = lean_ctor_get(v_t_4027_, 4);
v_fst_4038_ = lean_ctor_get(v_k_4028_, 0);
v_snd_4039_ = lean_ctor_get(v_k_4028_, 1);
v_fst_4040_ = lean_ctor_get(v_k_4030_, 0);
v_snd_4041_ = lean_ctor_get(v_k_4030_, 1);
v___x_4042_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4038_, v_fst_4040_);
if (v___x_4042_ == 1)
{
uint8_t v___x_4043_; 
v___x_4043_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4039_, v_snd_4041_);
v___y_4035_ = v___x_4043_;
goto v___jp_4034_;
}
else
{
v___y_4035_ = v___x_4042_;
goto v___jp_4034_;
}
v___jp_4034_:
{
switch(v___y_4035_)
{
case 0:
{
v_t_4027_ = v_l_4032_;
goto _start;
}
case 1:
{
lean_inc(v_v_4031_);
return v_v_4031_;
}
default: 
{
v_t_4027_ = v_r_4033_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4029_);
return v_fallback_4029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4044_, lean_object* v_k_4045_, lean_object* v_fallback_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4044_, v_k_4045_, v_fallback_4046_);
lean_dec(v_fallback_4046_);
lean_dec_ref(v_k_4045_);
lean_dec(v_t_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4048_, lean_object* v_as_4049_, size_t v_sz_4050_, size_t v_i_4051_, lean_object* v_b_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_usize_dec_lt(v_i_4051_, v_sz_4050_);
if (v___x_4056_ == 0)
{
lean_object* v___x_4057_; 
lean_dec(v___x_4048_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v_b_4052_);
return v___x_4057_;
}
else
{
lean_object* v_a_4058_; lean_object* v_fst_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4087_; 
v_a_4058_ = lean_array_uget(v_as_4049_, v_i_4051_);
v_fst_4059_ = lean_ctor_get(v_a_4058_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_4058_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v_a_4058_, 1);
lean_dec(v_unused_4088_);
v___x_4061_ = v_a_4058_;
v_isShared_4062_ = v_isSharedCheck_4087_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_fst_4059_);
lean_dec(v_a_4058_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4087_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; 
lean_inc(v_fst_4059_);
v___x_4063_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4059_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___y_4067_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_4064_) == 0)
{
lean_inc(v___x_4048_);
v___y_4067_ = v___x_4048_;
goto v___jp_4066_;
}
else
{
lean_object* v_val_4078_; 
v_val_4078_ = lean_ctor_get(v_a_4064_, 0);
lean_inc(v_val_4078_);
lean_dec_ref_known(v_a_4064_, 1);
v___y_4067_ = v_val_4078_;
goto v___jp_4066_;
}
v___jp_4066_:
{
lean_object* v___x_4069_; 
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 1, v_fst_4059_);
lean_ctor_set(v___x_4061_, 0, v___y_4067_);
v___x_4069_ = v___x_4061_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___y_4067_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_fst_4059_);
v___x_4069_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; size_t v___x_4074_; size_t v___x_4075_; 
v___x_4070_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4052_, v___x_4069_, v___x_4065_);
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_add(v___x_4070_, v___x_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4069_, v___x_4072_, v_b_4052_);
v___x_4074_ = ((size_t)1ULL);
v___x_4075_ = lean_usize_add(v_i_4051_, v___x_4074_);
v_i_4051_ = v___x_4075_;
v_b_4052_ = v___x_4073_;
goto _start;
}
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_del_object(v___x_4061_);
lean_dec(v_fst_4059_);
lean_dec(v_b_4052_);
lean_dec(v___x_4048_);
v_a_4079_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4063_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4063_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4089_, lean_object* v_as_4090_, lean_object* v_sz_4091_, lean_object* v_i_4092_, lean_object* v_b_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
size_t v_sz_boxed_4097_; size_t v_i_boxed_4098_; lean_object* v_res_4099_; 
v_sz_boxed_4097_ = lean_unbox_usize(v_sz_4091_);
lean_dec(v_sz_4091_);
v_i_boxed_4098_ = lean_unbox_usize(v_i_4092_);
lean_dec(v_i_4092_);
v_res_4099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4089_, v_as_4090_, v_sz_boxed_4097_, v_i_boxed_4098_, v_b_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v_as_4090_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4100_, lean_object* v_init_4101_, lean_object* v_x_4102_){
_start:
{
if (lean_obj_tag(v_x_4102_) == 0)
{
lean_object* v_k_4104_; lean_object* v_v_4105_; lean_object* v_l_4106_; lean_object* v_r_4107_; lean_object* v___x_4108_; lean_object* v_a_4109_; lean_object* v_a_4110_; lean_object* v_fst_4111_; lean_object* v_snd_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4127_; 
v_k_4104_ = lean_ctor_get(v_x_4102_, 1);
lean_inc(v_k_4104_);
v_v_4105_ = lean_ctor_get(v_x_4102_, 2);
lean_inc(v_v_4105_);
v_l_4106_ = lean_ctor_get(v_x_4102_, 3);
lean_inc(v_l_4106_);
v_r_4107_ = lean_ctor_get(v_x_4102_, 4);
lean_inc(v_r_4107_);
lean_dec_ref_known(v_x_4102_, 5);
lean_inc_ref(v_fst_4100_);
v___x_4108_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4100_, v_init_4101_, v_l_4106_);
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref(v___x_4108_);
v_a_4110_ = lean_ctor_get(v_a_4109_, 0);
lean_inc(v_a_4110_);
lean_dec(v_a_4109_);
v_fst_4111_ = lean_ctor_get(v_k_4104_, 0);
v_snd_4112_ = lean_ctor_get(v_k_4104_, 1);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_k_4104_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4114_ = v_k_4104_;
v_isShared_4115_ = v_isSharedCheck_4127_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_snd_4112_);
lean_inc(v_fst_4111_);
lean_dec(v_k_4104_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4127_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v_optName_4116_; uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v_optName_4116_ = lean_ctor_get(v_fst_4100_, 1);
v___x_4117_ = 1;
lean_inc(v_optName_4116_);
v___x_4118_ = l_Lean_Name_toString(v_optName_4116_, v___x_4117_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 1);
v___x_4120_ = v___x_4114_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_fst_4111_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_snd_4112_);
v___x_4120_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
double v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4121_ = lean_float_of_nat(v_v_4105_);
v___x_4122_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4122_, 0, v___x_4121_);
v___x_4123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4118_);
lean_ctor_set(v___x_4123_, 1, v___x_4120_);
lean_ctor_set(v___x_4123_, 2, v___x_4122_);
v___x_4124_ = lean_array_push(v_a_4110_, v___x_4123_);
v_init_4101_ = v___x_4124_;
v_x_4102_ = v_r_4107_;
goto _start;
}
}
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref(v_fst_4100_);
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_init_4101_);
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4130_, lean_object* v_init_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4130_, v_init_4131_, v_x_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4135_, lean_object* v_as_4136_, size_t v_sz_4137_, size_t v_i_4138_, lean_object* v_b_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_a_4144_; uint8_t v___x_4148_; 
v___x_4148_ = lean_usize_dec_lt(v_i_4138_, v_sz_4137_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
lean_dec(v___x_4135_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_b_4139_);
return v___x_4149_;
}
else
{
lean_object* v_a_4150_; lean_object* v_snd_4151_; lean_object* v_fst_4152_; lean_object* v_size_4153_; lean_object* v_buckets_4154_; lean_object* v___x_4155_; lean_object* v___y_4157_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v_a_4150_ = lean_array_uget_borrowed(v_as_4136_, v_i_4138_);
v_snd_4151_ = lean_ctor_get(v_a_4150_, 1);
v_fst_4152_ = lean_ctor_get(v_a_4150_, 0);
v_size_4153_ = lean_ctor_get(v_snd_4151_, 0);
v_buckets_4154_ = lean_ctor_get(v_snd_4151_, 1);
v___x_4155_ = lean_box(1);
v___x_4191_ = lean_mk_empty_array_with_capacity(v_size_4153_);
v___x_4192_ = lean_unsigned_to_nat(0u);
v___x_4193_ = lean_array_get_size(v_buckets_4154_);
v___x_4194_ = lean_nat_dec_lt(v___x_4192_, v___x_4193_);
if (v___x_4194_ == 0)
{
v___y_4157_ = v___x_4191_;
goto v___jp_4156_;
}
else
{
size_t v___x_4195_; size_t v___x_4196_; lean_object* v___x_4197_; 
v___x_4195_ = ((size_t)0ULL);
v___x_4196_ = lean_usize_of_nat(v___x_4193_);
v___x_4197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4154_, v___x_4195_, v___x_4196_, v___x_4191_);
v___y_4157_ = v___x_4197_;
goto v___jp_4156_;
}
v___jp_4156_:
{
size_t v_sz_4158_; size_t v___x_4159_; lean_object* v___x_4160_; 
v_sz_4158_ = lean_array_size(v___y_4157_);
v___x_4159_ = ((size_t)0ULL);
lean_inc(v___x_4135_);
v___x_4160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4135_, v___y_4157_, v_sz_4158_, v___x_4159_, v___x_4155_, v___y_4140_, v___y_4141_);
lean_dec_ref(v___y_4157_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
lean_inc(v_fst_4152_);
v___x_4162_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4152_, v_b_4139_, v_a_4161_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v_a_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v_a_4164_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_a_4164_);
lean_dec(v_a_4163_);
v_a_4144_ = v_a_4164_;
goto v___jp_4143_;
}
else
{
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4174_; 
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
if (lean_obj_tag(v_a_4165_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; 
lean_dec(v___x_4135_);
v_a_4169_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v_a_4165_, 1);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 0);
lean_ctor_set(v___x_4167_, 0, v_a_4169_);
v___x_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
else
{
lean_object* v_a_4173_; 
lean_del_object(v___x_4167_);
v_a_4173_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v_a_4165_, 1);
v_a_4144_ = v_a_4173_;
goto v___jp_4143_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v___x_4135_);
v_a_4175_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4162_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4162_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec_ref(v_b_4139_);
lean_dec(v___x_4135_);
v_a_4183_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4160_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4160_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
v___jp_4143_:
{
size_t v___x_4145_; size_t v___x_4146_; 
v___x_4145_ = ((size_t)1ULL);
v___x_4146_ = lean_usize_add(v_i_4138_, v___x_4145_);
v_i_4138_ = v___x_4146_;
v_b_4139_ = v_a_4144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4198_, lean_object* v_as_4199_, lean_object* v_sz_4200_, lean_object* v_i_4201_, lean_object* v_b_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
size_t v_sz_boxed_4206_; size_t v_i_boxed_4207_; lean_object* v_res_4208_; 
v_sz_boxed_4206_ = lean_unbox_usize(v_sz_4200_);
lean_dec(v_sz_4200_);
v_i_boxed_4207_ = lean_unbox_usize(v_i_4201_);
lean_dec(v_i_4201_);
v_res_4208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4198_, v_as_4199_, v_sz_boxed_4206_, v_i_boxed_4207_, v_b_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec_ref(v_as_4199_);
return v_res_4208_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = l_Lean_maxRecDepth;
v___x_4216_ = l_Lean_Options_empty;
v___x_4217_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4218_, lean_object* v_linterOpts_4219_, lean_object* v_sp_4220_, lean_object* v_env_4221_, lean_object* v_mod_4222_){
_start:
{
lean_object* v_msg_4225_; lean_object* v_a_4230_; lean_object* v_a_4234_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v_a_4265_; lean_object* v___y_4269_; lean_object* v___y_4272_; lean_object* v___y_4273_; uint8_t v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; uint8_t v___y_4278_; uint8_t v___y_4279_; lean_object* v___y_4349_; lean_object* v___y_4350_; uint8_t v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; uint8_t v___y_4354_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v_env_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; uint8_t v___x_4373_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; lean_object* v_toCold_4408_; lean_object* v_currRecDepth_4409_; lean_object* v_ref_4410_; lean_object* v_currNamespace_4411_; lean_object* v_openDecls_4412_; lean_object* v_initHeartbeats_4413_; lean_object* v_maxHeartbeats_4414_; lean_object* v_currMacroScope_4415_; uint8_t v_suppressElabErrors_4416_; lean_object* v___y_4417_; uint8_t v___y_4433_; uint8_t v___x_4453_; 
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4250_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4251_ = lean_io_get_num_heartbeats();
v___x_4252_ = l_Lean_firstFrontendMacroScope;
v___x_4253_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4254_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4255_ = lean_box(0);
v___x_4256_ = lean_box(0);
v___x_4257_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4258_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4259_ = 1;
v___x_4260_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4261_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4262_, 0, v_env_4221_);
lean_ctor_set(v___x_4262_, 1, v___x_4253_);
lean_ctor_set(v___x_4262_, 2, v___x_4254_);
lean_ctor_set(v___x_4262_, 3, v___x_4257_);
lean_ctor_set(v___x_4262_, 4, v___x_4258_);
lean_ctor_set(v___x_4262_, 5, v___x_4249_);
lean_ctor_set(v___x_4262_, 6, v___x_4250_);
lean_ctor_set(v___x_4262_, 7, v___x_4260_);
lean_ctor_set(v___x_4262_, 8, v___x_4261_);
v___x_4263_ = lean_st_mk_ref(v___x_4262_);
v___x_4363_ = l_Lean_inheritedTraceOptions;
v___x_4364_ = lean_st_ref_get(v___x_4363_);
v___x_4365_ = lean_st_ref_get(v___x_4263_);
v_env_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc_ref(v_env_4366_);
lean_dec(v___x_4365_);
v___x_4367_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4368_ = l_Lean_instInhabitedFileMap_default;
v___x_4369_ = lean_box(0);
v___x_4370_ = l_Lean_Options_empty;
v___x_4371_ = lean_box(0);
v___x_4372_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4373_ = 0;
v___x_4404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4367_);
lean_ctor_set(v___x_4404_, 1, v___x_4368_);
lean_ctor_set(v___x_4404_, 2, v___x_4255_);
lean_ctor_set(v___x_4404_, 3, v___x_4369_);
lean_ctor_set(v___x_4404_, 4, v___x_4364_);
v___x_4405_ = l_Lean_Name_getRoot(v_mod_4222_);
v___x_4406_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4453_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4366_);
lean_dec_ref(v_env_4366_);
if (v___x_4406_ == 0)
{
if (v___x_4453_ == 0)
{
lean_inc(v___x_4263_);
v_toCold_4408_ = v___x_4404_;
v_currRecDepth_4409_ = v___x_4248_;
v_ref_4410_ = v___x_4371_;
v_currNamespace_4411_ = v___x_4255_;
v_openDecls_4412_ = v___x_4256_;
v_initHeartbeats_4413_ = v___x_4251_;
v_maxHeartbeats_4414_ = v___x_4372_;
v_currMacroScope_4415_ = v___x_4252_;
v_suppressElabErrors_4416_ = v___x_4373_;
v___y_4417_ = v___x_4263_;
goto v___jp_4407_;
}
else
{
v___y_4433_ = v___x_4406_;
goto v___jp_4432_;
}
}
else
{
v___y_4433_ = v___x_4453_;
goto v___jp_4432_;
}
v___jp_4224_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = l_Lean_MessageData_toString(v_msg_4225_);
v___x_4227_ = lean_mk_io_user_error(v___x_4226_);
v___x_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
v___jp_4229_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = lean_mk_io_user_error(v_a_4230_);
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
v___jp_4233_:
{
if (lean_obj_tag(v_a_4234_) == 0)
{
lean_object* v_msg_4235_; 
v_msg_4235_ = lean_ctor_get(v_a_4234_, 1);
lean_inc_ref(v_msg_4235_);
lean_dec_ref_known(v_a_4234_, 2);
v_msg_4225_ = v_msg_4235_;
goto v___jp_4224_;
}
else
{
lean_object* v_id_4236_; lean_object* v___x_4237_; 
v_id_4236_ = lean_ctor_get(v_a_4234_, 0);
lean_inc(v_id_4236_);
lean_dec_ref_known(v_a_4234_, 2);
v___x_4237_ = l_Lean_InternalExceptionId_getName(v_id_4236_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec(v_id_4236_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___x_4239_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4240_ = 1;
v___x_4241_ = l_Lean_Name_toString(v_a_4238_, v___x_4240_);
v___x_4242_ = lean_string_append(v___x_4239_, v___x_4241_);
lean_dec_ref(v___x_4241_);
v_a_4230_ = v___x_4242_;
goto v___jp_4229_;
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_dec_ref_known(v___x_4237_, 1);
v___x_4243_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4244_ = l_Nat_reprFast(v_id_4236_);
v___x_4245_ = lean_string_append(v___x_4243_, v___x_4244_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4247_ = lean_string_append(v___x_4245_, v___x_4246_);
v_a_4230_ = v___x_4247_;
goto v___jp_4229_;
}
}
}
v___jp_4264_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = lean_st_ref_get(v___x_4263_);
lean_dec(v___x_4263_);
lean_dec(v___x_4266_);
v___x_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4267_, 0, v_a_4265_);
return v___x_4267_;
}
v___jp_4268_:
{
lean_object* v_a_4270_; 
v_a_4270_ = lean_ctor_get(v___y_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref(v___y_4269_);
v_a_4265_ = v_a_4270_;
goto v___jp_4264_;
}
v___jp_4271_:
{
switch(v___y_4274_)
{
case 0:
{
lean_dec(v_sp_4220_);
if (v___y_4279_ == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_dec_ref(v___y_4275_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
v___x_4280_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4222_, v___x_4259_);
v___x_4282_ = lean_string_append(v___x_4280_, v___x_4281_);
lean_dec_ref(v___x_4281_);
v___x_4283_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4284_ = lean_string_append(v___x_4282_, v___x_4283_);
v___x_4285_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4279_, v_a_4286_, v___y_4277_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4277_);
v___y_4269_ = v___x_4287_;
goto v___jp_4268_;
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec(v___x_4263_);
v_a_4288_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4290_ = v___x_4285_;
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4285_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4294_; 
v___x_4292_ = lean_io_error_to_string(v_a_4288_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 3);
lean_ctor_set(v___x_4290_, 0, v___x_4292_);
v___x_4294_ = v___x_4290_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4292_);
v___x_4294_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_MessageData_ofFormat(v___x_4294_);
v_msg_4225_ = v___x_4295_;
goto v___jp_4224_;
}
}
}
}
else
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4298_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4299_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4222_, v___y_4279_);
v___x_4300_ = lean_string_append(v___x_4298_, v___x_4299_);
lean_dec_ref(v___x_4299_);
v___x_4301_ = lean_array_get_size(v___y_4273_);
lean_dec_ref(v___y_4273_);
v___x_4302_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4275_, v___y_4272_, v___x_4259_, v___x_4300_, v___x_4301_, v___x_4259_, v___y_4277_, v___y_4276_);
lean_dec_ref(v___y_4272_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = l_Lean_MessageData_toString(v_a_4303_);
v___x_4305_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4307_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___x_4307_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4279_, v_a_4306_, v___y_4277_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4277_);
v___y_4269_ = v___x_4307_;
goto v___jp_4268_;
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4317_; 
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec(v___x_4263_);
v_a_4308_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4310_ = v___x_4305_;
v_isShared_4311_ = v_isSharedCheck_4317_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4305_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4317_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; lean_object* v___x_4314_; 
v___x_4312_ = lean_io_error_to_string(v_a_4308_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set_tag(v___x_4310_, 3);
lean_ctor_set(v___x_4310_, 0, v___x_4312_);
v___x_4314_ = v___x_4310_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Lean_MessageData_ofFormat(v___x_4314_);
v_msg_4225_ = v___x_4315_;
goto v___jp_4224_;
}
}
}
}
else
{
lean_object* v_a_4318_; 
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec(v___x_4263_);
v_a_4318_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4302_, 1);
v_a_4234_ = v_a_4318_;
goto v___jp_4233_;
}
}
}
case 1:
{
lean_object* v___x_4319_; lean_object* v_env_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; size_t v_sz_4324_; size_t v___x_4325_; lean_object* v___x_4326_; 
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v_mod_4222_);
v___x_4319_ = lean_st_ref_get(v___y_4276_);
v_env_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc_ref(v_env_4320_);
lean_dec(v___x_4319_);
v___x_4321_ = l_Lean_Environment_mainModule(v_env_4320_);
lean_dec_ref(v_env_4320_);
v___x_4322_ = lean_box(v___y_4278_);
v___x_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4261_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v_sz_4324_ = lean_array_size(v___y_4275_);
v___x_4325_ = ((size_t)0ULL);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4220_, v___x_4321_, v___y_4275_, v_sz_4324_, v___x_4325_, v___x_4323_, v___y_4277_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v___y_4275_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v_fst_4328_; lean_object* v_snd_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4326_, 1);
v_fst_4328_ = lean_ctor_get(v_a_4327_, 0);
lean_inc(v_fst_4328_);
v_snd_4329_ = lean_ctor_get(v_a_4327_, 1);
lean_inc(v_snd_4329_);
lean_dec(v_a_4327_);
v___x_4330_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4330_, 0, v_fst_4328_);
v___x_4331_ = lean_unbox(v_snd_4329_);
lean_dec(v_snd_4329_);
lean_ctor_set_uint8(v___x_4330_, sizeof(void*)*1, v___x_4331_);
v_a_4265_ = v___x_4330_;
goto v___jp_4264_;
}
else
{
lean_object* v_a_4332_; 
lean_dec(v___x_4263_);
v_a_4332_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4326_, 1);
v_a_4234_ = v_a_4332_;
goto v___jp_4233_;
}
}
default: 
{
lean_object* v___x_4333_; lean_object* v_env_4334_; lean_object* v___x_4335_; size_t v_sz_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v_mod_4222_);
lean_dec(v_sp_4220_);
v___x_4333_ = lean_st_ref_get(v___y_4276_);
v_env_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc_ref(v_env_4334_);
lean_dec(v___x_4333_);
v___x_4335_ = l_Lean_Environment_mainModule(v_env_4334_);
lean_dec_ref(v_env_4334_);
v_sz_4336_ = lean_array_size(v___y_4275_);
v___x_4337_ = ((size_t)0ULL);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4335_, v___y_4275_, v_sz_4336_, v___x_4337_, v___x_4261_, v___y_4277_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v___y_4275_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 2);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
v_a_4265_ = v___x_4344_;
goto v___jp_4264_;
}
}
}
else
{
lean_object* v_a_4347_; 
lean_dec(v___x_4263_);
v_a_4347_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4338_, 1);
v_a_4234_ = v_a_4347_;
goto v___jp_4233_;
}
}
}
}
v___jp_4348_:
{
lean_object* v___x_4355_; 
lean_inc_ref(v___y_4350_);
v___x_4355_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4349_, v___y_4350_, v___y_4353_, v___y_4352_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = lean_array_get_size(v_a_4356_);
v___x_4358_ = lean_nat_dec_lt(v___x_4248_, v___x_4357_);
if (v___x_4358_ == 0)
{
v___y_4272_ = v___y_4349_;
v___y_4273_ = v___y_4350_;
v___y_4274_ = v___y_4351_;
v___y_4275_ = v_a_4356_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v___y_4354_;
v___y_4279_ = v___x_4358_;
goto v___jp_4271_;
}
else
{
if (v___x_4358_ == 0)
{
v___y_4272_ = v___y_4349_;
v___y_4273_ = v___y_4350_;
v___y_4274_ = v___y_4351_;
v___y_4275_ = v_a_4356_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v___y_4354_;
v___y_4279_ = v___x_4358_;
goto v___jp_4271_;
}
else
{
size_t v___x_4359_; size_t v___x_4360_; uint8_t v___x_4361_; 
v___x_4359_ = ((size_t)0ULL);
v___x_4360_ = lean_usize_of_nat(v___x_4357_);
v___x_4361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4354_, v_a_4356_, v___x_4359_, v___x_4360_);
v___y_4272_ = v___y_4349_;
v___y_4273_ = v___y_4350_;
v___y_4274_ = v___y_4351_;
v___y_4275_ = v_a_4356_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v___y_4354_;
v___y_4279_ = v___x_4361_;
goto v___jp_4271_;
}
}
}
else
{
lean_object* v_a_4362_; 
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___x_4263_);
lean_dec(v_mod_4222_);
lean_dec(v_sp_4220_);
v_a_4362_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4355_, 1);
v_a_4234_ = v_a_4362_;
goto v___jp_4233_;
}
}
v___jp_4374_:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4379_, v___y_4378_, v___y_4377_);
lean_dec(v___y_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4382_; uint8_t v___x_4383_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4380_, 1);
v___x_4382_ = lean_array_get_size(v_a_4381_);
v___x_4383_ = lean_nat_dec_eq(v___x_4382_, v___x_4248_);
if (v___x_4383_ == 0)
{
v___y_4349_ = v___y_4375_;
v___y_4350_ = v_a_4381_;
v___y_4351_ = v___y_4376_;
v___y_4352_ = v___y_4377_;
v___y_4353_ = v___y_4378_;
v___y_4354_ = v___x_4383_;
goto v___jp_4348_;
}
else
{
uint8_t v___x_4384_; uint8_t v___x_4385_; 
v___x_4384_ = 0;
v___x_4385_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4376_, v___x_4384_);
if (v___x_4385_ == 0)
{
v___y_4349_ = v___y_4375_;
v___y_4350_ = v_a_4381_;
v___y_4351_ = v___y_4376_;
v___y_4352_ = v___y_4377_;
v___y_4353_ = v___y_4378_;
v___y_4354_ = v___x_4385_;
goto v___jp_4348_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec(v_a_4381_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4375_);
lean_dec(v_sp_4220_);
v___x_4386_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4222_, v___x_4385_);
v___x_4388_ = lean_string_append(v___x_4386_, v___x_4387_);
lean_dec_ref(v___x_4387_);
v___x_4389_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4390_ = lean_string_append(v___x_4388_, v___x_4389_);
v___x_4391_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4390_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v___x_4392_; 
lean_dec_ref_known(v___x_4391_, 1);
v___x_4392_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4265_ = v___x_4392_;
goto v___jp_4264_;
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v___x_4263_);
v_a_4393_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4395_ = v___x_4391_;
v_isShared_4396_ = v_isSharedCheck_4402_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4391_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4402_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4397_ = lean_io_error_to_string(v_a_4393_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 3);
lean_ctor_set(v___x_4395_, 0, v___x_4397_);
v___x_4399_ = v___x_4395_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_MessageData_ofFormat(v___x_4399_);
v_msg_4225_ = v___x_4400_;
goto v___jp_4224_;
}
}
}
}
}
}
else
{
lean_object* v_a_4403_; 
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4375_);
lean_dec(v___x_4263_);
lean_dec(v_mod_4222_);
lean_dec(v_sp_4220_);
v_a_4403_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4380_, 1);
v_a_4234_ = v_a_4403_;
goto v___jp_4233_;
}
}
v___jp_4407_:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4405_, v___y_4417_);
lean_dec(v___x_4405_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4430_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4430_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4430_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
uint8_t v_lintOnly_4423_; uint8_t v_mode_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v_lintOnly_4423_ = lean_ctor_get_uint8(v_args_4218_, sizeof(void*)*4);
v_mode_4424_ = lean_ctor_get_uint8(v_args_4218_, sizeof(void*)*4 + 1);
v___x_4425_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4415_);
lean_inc(v_maxHeartbeats_4414_);
lean_inc(v_openDecls_4412_);
lean_inc(v_currNamespace_4411_);
lean_inc(v_ref_4410_);
v___x_4426_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_4426_, 0, v_toCold_4408_);
lean_ctor_set(v___x_4426_, 1, v___x_4370_);
lean_ctor_set(v___x_4426_, 2, v_currRecDepth_4409_);
lean_ctor_set(v___x_4426_, 3, v___x_4425_);
lean_ctor_set(v___x_4426_, 4, v_ref_4410_);
lean_ctor_set(v___x_4426_, 5, v_currNamespace_4411_);
lean_ctor_set(v___x_4426_, 6, v_openDecls_4412_);
lean_ctor_set(v___x_4426_, 7, v_initHeartbeats_4413_);
lean_ctor_set(v___x_4426_, 8, v_maxHeartbeats_4414_);
lean_ctor_set(v___x_4426_, 9, v_currMacroScope_4415_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*10, v___x_4406_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*10 + 1, v_suppressElabErrors_4416_);
if (v_lintOnly_4423_ == 0)
{
lean_del_object(v___x_4421_);
lean_dec_ref(v_linterOpts_4219_);
v___y_4375_ = v_a_4419_;
v___y_4376_ = v_mode_4424_;
v___y_4377_ = v___y_4417_;
v___y_4378_ = v___x_4426_;
v___y_4379_ = v___x_4369_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4428_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set_tag(v___x_4421_, 1);
lean_ctor_set(v___x_4421_, 0, v_linterOpts_4219_);
v___x_4428_ = v___x_4421_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_linterOpts_4219_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
v___y_4375_ = v_a_4419_;
v___y_4376_ = v_mode_4424_;
v___y_4377_ = v___y_4417_;
v___y_4378_ = v___x_4426_;
v___y_4379_ = v___x_4428_;
goto v___jp_4374_;
}
}
}
}
else
{
lean_object* v_a_4431_; 
lean_dec(v___y_4417_);
lean_dec(v_initHeartbeats_4413_);
lean_dec(v_currRecDepth_4409_);
lean_dec_ref(v_toCold_4408_);
lean_dec(v___x_4263_);
lean_dec(v_mod_4222_);
lean_dec(v_sp_4220_);
lean_dec_ref(v_linterOpts_4219_);
v_a_4431_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v___x_4418_, 1);
v_a_4234_ = v_a_4431_;
goto v___jp_4233_;
}
}
v___jp_4432_:
{
if (v___y_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v_env_4435_; lean_object* v_nextMacroScope_4436_; lean_object* v_ngen_4437_; lean_object* v_auxDeclNGen_4438_; lean_object* v_traceState_4439_; lean_object* v_messages_4440_; lean_object* v_infoState_4441_; lean_object* v_snapshotTasks_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4451_; 
v___x_4434_ = lean_st_ref_take(v___x_4263_);
v_env_4435_ = lean_ctor_get(v___x_4434_, 0);
v_nextMacroScope_4436_ = lean_ctor_get(v___x_4434_, 1);
v_ngen_4437_ = lean_ctor_get(v___x_4434_, 2);
v_auxDeclNGen_4438_ = lean_ctor_get(v___x_4434_, 3);
v_traceState_4439_ = lean_ctor_get(v___x_4434_, 4);
v_messages_4440_ = lean_ctor_get(v___x_4434_, 6);
v_infoState_4441_ = lean_ctor_get(v___x_4434_, 7);
v_snapshotTasks_4442_ = lean_ctor_get(v___x_4434_, 8);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4451_ == 0)
{
lean_object* v_unused_4452_; 
v_unused_4452_ = lean_ctor_get(v___x_4434_, 5);
lean_dec(v_unused_4452_);
v___x_4444_ = v___x_4434_;
v_isShared_4445_ = v_isSharedCheck_4451_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_snapshotTasks_4442_);
lean_inc(v_infoState_4441_);
lean_inc(v_messages_4440_);
lean_inc(v_traceState_4439_);
lean_inc(v_auxDeclNGen_4438_);
lean_inc(v_ngen_4437_);
lean_inc(v_nextMacroScope_4436_);
lean_inc(v_env_4435_);
lean_dec(v___x_4434_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4451_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = l_Lean_Kernel_enableDiag(v_env_4435_, v___x_4406_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 5, v___x_4249_);
lean_ctor_set(v___x_4444_, 0, v___x_4446_);
v___x_4448_ = v___x_4444_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4446_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_nextMacroScope_4436_);
lean_ctor_set(v_reuseFailAlloc_4450_, 2, v_ngen_4437_);
lean_ctor_set(v_reuseFailAlloc_4450_, 3, v_auxDeclNGen_4438_);
lean_ctor_set(v_reuseFailAlloc_4450_, 4, v_traceState_4439_);
lean_ctor_set(v_reuseFailAlloc_4450_, 5, v___x_4249_);
lean_ctor_set(v_reuseFailAlloc_4450_, 6, v_messages_4440_);
lean_ctor_set(v_reuseFailAlloc_4450_, 7, v_infoState_4441_);
lean_ctor_set(v_reuseFailAlloc_4450_, 8, v_snapshotTasks_4442_);
v___x_4448_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; 
v___x_4449_ = lean_st_ref_put(v___x_4263_, v___x_4448_);
lean_inc(v___x_4263_);
v_toCold_4408_ = v___x_4404_;
v_currRecDepth_4409_ = v___x_4248_;
v_ref_4410_ = v___x_4371_;
v_currNamespace_4411_ = v___x_4255_;
v_openDecls_4412_ = v___x_4256_;
v_initHeartbeats_4413_ = v___x_4251_;
v_maxHeartbeats_4414_ = v___x_4372_;
v_currMacroScope_4415_ = v___x_4252_;
v_suppressElabErrors_4416_ = v___x_4373_;
v___y_4417_ = v___x_4263_;
goto v___jp_4407_;
}
}
}
else
{
lean_inc(v___x_4263_);
v_toCold_4408_ = v___x_4404_;
v_currRecDepth_4409_ = v___x_4248_;
v_ref_4410_ = v___x_4371_;
v_currNamespace_4411_ = v___x_4255_;
v_openDecls_4412_ = v___x_4256_;
v_initHeartbeats_4413_ = v___x_4251_;
v_maxHeartbeats_4414_ = v___x_4372_;
v_currMacroScope_4415_ = v___x_4252_;
v_suppressElabErrors_4416_ = v___x_4373_;
v___y_4417_ = v___x_4263_;
goto v___jp_4407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4454_, lean_object* v_linterOpts_4455_, lean_object* v_sp_4456_, lean_object* v_env_4457_, lean_object* v_mod_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4454_, v_linterOpts_4455_, v_sp_4456_, v_env_4457_, v_mod_4458_);
lean_dec_ref(v_args_4454_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4461_, lean_object* v_t_4462_, lean_object* v_k_4463_, lean_object* v_fallback_4464_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4462_, v_k_4463_, v_fallback_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4466_, lean_object* v_t_4467_, lean_object* v_k_4468_, lean_object* v_fallback_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4466_, v_t_4467_, v_k_4468_, v_fallback_4469_);
lean_dec(v_fallback_4469_);
lean_dec_ref(v_k_4468_);
lean_dec(v_t_4467_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4471_, lean_object* v_k_4472_, lean_object* v_v_4473_, lean_object* v_t_4474_, lean_object* v_hl_4475_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4472_, v_v_4473_, v_t_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4477_, lean_object* v_init_4478_, lean_object* v_x_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4477_, v_init_4478_, v_x_4479_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4484_, lean_object* v_init_4485_, lean_object* v_x_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4484_, v_init_4485_, v_x_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4491_, lean_object* v_constName_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4492_, v___y_4493_, v___y_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4497_, lean_object* v_constName_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4497_, v_constName_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4503_, lean_object* v_ref_4504_, lean_object* v_constName_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4504_, v_constName_4505_, v___y_4506_, v___y_4507_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4510_, lean_object* v_ref_4511_, lean_object* v_constName_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4510_, v_ref_4511_, v_constName_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v_ref_4511_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4517_, lean_object* v_ref_4518_, lean_object* v_msg_4519_, lean_object* v_declHint_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4518_, v_msg_4519_, v_declHint_4520_, v___y_4521_, v___y_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4525_, lean_object* v_ref_4526_, lean_object* v_msg_4527_, lean_object* v_declHint_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4525_, v_ref_4526_, v_msg_4527_, v_declHint_4528_, v___y_4529_, v___y_4530_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v_ref_4526_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4533_, lean_object* v_declHint_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4533_, v_declHint_4534_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4539_, lean_object* v_declHint_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4539_, v_declHint_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4545_, lean_object* v_ref_4546_, lean_object* v_msg_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4546_, v_msg_4547_, v___y_4548_, v___y_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4552_, lean_object* v_ref_4553_, lean_object* v_msg_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4552_, v_ref_4553_, v_msg_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v_ref_4553_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4559_, lean_object* v_msg_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4560_, v___y_4561_, v___y_4562_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4565_, lean_object* v_msg_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4565_, v_msg_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4571_){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; uint32_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4573_ = l_Std_Format_defWidth;
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = l_Std_Format_pretty(v_s_4571_, v___x_4573_, v___x_4574_, v___x_4574_);
v___x_4576_ = 10;
v___x_4577_ = lean_string_push(v___x_4575_, v___x_4576_);
v___x_4578_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4582_, size_t v_sz_4583_, size_t v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_){
_start:
{
uint8_t v___x_4588_; 
v___x_4588_ = lean_usize_dec_lt(v_i_4584_, v_sz_4583_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_b_4585_);
return v___x_4589_;
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_a_4590_ = lean_array_uget_borrowed(v_as_4582_, v_i_4584_);
v___x_4591_ = lean_box(0);
lean_inc(v_a_4590_);
v___x_4592_ = l_Lean_MessageData_format(v_a_4590_, v___x_4591_);
v___x_4593_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4592_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v___x_4594_; size_t v___x_4595_; size_t v___x_4596_; 
lean_dec_ref_known(v___x_4593_, 1);
v___x_4594_ = lean_box(0);
v___x_4595_ = ((size_t)1ULL);
v___x_4596_ = lean_usize_add(v_i_4584_, v___x_4595_);
v_i_4584_ = v___x_4596_;
v_b_4585_ = v___x_4594_;
goto _start;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4610_; 
v_a_4598_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4600_ = v___x_4593_;
v_isShared_4601_ = v_isSharedCheck_4610_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4593_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4610_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v_ref_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4608_; 
v_ref_4602_ = lean_ctor_get(v___y_4586_, 4);
v___x_4603_ = lean_io_error_to_string(v_a_4598_);
v___x_4604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4603_);
v___x_4605_ = l_Lean_MessageData_ofFormat(v___x_4604_);
lean_inc(v_ref_4602_);
v___x_4606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4606_, 0, v_ref_4602_);
lean_ctor_set(v___x_4606_, 1, v___x_4605_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4606_);
v___x_4608_ = v___x_4600_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4611_, lean_object* v_sz_4612_, lean_object* v_i_4613_, lean_object* v_b_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
size_t v_sz_boxed_4617_; size_t v_i_boxed_4618_; lean_object* v_res_4619_; 
v_sz_boxed_4617_ = lean_unbox_usize(v_sz_4612_);
lean_dec(v_sz_4612_);
v_i_boxed_4618_ = lean_unbox_usize(v_i_4613_);
lean_dec(v_i_4613_);
v_res_4619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4611_, v_sz_boxed_4617_, v_i_boxed_4618_, v_b_4614_, v___y_4615_);
lean_dec_ref(v___y_4615_);
lean_dec_ref(v_as_4611_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4620_, lean_object* v_entries_4621_, lean_object* v_____r_4622_, uint8_t v_anyFailed_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v___x_4627_; size_t v_sz_4628_; size_t v___x_4629_; lean_object* v___x_4630_; 
v___x_4627_ = lean_box(0);
v_sz_4628_ = lean_array_size(v_errors_4620_);
v___x_4629_ = ((size_t)0ULL);
v___x_4630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4620_, v_sz_4628_, v___x_4629_, v___x_4627_, v___y_4624_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4639_; 
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; 
v_unused_4640_ = lean_ctor_get(v___x_4630_, 0);
lean_dec(v_unused_4640_);
v___x_4632_ = v___x_4630_;
v_isShared_4633_ = v_isSharedCheck_4639_;
goto v_resetjp_4631_;
}
else
{
lean_dec(v___x_4630_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4639_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v___x_4634_ = lean_box(v_anyFailed_4623_);
v___x_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4635_, 0, v_entries_4621_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
if (v_isShared_4633_ == 0)
{
lean_ctor_set(v___x_4632_, 0, v___x_4635_);
v___x_4637_ = v___x_4632_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec_ref(v_entries_4621_);
v_a_4641_ = lean_ctor_get(v___x_4630_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4630_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4630_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4649_, lean_object* v_entries_4650_, lean_object* v_____r_4651_, lean_object* v_anyFailed_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
uint8_t v_anyFailed_boxed_4656_; lean_object* v_res_4657_; 
v_anyFailed_boxed_4656_ = lean_unbox(v_anyFailed_4652_);
v_res_4657_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4649_, v_entries_4650_, v_____r_4651_, v_anyFailed_boxed_4656_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec_ref(v_errors_4649_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4658_, lean_object* v_env_4659_, lean_object* v_mod_4660_){
_start:
{
lean_object* v_a_4663_; lean_object* v_a_4667_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___y_4703_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v_env_4721_; uint8_t v_anyFailed_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; uint8_t v___x_4730_; lean_object* v_toCold_4732_; lean_object* v_currRecDepth_4733_; lean_object* v_ref_4734_; lean_object* v_currNamespace_4735_; lean_object* v_openDecls_4736_; lean_object* v_initHeartbeats_4737_; lean_object* v_maxHeartbeats_4738_; lean_object* v_currMacroScope_4739_; uint8_t v_suppressElabErrors_4740_; lean_object* v___y_4741_; uint8_t v___y_4760_; uint8_t v___x_4780_; 
v___x_4684_ = lean_unsigned_to_nat(0u);
v___x_4685_ = lean_unsigned_to_nat(32u);
v___x_4686_ = lean_mk_empty_array_with_capacity(v___x_4685_);
lean_dec_ref(v___x_4686_);
v___x_4687_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4688_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4689_ = lean_io_get_num_heartbeats();
v___x_4690_ = l_Lean_firstFrontendMacroScope;
v___x_4691_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4692_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4693_ = lean_box(0);
v___x_4694_ = lean_box(0);
v___x_4695_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4696_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4697_ = 1;
v___x_4698_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4699_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4700_, 0, v_env_4659_);
lean_ctor_set(v___x_4700_, 1, v___x_4691_);
lean_ctor_set(v___x_4700_, 2, v___x_4692_);
lean_ctor_set(v___x_4700_, 3, v___x_4695_);
lean_ctor_set(v___x_4700_, 4, v___x_4696_);
lean_ctor_set(v___x_4700_, 5, v___x_4687_);
lean_ctor_set(v___x_4700_, 6, v___x_4688_);
lean_ctor_set(v___x_4700_, 7, v___x_4698_);
lean_ctor_set(v___x_4700_, 8, v___x_4699_);
v___x_4701_ = lean_st_mk_ref(v___x_4700_);
v___x_4718_ = l_Lean_inheritedTraceOptions;
v___x_4719_ = lean_st_ref_get(v___x_4718_);
v___x_4720_ = lean_st_ref_get(v___x_4701_);
v_env_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc_ref(v_env_4721_);
lean_dec(v___x_4720_);
v_anyFailed_4722_ = 0;
v___x_4723_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4724_ = l_Lean_instInhabitedFileMap_default;
v___x_4725_ = lean_box(0);
v___x_4726_ = l_Lean_Options_empty;
v___x_4727_ = lean_box(0);
v___x_4728_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4723_);
lean_ctor_set(v___x_4729_, 1, v___x_4724_);
lean_ctor_set(v___x_4729_, 2, v___x_4693_);
lean_ctor_set(v___x_4729_, 3, v___x_4725_);
lean_ctor_set(v___x_4729_, 4, v___x_4719_);
v___x_4730_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4780_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4721_);
lean_dec_ref(v_env_4721_);
if (v___x_4730_ == 0)
{
if (v___x_4780_ == 0)
{
lean_inc(v___x_4701_);
v_toCold_4732_ = v___x_4729_;
v_currRecDepth_4733_ = v___x_4684_;
v_ref_4734_ = v___x_4727_;
v_currNamespace_4735_ = v___x_4693_;
v_openDecls_4736_ = v___x_4694_;
v_initHeartbeats_4737_ = v___x_4689_;
v_maxHeartbeats_4738_ = v___x_4728_;
v_currMacroScope_4739_ = v___x_4690_;
v_suppressElabErrors_4740_ = v_anyFailed_4722_;
v___y_4741_ = v___x_4701_;
goto v___jp_4731_;
}
else
{
v___y_4760_ = v___x_4730_;
goto v___jp_4759_;
}
}
else
{
v___y_4760_ = v___x_4780_;
goto v___jp_4759_;
}
v___jp_4662_:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4664_ = lean_mk_io_user_error(v_a_4663_);
v___x_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4664_);
return v___x_4665_;
}
v___jp_4666_:
{
if (lean_obj_tag(v_a_4667_) == 0)
{
lean_object* v_msg_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_msg_4668_ = lean_ctor_get(v_a_4667_, 1);
lean_inc_ref(v_msg_4668_);
lean_dec_ref_known(v_a_4667_, 2);
v___x_4669_ = l_Lean_MessageData_toString(v_msg_4668_);
v___x_4670_ = lean_mk_io_user_error(v___x_4669_);
v___x_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
else
{
lean_object* v_id_4672_; lean_object* v___x_4673_; 
v_id_4672_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_id_4672_);
lean_dec_ref_known(v_a_4667_, 2);
v___x_4673_ = l_Lean_InternalExceptionId_getName(v_id_4672_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
lean_dec(v_id_4672_);
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v___x_4675_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4676_ = 1;
v___x_4677_ = l_Lean_Name_toString(v_a_4674_, v___x_4676_);
v___x_4678_ = lean_string_append(v___x_4675_, v___x_4677_);
lean_dec_ref(v___x_4677_);
v_a_4663_ = v___x_4678_;
goto v___jp_4662_;
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
lean_dec_ref_known(v___x_4673_, 1);
v___x_4679_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4680_ = l_Nat_reprFast(v_id_4672_);
v___x_4681_ = lean_string_append(v___x_4679_, v___x_4680_);
lean_dec_ref(v___x_4680_);
v___x_4682_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4683_ = lean_string_append(v___x_4681_, v___x_4682_);
v_a_4663_ = v___x_4683_;
goto v___jp_4662_;
}
}
}
v___jp_4702_:
{
if (lean_obj_tag(v___y_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4716_; 
v_a_4704_ = lean_ctor_get(v___y_4703_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___y_4703_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4706_ = v___y_4703_;
v_isShared_4707_ = v_isSharedCheck_4716_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___y_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4716_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v_fst_4709_; lean_object* v_snd_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; lean_object* v___x_4714_; 
v___x_4708_ = lean_st_ref_get(v___x_4701_);
lean_dec(v___x_4701_);
lean_dec(v___x_4708_);
v_fst_4709_ = lean_ctor_get(v_a_4704_, 0);
lean_inc(v_fst_4709_);
v_snd_4710_ = lean_ctor_get(v_a_4704_, 1);
lean_inc(v_snd_4710_);
lean_dec(v_a_4704_);
v___x_4711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4711_, 0, v_fst_4709_);
v___x_4712_ = lean_unbox(v_snd_4710_);
lean_dec(v_snd_4710_);
lean_ctor_set_uint8(v___x_4711_, sizeof(void*)*1, v___x_4712_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4711_);
v___x_4714_ = v___x_4706_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4711_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
else
{
lean_object* v_a_4717_; 
lean_dec(v___x_4701_);
v_a_4717_ = lean_ctor_get(v___y_4703_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___y_4703_, 1);
v_a_4667_ = v_a_4717_;
goto v___jp_4666_;
}
}
v___jp_4731_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4739_);
lean_inc(v_maxHeartbeats_4738_);
lean_inc(v_openDecls_4736_);
lean_inc(v_currNamespace_4735_);
lean_inc(v_ref_4734_);
v___x_4743_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_4743_, 0, v_toCold_4732_);
lean_ctor_set(v___x_4743_, 1, v___x_4726_);
lean_ctor_set(v___x_4743_, 2, v_currRecDepth_4733_);
lean_ctor_set(v___x_4743_, 3, v___x_4742_);
lean_ctor_set(v___x_4743_, 4, v_ref_4734_);
lean_ctor_set(v___x_4743_, 5, v_currNamespace_4735_);
lean_ctor_set(v___x_4743_, 6, v_openDecls_4736_);
lean_ctor_set(v___x_4743_, 7, v_initHeartbeats_4737_);
lean_ctor_set(v___x_4743_, 8, v_maxHeartbeats_4738_);
lean_ctor_set(v___x_4743_, 9, v_currMacroScope_4739_);
lean_ctor_set_uint8(v___x_4743_, sizeof(void*)*10, v___x_4730_);
lean_ctor_set_uint8(v___x_4743_, sizeof(void*)*10 + 1, v_suppressElabErrors_4740_);
v___x_4744_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4743_, v___y_4741_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v___x_4746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4746_, 0, v_sp_4658_);
lean_ctor_set(v___x_4746_, 1, v_mod_4660_);
v___x_4747_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4745_, v___x_4746_, v___x_4743_, v___y_4741_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v_entries_4749_; lean_object* v_errors_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4747_, 1);
v_entries_4749_ = lean_ctor_get(v_a_4748_, 0);
lean_inc_ref(v_entries_4749_);
v_errors_4750_ = lean_ctor_get(v_a_4748_, 1);
lean_inc_ref(v_errors_4750_);
lean_dec(v_a_4748_);
v___x_4751_ = lean_array_get_size(v_errors_4750_);
v___x_4752_ = lean_nat_dec_eq(v___x_4751_, v___x_4684_);
if (v___x_4752_ == 0)
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = lean_box(0);
v___x_4754_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4750_, v_entries_4749_, v___x_4753_, v___x_4697_, v___x_4743_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref_known(v___x_4743_, 10);
lean_dec_ref(v_errors_4750_);
v___y_4703_ = v___x_4754_;
goto v___jp_4702_;
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = lean_box(0);
v___x_4756_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4750_, v_entries_4749_, v___x_4755_, v_anyFailed_4722_, v___x_4743_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref_known(v___x_4743_, 10);
lean_dec_ref(v_errors_4750_);
v___y_4703_ = v___x_4756_;
goto v___jp_4702_;
}
}
else
{
lean_object* v_a_4757_; 
lean_dec_ref_known(v___x_4743_, 10);
lean_dec(v___y_4741_);
lean_dec(v___x_4701_);
v_a_4757_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4747_, 1);
v_a_4667_ = v_a_4757_;
goto v___jp_4666_;
}
}
else
{
lean_object* v_a_4758_; 
lean_dec_ref_known(v___x_4743_, 10);
lean_dec(v___y_4741_);
lean_dec(v___x_4701_);
lean_dec(v_mod_4660_);
lean_dec(v_sp_4658_);
v_a_4758_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4744_, 1);
v_a_4667_ = v_a_4758_;
goto v___jp_4666_;
}
}
v___jp_4759_:
{
if (v___y_4760_ == 0)
{
lean_object* v___x_4761_; lean_object* v_env_4762_; lean_object* v_nextMacroScope_4763_; lean_object* v_ngen_4764_; lean_object* v_auxDeclNGen_4765_; lean_object* v_traceState_4766_; lean_object* v_messages_4767_; lean_object* v_infoState_4768_; lean_object* v_snapshotTasks_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4778_; 
v___x_4761_ = lean_st_ref_take(v___x_4701_);
v_env_4762_ = lean_ctor_get(v___x_4761_, 0);
v_nextMacroScope_4763_ = lean_ctor_get(v___x_4761_, 1);
v_ngen_4764_ = lean_ctor_get(v___x_4761_, 2);
v_auxDeclNGen_4765_ = lean_ctor_get(v___x_4761_, 3);
v_traceState_4766_ = lean_ctor_get(v___x_4761_, 4);
v_messages_4767_ = lean_ctor_get(v___x_4761_, 6);
v_infoState_4768_ = lean_ctor_get(v___x_4761_, 7);
v_snapshotTasks_4769_ = lean_ctor_get(v___x_4761_, 8);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4778_ == 0)
{
lean_object* v_unused_4779_; 
v_unused_4779_ = lean_ctor_get(v___x_4761_, 5);
lean_dec(v_unused_4779_);
v___x_4771_ = v___x_4761_;
v_isShared_4772_ = v_isSharedCheck_4778_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_snapshotTasks_4769_);
lean_inc(v_infoState_4768_);
lean_inc(v_messages_4767_);
lean_inc(v_traceState_4766_);
lean_inc(v_auxDeclNGen_4765_);
lean_inc(v_ngen_4764_);
lean_inc(v_nextMacroScope_4763_);
lean_inc(v_env_4762_);
lean_dec(v___x_4761_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4778_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4773_; lean_object* v___x_4775_; 
v___x_4773_ = l_Lean_Kernel_enableDiag(v_env_4762_, v___x_4730_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 5, v___x_4687_);
lean_ctor_set(v___x_4771_, 0, v___x_4773_);
v___x_4775_ = v___x_4771_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4773_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_nextMacroScope_4763_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_ngen_4764_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v_auxDeclNGen_4765_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_traceState_4766_);
lean_ctor_set(v_reuseFailAlloc_4777_, 5, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4777_, 6, v_messages_4767_);
lean_ctor_set(v_reuseFailAlloc_4777_, 7, v_infoState_4768_);
lean_ctor_set(v_reuseFailAlloc_4777_, 8, v_snapshotTasks_4769_);
v___x_4775_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4776_; 
v___x_4776_ = lean_st_ref_put(v___x_4701_, v___x_4775_);
lean_inc(v___x_4701_);
v_toCold_4732_ = v___x_4729_;
v_currRecDepth_4733_ = v___x_4684_;
v_ref_4734_ = v___x_4727_;
v_currNamespace_4735_ = v___x_4693_;
v_openDecls_4736_ = v___x_4694_;
v_initHeartbeats_4737_ = v___x_4689_;
v_maxHeartbeats_4738_ = v___x_4728_;
v_currMacroScope_4739_ = v___x_4690_;
v_suppressElabErrors_4740_ = v_anyFailed_4722_;
v___y_4741_ = v___x_4701_;
goto v___jp_4731_;
}
}
}
else
{
lean_inc(v___x_4701_);
v_toCold_4732_ = v___x_4729_;
v_currRecDepth_4733_ = v___x_4684_;
v_ref_4734_ = v___x_4727_;
v_currNamespace_4735_ = v___x_4693_;
v_openDecls_4736_ = v___x_4694_;
v_initHeartbeats_4737_ = v___x_4689_;
v_maxHeartbeats_4738_ = v___x_4728_;
v_currMacroScope_4739_ = v___x_4690_;
v_suppressElabErrors_4740_ = v_anyFailed_4722_;
v___y_4741_ = v___x_4701_;
goto v___jp_4731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4781_, lean_object* v_env_4782_, lean_object* v_mod_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4781_, v_env_4782_, v_mod_4783_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4786_, size_t v_sz_4787_, size_t v_i_4788_, lean_object* v_b_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4786_, v_sz_4787_, v_i_4788_, v_b_4789_, v___y_4790_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4794_, lean_object* v_sz_4795_, lean_object* v_i_4796_, lean_object* v_b_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
size_t v_sz_boxed_4801_; size_t v_i_boxed_4802_; lean_object* v_res_4803_; 
v_sz_boxed_4801_ = lean_unbox_usize(v_sz_4795_);
lean_dec(v_sz_4795_);
v_i_boxed_4802_ = lean_unbox_usize(v_i_4796_);
lean_dec(v_i_4796_);
v_res_4803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4794_, v_sz_boxed_4801_, v_i_boxed_4802_, v_b_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec_ref(v_as_4794_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4805_; 
v___x_4805_ = lean_enable_initializer_execution();
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = lean_compacted_region_free(v_region_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4811_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4817_, lean_object* v_k_4818_, uint8_t v_v_4819_){
_start:
{
lean_object* v_map_4820_; uint8_t v_hasTrace_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4835_; 
v_map_4820_ = lean_ctor_get(v_o_4817_, 0);
v_hasTrace_4821_ = lean_ctor_get_uint8(v_o_4817_, sizeof(void*)*1);
v_isSharedCheck_4835_ = !lean_is_exclusive(v_o_4817_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4823_ = v_o_4817_;
v_isShared_4824_ = v_isSharedCheck_4835_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_map_4820_);
lean_dec(v_o_4817_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4835_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4825_, 0, v_v_4819_);
lean_inc(v_k_4818_);
v___x_4826_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4818_, v___x_4825_, v_map_4820_);
if (v_hasTrace_4821_ == 0)
{
lean_object* v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4830_; 
v___x_4827_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4828_ = l_Lean_Name_isPrefixOf(v___x_4827_, v_k_4818_);
lean_dec(v_k_4818_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v___x_4826_);
v___x_4830_ = v___x_4823_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4826_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_ctor_set_uint8(v___x_4830_, sizeof(void*)*1, v___x_4828_);
return v___x_4830_;
}
}
else
{
lean_object* v___x_4833_; 
lean_dec(v_k_4818_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v___x_4826_);
v___x_4833_ = v___x_4823_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4826_);
lean_ctor_set_uint8(v_reuseFailAlloc_4834_, sizeof(void*)*1, v_hasTrace_4821_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4836_, lean_object* v_k_4837_, lean_object* v_v_4838_){
_start:
{
uint8_t v_v_boxed_4839_; lean_object* v_res_4840_; 
v_v_boxed_4839_ = lean_unbox(v_v_4838_);
v_res_4840_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4836_, v_k_4837_, v_v_boxed_4839_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4841_){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; uint32_t v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4843_ = lean_unsigned_to_nat(80u);
v___x_4844_ = l_Lean_Json_pretty(v_s_4841_, v___x_4843_);
v___x_4845_ = 10;
v___x_4846_ = lean_string_push(v___x_4844_, v___x_4845_);
v___x_4847_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4851_, size_t v_sz_4852_, size_t v_i_4853_, lean_object* v_b_4854_){
_start:
{
uint8_t v___x_4856_; 
v___x_4856_ = lean_usize_dec_lt(v_i_4853_, v_sz_4852_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; 
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v_b_4854_);
return v___x_4857_;
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v_a_4858_ = lean_array_uget_borrowed(v_as_4851_, v_i_4853_);
lean_inc(v_a_4858_);
v___x_4859_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4858_);
v___x_4860_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4859_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v___x_4861_; size_t v___x_4862_; size_t v___x_4863_; 
lean_dec_ref_known(v___x_4860_, 1);
v___x_4861_ = lean_box(0);
v___x_4862_ = ((size_t)1ULL);
v___x_4863_ = lean_usize_add(v_i_4853_, v___x_4862_);
v_i_4853_ = v___x_4863_;
v_b_4854_ = v___x_4861_;
goto _start;
}
else
{
return v___x_4860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4865_, lean_object* v_sz_4866_, lean_object* v_i_4867_, lean_object* v_b_4868_, lean_object* v___y_4869_){
_start:
{
size_t v_sz_boxed_4870_; size_t v_i_boxed_4871_; lean_object* v_res_4872_; 
v_sz_boxed_4870_ = lean_unbox_usize(v_sz_4866_);
lean_dec(v_sz_4866_);
v_i_boxed_4871_ = lean_unbox_usize(v_i_4867_);
lean_dec(v_i_4867_);
v_res_4872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4865_, v_sz_boxed_4870_, v_i_boxed_4871_, v_b_4868_);
lean_dec_ref(v_as_4865_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4873_, size_t v_sz_4874_, size_t v_i_4875_, lean_object* v_bs_4876_){
_start:
{
uint8_t v_anyUnlocated_4877_; 
v_anyUnlocated_4877_ = lean_usize_dec_lt(v_i_4875_, v_sz_4874_);
if (v_anyUnlocated_4877_ == 0)
{
return v_bs_4876_;
}
else
{
lean_object* v___x_4878_; uint8_t v_anyFailed_4879_; lean_object* v_v_4880_; lean_object* v_bs_x27_4881_; lean_object* v___x_4882_; size_t v___x_4883_; size_t v___x_4884_; lean_object* v___x_4885_; 
v___x_4878_ = lean_unsigned_to_nat(0u);
v_anyFailed_4879_ = lean_nat_dec_eq(v___x_4873_, v___x_4878_);
v_v_4880_ = lean_array_uget(v_bs_4876_, v_i_4875_);
v_bs_x27_4881_ = lean_array_uset(v_bs_4876_, v_i_4875_, v___x_4878_);
v___x_4882_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4882_, 0, v_v_4880_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*1, v_anyFailed_4879_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*1 + 1, v_anyUnlocated_4877_);
lean_ctor_set_uint8(v___x_4882_, sizeof(void*)*1 + 2, v_anyFailed_4879_);
v___x_4883_ = ((size_t)1ULL);
v___x_4884_ = lean_usize_add(v_i_4875_, v___x_4883_);
v___x_4885_ = lean_array_uset(v_bs_x27_4881_, v_i_4875_, v___x_4882_);
v_i_4875_ = v___x_4884_;
v_bs_4876_ = v___x_4885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4887_, lean_object* v_sz_4888_, lean_object* v_i_4889_, lean_object* v_bs_4890_){
_start:
{
size_t v_sz_boxed_4891_; size_t v_i_boxed_4892_; lean_object* v_res_4893_; 
v_sz_boxed_4891_ = lean_unbox_usize(v_sz_4888_);
lean_dec(v_sz_4888_);
v_i_boxed_4892_ = lean_unbox_usize(v_i_4889_);
lean_dec(v_i_4889_);
v_res_4893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4887_, v_sz_boxed_4891_, v_i_boxed_4892_, v_bs_4890_);
lean_dec(v___x_4887_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4894_, size_t v_i_4895_, size_t v_stop_4896_, lean_object* v_b_4897_){
_start:
{
uint8_t v___x_4898_; 
v___x_4898_ = lean_usize_dec_eq(v_i_4895_, v_stop_4896_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; lean_object* v_fst_4900_; lean_object* v_snd_4901_; uint8_t v___x_4902_; lean_object* v___x_4903_; size_t v___x_4904_; size_t v___x_4905_; 
v___x_4899_ = lean_array_uget_borrowed(v_as_4894_, v_i_4895_);
v_fst_4900_ = lean_ctor_get(v___x_4899_, 0);
v_snd_4901_ = lean_ctor_get(v___x_4899_, 1);
v___x_4902_ = lean_unbox(v_snd_4901_);
lean_inc(v_fst_4900_);
v___x_4903_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4897_, v_fst_4900_, v___x_4902_);
v___x_4904_ = ((size_t)1ULL);
v___x_4905_ = lean_usize_add(v_i_4895_, v___x_4904_);
v_i_4895_ = v___x_4905_;
v_b_4897_ = v___x_4903_;
goto _start;
}
else
{
return v_b_4897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4907_, lean_object* v_i_4908_, lean_object* v_stop_4909_, lean_object* v_b_4910_){
_start:
{
size_t v_i_boxed_4911_; size_t v_stop_boxed_4912_; lean_object* v_res_4913_; 
v_i_boxed_4911_ = lean_unbox_usize(v_i_4908_);
lean_dec(v_i_4908_);
v_stop_boxed_4912_ = lean_unbox_usize(v_stop_4909_);
lean_dec(v_stop_4909_);
v_res_4913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4907_, v_i_boxed_4911_, v_stop_boxed_4912_, v_b_4910_);
lean_dec_ref(v_as_4907_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4923_, lean_object* v_checkImports_4924_, lean_object* v_args_4925_, lean_object* v___x_4926_, lean_object* v_as_4927_, size_t v_sz_4928_, size_t v_i_4929_, lean_object* v_b_4930_){
_start:
{
lean_object* v_a_4933_; lean_object* v___x_4937_; uint8_t v_anyFailed_4938_; uint8_t v_anyUnlocated_4939_; lean_object* v___x_4940_; lean_object* v_envLinterModule_4941_; uint8_t v___x_4942_; 
v___x_4937_ = lean_unsigned_to_nat(0u);
v_anyFailed_4938_ = lean_nat_dec_eq(v___x_4923_, v___x_4937_);
v_anyUnlocated_4939_ = 1;
v___x_4940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4941_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4941_, 0, v___x_4940_);
lean_ctor_set_uint8(v_envLinterModule_4941_, sizeof(void*)*1, v_anyFailed_4938_);
lean_ctor_set_uint8(v_envLinterModule_4941_, sizeof(void*)*1 + 1, v_anyUnlocated_4939_);
lean_ctor_set_uint8(v_envLinterModule_4941_, sizeof(void*)*1 + 2, v_anyFailed_4938_);
v___x_4942_ = lean_usize_dec_lt(v_i_4929_, v_sz_4928_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
lean_dec_ref_known(v_envLinterModule_4941_, 1);
lean_dec(v___x_4926_);
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_b_4930_);
return v___x_4943_;
}
else
{
lean_object* v___x_4944_; lean_object* v_a_4945_; lean_object* v___x_4946_; 
v___x_4944_ = lean_enable_initializer_execution();
v_a_4945_ = lean_array_uget_borrowed(v_as_4927_, v_i_4929_);
lean_inc(v_a_4945_);
v___x_4946_ = l_Lean_findOLean(v_a_4945_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = l_Lean_readModuleData(v_a_4947_);
lean_dec(v_a_4947_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4949_; lean_object* v_fst_4950_; lean_object* v_snd_4951_; uint8_t v___x_4952_; lean_object* v_snd_4953_; lean_object* v_snd_4954_; lean_object* v_snd_4955_; lean_object* v_snd_4956_; lean_object* v_fst_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_5245_; 
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_a_4949_);
lean_dec_ref_known(v___x_4948_, 1);
v_fst_4950_ = lean_ctor_get(v_a_4949_, 0);
lean_inc(v_fst_4950_);
v_snd_4951_ = lean_ctor_get(v_a_4949_, 1);
lean_inc(v_snd_4951_);
lean_dec(v_a_4949_);
v___x_4952_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4950_);
lean_dec(v_fst_4950_);
v_snd_4953_ = lean_ctor_get(v_b_4930_, 1);
lean_inc(v_snd_4953_);
v_snd_4954_ = lean_ctor_get(v_snd_4953_, 1);
lean_inc(v_snd_4954_);
v_snd_4955_ = lean_ctor_get(v_snd_4954_, 1);
lean_inc(v_snd_4955_);
v_snd_4956_ = lean_ctor_get(v_snd_4955_, 1);
lean_inc(v_snd_4956_);
v_fst_4957_ = lean_ctor_get(v_b_4930_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v_b_4930_);
if (v_isSharedCheck_5245_ == 0)
{
lean_object* v_unused_5246_; 
v_unused_5246_ = lean_ctor_get(v_b_4930_, 1);
lean_dec(v_unused_5246_);
v___x_4959_ = v_b_4930_;
v_isShared_4960_ = v_isSharedCheck_5245_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_fst_4957_);
lean_dec(v_b_4930_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_5245_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v_fst_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_5243_; 
v_fst_4961_ = lean_ctor_get(v_snd_4953_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v_snd_4953_);
if (v_isSharedCheck_5243_ == 0)
{
lean_object* v_unused_5244_; 
v_unused_5244_ = lean_ctor_get(v_snd_4953_, 1);
lean_dec(v_unused_5244_);
v___x_4963_ = v_snd_4953_;
v_isShared_4964_ = v_isSharedCheck_5243_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_fst_4961_);
lean_dec(v_snd_4953_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_5243_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v_fst_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_5241_; 
v_fst_4965_ = lean_ctor_get(v_snd_4954_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_snd_4954_);
if (v_isSharedCheck_5241_ == 0)
{
lean_object* v_unused_5242_; 
v_unused_5242_ = lean_ctor_get(v_snd_4954_, 1);
lean_dec(v_unused_5242_);
v___x_4967_ = v_snd_4954_;
v_isShared_4968_ = v_isSharedCheck_5241_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_fst_4965_);
lean_dec(v_snd_4954_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_5241_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v_fst_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_5239_; 
v_fst_4969_ = lean_ctor_get(v_snd_4955_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_snd_4955_);
if (v_isSharedCheck_5239_ == 0)
{
lean_object* v_unused_5240_; 
v_unused_5240_ = lean_ctor_get(v_snd_4955_, 1);
lean_dec(v_unused_5240_);
v___x_4971_ = v_snd_4955_;
v_isShared_4972_ = v_isSharedCheck_5239_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_fst_4969_);
lean_dec(v_snd_4955_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_5239_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v_fst_4973_; lean_object* v_snd_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5238_; 
v_fst_4973_ = lean_ctor_get(v_snd_4956_, 0);
v_snd_4974_ = lean_ctor_get(v_snd_4956_, 1);
v_isSharedCheck_5238_ = !lean_is_exclusive(v_snd_4956_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_4976_ = v_snd_4956_;
v_isShared_4977_ = v_isSharedCheck_5238_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_snd_4974_);
lean_inc(v_fst_4973_);
lean_dec(v_snd_4956_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5238_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___y_4979_; lean_object* v___y_4980_; uint8_t v_anyFailed_4981_; uint8_t v_anyUnlocated_4982_; lean_object* v_records_4983_; lean_object* v_codeQualityEntries_4984_; lean_object* v___y_5131_; lean_object* v___y_5132_; uint8_t v_anyFailed_5133_; uint8_t v_anyUnlocated_5134_; lean_object* v_records_5135_; lean_object* v_codeQualityEntries_5136_; lean_object* v___x_5153_; lean_object* v___y_5155_; lean_object* v___y_5156_; uint8_t v___y_5196_; 
v___x_5153_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
if (v___x_4952_ == 0)
{
uint8_t v___x_5236_; 
v___x_5236_ = 2;
v___y_5196_ = v___x_5236_;
goto v___jp_5195_;
}
else
{
uint8_t v___x_5237_; 
v___x_5237_ = 1;
v___y_5196_ = v___x_5237_;
goto v___jp_5195_;
}
v___jp_4978_:
{
uint8_t v_mode_4985_; uint8_t v___x_4986_; uint8_t v___x_4987_; 
v_mode_4985_ = lean_ctor_get_uint8(v_args_4925_, sizeof(void*)*4 + 1);
v___x_4986_ = 2;
v___x_4987_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4985_, v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = l_Lean_Name_getRoot(v_a_4945_);
lean_inc(v___x_4926_);
v___x_4989_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4925_, v___y_4980_, v___x_4926_, v___y_4979_, v___x_4988_, v_fst_4973_);
lean_dec_ref(v___y_4980_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v_outcome_4991_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4989_, 1);
v_outcome_4991_ = lean_ctor_get(v_a_4990_, 0);
if (lean_obj_tag(v_outcome_4991_) == 0)
{
uint8_t v_failed_4992_; 
v_failed_4992_ = lean_ctor_get_uint8(v_outcome_4991_, 0);
if (v_failed_4992_ == 0)
{
lean_object* v_checkedModules_4993_; lean_object* v___x_4995_; 
v_checkedModules_4993_ = lean_ctor_get(v_a_4990_, 1);
lean_inc(v_checkedModules_4993_);
lean_dec(v_a_4990_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_checkedModules_4993_);
v___x_4995_ = v___x_4976_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_checkedModules_4993_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_snd_4974_);
v___x_4995_ = v_reuseFailAlloc_5010_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4997_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_4995_);
lean_ctor_set(v___x_4971_, 0, v_codeQualityEntries_4984_);
v___x_4997_ = v___x_4971_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_codeQualityEntries_4984_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_5009_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4999_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_4997_);
lean_ctor_set(v___x_4967_, 0, v_records_4983_);
v___x_4999_ = v___x_4967_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_records_4983_);
lean_ctor_set(v_reuseFailAlloc_5008_, 1, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5008_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_5000_ = lean_box(v_anyUnlocated_4982_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_4999_);
lean_ctor_set(v___x_4963_, 0, v___x_5000_);
v___x_5002_ = v___x_4963_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5000_);
lean_ctor_set(v_reuseFailAlloc_5007_, 1, v___x_4999_);
v___x_5002_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
lean_object* v___x_5003_; lean_object* v___x_5005_; 
v___x_5003_ = lean_box(v_anyFailed_4981_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_5002_);
lean_ctor_set(v___x_4959_, 0, v___x_5003_);
v___x_5005_ = v___x_4959_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5006_, 1, v___x_5002_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
v_a_4933_ = v___x_5005_;
goto v___jp_4932_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5011_; lean_object* v___x_5013_; 
v_checkedModules_5011_ = lean_ctor_get(v_a_4990_, 1);
lean_inc(v_checkedModules_5011_);
lean_dec(v_a_4990_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_checkedModules_5011_);
v___x_5013_ = v___x_4976_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_checkedModules_5011_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_snd_4974_);
v___x_5013_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
lean_object* v___x_5015_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5013_);
lean_ctor_set(v___x_4971_, 0, v_codeQualityEntries_4984_);
v___x_5015_ = v___x_4971_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_codeQualityEntries_4984_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
lean_object* v___x_5017_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_5015_);
lean_ctor_set(v___x_4967_, 0, v_records_4983_);
v___x_5017_ = v___x_4967_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_records_4983_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v___x_5015_);
v___x_5017_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5018_ = lean_box(v_anyUnlocated_4982_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5017_);
lean_ctor_set(v___x_4963_, 0, v___x_5018_);
v___x_5020_ = v___x_4963_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5018_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v___x_5017_);
v___x_5020_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5021_ = lean_box(v_anyUnlocated_4939_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_5020_);
lean_ctor_set(v___x_4959_, 0, v___x_5021_);
v___x_5023_ = v___x_4959_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5020_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
v_a_4933_ = v___x_5023_;
goto v___jp_4932_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5029_; lean_object* v_records_5030_; uint8_t v_unlocated_5031_; lean_object* v___x_5032_; 
lean_inc_ref(v_outcome_4991_);
v_checkedModules_5029_ = lean_ctor_get(v_a_4990_, 1);
lean_inc(v_checkedModules_5029_);
lean_dec(v_a_4990_);
v_records_5030_ = lean_ctor_get(v_outcome_4991_, 0);
lean_inc_ref(v_records_5030_);
v_unlocated_5031_ = lean_ctor_get_uint8(v_outcome_4991_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4991_, 1);
v___x_5032_ = l_Array_append___redArg(v_records_4983_, v_records_5030_);
lean_dec_ref(v_records_5030_);
if (v_unlocated_5031_ == 0)
{
lean_object* v___x_5034_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_checkedModules_5029_);
v___x_5034_ = v___x_4976_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_checkedModules_5029_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v_snd_4974_);
v___x_5034_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5036_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5034_);
lean_ctor_set(v___x_4971_, 0, v_codeQualityEntries_4984_);
v___x_5036_ = v___x_4971_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_codeQualityEntries_4984_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5038_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_5036_);
lean_ctor_set(v___x_4967_, 0, v___x_5032_);
v___x_5038_ = v___x_4967_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5032_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
lean_object* v___x_5039_; lean_object* v___x_5041_; 
v___x_5039_ = lean_box(v_anyUnlocated_4982_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5038_);
lean_ctor_set(v___x_4963_, 0, v___x_5039_);
v___x_5041_ = v___x_4963_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5038_);
v___x_5041_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5042_; lean_object* v___x_5044_; 
v___x_5042_ = lean_box(v_anyFailed_4981_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_5041_);
lean_ctor_set(v___x_4959_, 0, v___x_5042_);
v___x_5044_ = v___x_4959_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5042_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v___x_5041_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
v_a_4933_ = v___x_5044_;
goto v___jp_4932_;
}
}
}
}
}
}
else
{
lean_object* v___x_5051_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_checkedModules_5029_);
v___x_5051_ = v___x_4976_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_checkedModules_5029_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_snd_4974_);
v___x_5051_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
lean_object* v___x_5053_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5051_);
lean_ctor_set(v___x_4971_, 0, v_codeQualityEntries_4984_);
v___x_5053_ = v___x_4971_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_codeQualityEntries_4984_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
lean_object* v___x_5055_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_5053_);
lean_ctor_set(v___x_4967_, 0, v___x_5032_);
v___x_5055_ = v___x_4967_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5032_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_box(v_anyUnlocated_4939_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5055_);
lean_ctor_set(v___x_4963_, 0, v___x_5056_);
v___x_5058_ = v___x_4963_;
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
v___x_5059_ = lean_box(v_anyFailed_4981_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_5058_);
lean_ctor_set(v___x_4959_, 0, v___x_5059_);
v___x_5061_ = v___x_4959_;
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
v_a_4933_ = v___x_5061_;
goto v___jp_4932_;
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
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec_ref(v_codeQualityEntries_4984_);
lean_dec_ref(v_records_4983_);
lean_del_object(v___x_4976_);
lean_dec(v_snd_4974_);
lean_del_object(v___x_4971_);
lean_del_object(v___x_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_dec(v___x_4926_);
v_a_5067_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_4989_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_4989_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
else
{
lean_object* v___x_5075_; lean_object* v_fst_5076_; lean_object* v_snd_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5129_; 
lean_del_object(v___x_4959_);
v___x_5075_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4925_, v___y_4980_, v___y_4979_, v_a_4945_, v_snd_4974_);
lean_dec_ref(v___y_4980_);
v_fst_5076_ = lean_ctor_get(v___x_5075_, 0);
v_snd_5077_ = lean_ctor_get(v___x_5075_, 1);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5079_ = v___x_5075_;
v_isShared_5080_ = v_isSharedCheck_5129_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_snd_5077_);
lean_inc(v_fst_5076_);
lean_dec(v___x_5075_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5129_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; 
lean_inc(v_a_4945_);
lean_inc(v___x_4926_);
v___x_5081_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4926_, v___y_4979_, v_a_4945_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v_entries_5083_; uint8_t v_failed_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_a_5082_);
lean_dec_ref_known(v___x_5081_, 1);
v_entries_5083_ = lean_ctor_get(v_a_5082_, 0);
lean_inc_ref(v_entries_5083_);
v_failed_5084_ = lean_ctor_get_uint8(v_a_5082_, sizeof(void*)*1);
lean_dec(v_a_5082_);
v___x_5085_ = l_Array_append___redArg(v_codeQualityEntries_4984_, v_fst_5076_);
lean_dec(v_fst_5076_);
v___x_5086_ = l_Array_append___redArg(v___x_5085_, v_entries_5083_);
lean_dec_ref(v_entries_5083_);
if (v_failed_5084_ == 0)
{
lean_object* v___x_5088_; 
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v_fst_4973_);
v___x_5088_ = v___x_5079_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_fst_4973_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_snd_5077_);
v___x_5088_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
lean_object* v___x_5090_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5088_);
lean_ctor_set(v___x_4976_, 0, v___x_5086_);
v___x_5090_ = v___x_4976_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5102_, 1, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
lean_object* v___x_5092_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5090_);
lean_ctor_set(v___x_4971_, 0, v_records_4983_);
v___x_5092_ = v___x_4971_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_records_4983_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5090_);
v___x_5092_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
lean_object* v___x_5093_; lean_object* v___x_5095_; 
v___x_5093_ = lean_box(v_anyUnlocated_4982_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_5092_);
lean_ctor_set(v___x_4967_, 0, v___x_5093_);
v___x_5095_ = v___x_4967_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5093_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5092_);
v___x_5095_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
lean_object* v___x_5096_; lean_object* v___x_5098_; 
v___x_5096_ = lean_box(v_anyFailed_4981_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5095_);
lean_ctor_set(v___x_4963_, 0, v___x_5096_);
v___x_5098_ = v___x_4963_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5095_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
v_a_4933_ = v___x_5098_;
goto v___jp_4932_;
}
}
}
}
}
}
else
{
lean_object* v___x_5105_; 
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v_fst_4973_);
v___x_5105_ = v___x_5079_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_fst_4973_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v_snd_5077_);
v___x_5105_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5107_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5105_);
lean_ctor_set(v___x_4976_, 0, v___x_5086_);
v___x_5107_ = v___x_4976_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
lean_object* v___x_5109_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 1, v___x_5107_);
lean_ctor_set(v___x_4971_, 0, v_records_4983_);
v___x_5109_ = v___x_4971_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_records_4983_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5110_ = lean_box(v_anyUnlocated_4982_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_5109_);
lean_ctor_set(v___x_4967_, 0, v___x_5110_);
v___x_5112_ = v___x_4967_;
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
v___x_5113_ = lean_box(v_anyUnlocated_4939_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5112_);
lean_ctor_set(v___x_4963_, 0, v___x_5113_);
v___x_5115_ = v___x_4963_;
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
v_a_4933_ = v___x_5115_;
goto v___jp_4932_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_del_object(v___x_5079_);
lean_dec(v_snd_5077_);
lean_dec(v_fst_5076_);
lean_dec_ref(v_codeQualityEntries_4984_);
lean_dec_ref(v_records_4983_);
lean_del_object(v___x_4976_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_del_object(v___x_4967_);
lean_del_object(v___x_4963_);
lean_dec(v___x_4926_);
v_a_5121_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5081_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5081_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
}
v___jp_5130_:
{
lean_object* v___x_5137_; 
lean_inc(v_a_4945_);
lean_inc_ref(v___y_5131_);
lean_inc(v___x_4926_);
lean_inc_ref(v___y_5132_);
v___x_5137_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4925_, v___y_5132_, v___x_4926_, v___y_5131_, v_a_4945_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
lean_dec_ref_known(v___x_5137_, 1);
switch(lean_obj_tag(v_a_5138_))
{
case 0:
{
uint8_t v_failed_5139_; 
v_failed_5139_ = lean_ctor_get_uint8(v_a_5138_, 0);
lean_dec_ref_known(v_a_5138_, 0);
if (v_failed_5139_ == 0)
{
v___y_4979_ = v___y_5131_;
v___y_4980_ = v___y_5132_;
v_anyFailed_4981_ = v_anyFailed_5133_;
v_anyUnlocated_4982_ = v_anyUnlocated_5134_;
v_records_4983_ = v_records_5135_;
v_codeQualityEntries_4984_ = v_codeQualityEntries_5136_;
goto v___jp_4978_;
}
else
{
v___y_4979_ = v___y_5131_;
v___y_4980_ = v___y_5132_;
v_anyFailed_4981_ = v_anyUnlocated_4939_;
v_anyUnlocated_4982_ = v_anyUnlocated_5134_;
v_records_4983_ = v_records_5135_;
v_codeQualityEntries_4984_ = v_codeQualityEntries_5136_;
goto v___jp_4978_;
}
}
case 1:
{
lean_object* v_records_5140_; uint8_t v_unlocated_5141_; lean_object* v___x_5142_; 
v_records_5140_ = lean_ctor_get(v_a_5138_, 0);
lean_inc_ref(v_records_5140_);
v_unlocated_5141_ = lean_ctor_get_uint8(v_a_5138_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5138_, 1);
v___x_5142_ = l_Array_append___redArg(v_records_5135_, v_records_5140_);
lean_dec_ref(v_records_5140_);
if (v_unlocated_5141_ == 0)
{
v___y_4979_ = v___y_5131_;
v___y_4980_ = v___y_5132_;
v_anyFailed_4981_ = v_anyFailed_5133_;
v_anyUnlocated_4982_ = v_anyUnlocated_5134_;
v_records_4983_ = v___x_5142_;
v_codeQualityEntries_4984_ = v_codeQualityEntries_5136_;
goto v___jp_4978_;
}
else
{
v___y_4979_ = v___y_5131_;
v___y_4980_ = v___y_5132_;
v_anyFailed_4981_ = v_anyFailed_5133_;
v_anyUnlocated_4982_ = v_anyUnlocated_4939_;
v_records_4983_ = v___x_5142_;
v_codeQualityEntries_4984_ = v_codeQualityEntries_5136_;
goto v___jp_4978_;
}
}
default: 
{
lean_object* v_entries_5143_; lean_object* v___x_5144_; 
v_entries_5143_ = lean_ctor_get(v_a_5138_, 0);
lean_inc_ref(v_entries_5143_);
lean_dec_ref_known(v_a_5138_, 1);
v___x_5144_ = l_Array_append___redArg(v_codeQualityEntries_5136_, v_entries_5143_);
lean_dec_ref(v_entries_5143_);
v___y_4979_ = v___y_5131_;
v___y_4980_ = v___y_5132_;
v_anyFailed_4981_ = v_anyFailed_5133_;
v_anyUnlocated_4982_ = v_anyUnlocated_5134_;
v_records_4983_ = v_records_5135_;
v_codeQualityEntries_4984_ = v___x_5144_;
goto v___jp_4978_;
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref(v_codeQualityEntries_5136_);
lean_dec_ref(v_records_5135_);
lean_dec_ref(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_del_object(v___x_4976_);
lean_dec(v_snd_4974_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_del_object(v___x_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_dec(v___x_4926_);
v_a_5145_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5137_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5137_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
v___jp_5154_:
{
lean_object* v___x_5157_; lean_object* v_toEnvExtension_5158_; lean_object* v_asyncMode_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v_merged_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5193_; 
v___x_5157_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5158_ = lean_ctor_get(v___x_5157_, 0);
v_asyncMode_5159_ = lean_ctor_get(v_toEnvExtension_5158_, 2);
v___x_5160_ = lean_box(0);
lean_inc_ref(v___y_5155_);
v___x_5161_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5153_, v___x_5157_, v___y_5155_, v_asyncMode_5159_, v___x_5160_);
v_merged_5162_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5193_ == 0)
{
lean_object* v_unused_5194_; 
v_unused_5194_ = lean_ctor_get(v___x_5161_, 1);
lean_dec(v_unused_5194_);
v___x_5164_ = v___x_5161_;
v_isShared_5165_ = v_isSharedCheck_5193_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_merged_5162_);
lean_dec(v___x_5161_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5193_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 1, v_merged_5162_);
lean_ctor_set(v___x_5164_, 0, v___y_5156_);
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___y_5156_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v_merged_5162_);
v___x_5167_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
lean_object* v___x_5168_; 
v___x_5168_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4925_, v___x_5167_, v___y_5155_, v_a_4945_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
switch(lean_obj_tag(v_a_5169_))
{
case 0:
{
uint8_t v___x_5170_; 
v___x_5170_ = lean_unbox(v_fst_4957_);
lean_dec(v_fst_4957_);
if (v___x_5170_ == 0)
{
uint8_t v_failed_5171_; uint8_t v___x_5172_; 
v_failed_5171_ = lean_ctor_get_uint8(v_a_5169_, 0);
lean_dec_ref_known(v_a_5169_, 0);
v___x_5172_ = lean_unbox(v_fst_4961_);
lean_dec(v_fst_4961_);
v___y_5131_ = v___y_5155_;
v___y_5132_ = v___x_5167_;
v_anyFailed_5133_ = v_failed_5171_;
v_anyUnlocated_5134_ = v___x_5172_;
v_records_5135_ = v_fst_4965_;
v_codeQualityEntries_5136_ = v_fst_4969_;
goto v___jp_5130_;
}
else
{
uint8_t v___x_5173_; 
lean_dec_ref_known(v_a_5169_, 0);
v___x_5173_ = lean_unbox(v_fst_4961_);
lean_dec(v_fst_4961_);
v___y_5131_ = v___y_5155_;
v___y_5132_ = v___x_5167_;
v_anyFailed_5133_ = v_anyUnlocated_4939_;
v_anyUnlocated_5134_ = v___x_5173_;
v_records_5135_ = v_fst_4965_;
v_codeQualityEntries_5136_ = v_fst_4969_;
goto v___jp_5130_;
}
}
case 1:
{
lean_object* v_records_5174_; uint8_t v_unlocated_5175_; lean_object* v___x_5176_; 
v_records_5174_ = lean_ctor_get(v_a_5169_, 0);
lean_inc_ref(v_records_5174_);
v_unlocated_5175_ = lean_ctor_get_uint8(v_a_5169_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5169_, 1);
v___x_5176_ = l_Array_append___redArg(v_fst_4965_, v_records_5174_);
lean_dec_ref(v_records_5174_);
if (v_unlocated_5175_ == 0)
{
uint8_t v___x_5177_; uint8_t v___x_5178_; 
v___x_5177_ = lean_unbox(v_fst_4957_);
lean_dec(v_fst_4957_);
v___x_5178_ = lean_unbox(v_fst_4961_);
lean_dec(v_fst_4961_);
v___y_5131_ = v___y_5155_;
v___y_5132_ = v___x_5167_;
v_anyFailed_5133_ = v___x_5177_;
v_anyUnlocated_5134_ = v___x_5178_;
v_records_5135_ = v___x_5176_;
v_codeQualityEntries_5136_ = v_fst_4969_;
goto v___jp_5130_;
}
else
{
uint8_t v___x_5179_; 
lean_dec(v_fst_4961_);
v___x_5179_ = lean_unbox(v_fst_4957_);
lean_dec(v_fst_4957_);
v___y_5131_ = v___y_5155_;
v___y_5132_ = v___x_5167_;
v_anyFailed_5133_ = v___x_5179_;
v_anyUnlocated_5134_ = v_anyUnlocated_4939_;
v_records_5135_ = v___x_5176_;
v_codeQualityEntries_5136_ = v_fst_4969_;
goto v___jp_5130_;
}
}
default: 
{
lean_object* v_entries_5180_; lean_object* v___x_5181_; uint8_t v___x_5182_; uint8_t v___x_5183_; 
v_entries_5180_ = lean_ctor_get(v_a_5169_, 0);
lean_inc_ref(v_entries_5180_);
lean_dec_ref_known(v_a_5169_, 1);
v___x_5181_ = l_Array_append___redArg(v_fst_4969_, v_entries_5180_);
lean_dec_ref(v_entries_5180_);
v___x_5182_ = lean_unbox(v_fst_4957_);
lean_dec(v_fst_4957_);
v___x_5183_ = lean_unbox(v_fst_4961_);
lean_dec(v_fst_4961_);
v___y_5131_ = v___y_5155_;
v___y_5132_ = v___x_5167_;
v_anyFailed_5133_ = v___x_5182_;
v_anyUnlocated_5134_ = v___x_5183_;
v_records_5135_ = v_fst_4965_;
v_codeQualityEntries_5136_ = v___x_5181_;
goto v___jp_5130_;
}
}
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
lean_dec_ref(v___x_5167_);
lean_dec_ref(v___y_5155_);
lean_del_object(v___x_4976_);
lean_dec(v_snd_4974_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4963_);
lean_dec(v_fst_4961_);
lean_del_object(v___x_4959_);
lean_dec(v_fst_4957_);
lean_dec(v___x_4926_);
v_a_5184_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5168_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5168_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
}
}
v___jp_5195_:
{
lean_object* v___x_5197_; 
v___x_5197_ = lean_compacted_region_free(v_snd_4951_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; uint32_t v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_dec_ref_known(v___x_5197_, 1);
lean_inc(v_a_4945_);
v___x_5198_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5198_, 0, v_a_4945_);
lean_ctor_set_uint8(v___x_5198_, sizeof(void*)*1, v_anyFailed_4938_);
lean_ctor_set_uint8(v___x_5198_, sizeof(void*)*1 + 1, v_anyUnlocated_4939_);
lean_ctor_set_uint8(v___x_5198_, sizeof(void*)*1 + 2, v_anyFailed_4938_);
v___x_5199_ = lean_unsigned_to_nat(2u);
v___x_5200_ = lean_mk_empty_array_with_capacity(v___x_5199_);
v___x_5201_ = lean_array_push(v___x_5200_, v___x_5198_);
v___x_5202_ = lean_array_push(v___x_5201_, v_envLinterModule_4941_);
v___x_5203_ = l_Array_append___redArg(v___x_5202_, v_checkImports_4924_);
v___x_5204_ = l_Lean_Options_empty;
v___x_5205_ = 1024;
v___x_5206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5207_ = lean_box(1);
v___x_5208_ = l_Lean_importModules(v___x_5203_, v___x_5204_, v___x_5205_, v___x_5206_, v_anyFailed_4938_, v_anyUnlocated_4939_, v___y_5196_, v___x_5207_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v_linterOverrides_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref_known(v___x_5208_, 1);
v_linterOverrides_5210_ = lean_ctor_get(v_args_4925_, 0);
v___x_5211_ = lean_array_get_size(v_linterOverrides_5210_);
v___x_5212_ = lean_nat_dec_lt(v___x_4937_, v___x_5211_);
if (v___x_5212_ == 0)
{
v___y_5155_ = v_a_5209_;
v___y_5156_ = v___x_5204_;
goto v___jp_5154_;
}
else
{
uint8_t v___x_5213_; 
v___x_5213_ = lean_nat_dec_le(v___x_5211_, v___x_5211_);
if (v___x_5213_ == 0)
{
if (v___x_5212_ == 0)
{
v___y_5155_ = v_a_5209_;
v___y_5156_ = v___x_5204_;
goto v___jp_5154_;
}
else
{
size_t v___x_5214_; size_t v___x_5215_; lean_object* v___x_5216_; 
v___x_5214_ = ((size_t)0ULL);
v___x_5215_ = lean_usize_of_nat(v___x_5211_);
v___x_5216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5210_, v___x_5214_, v___x_5215_, v___x_5204_);
v___y_5155_ = v_a_5209_;
v___y_5156_ = v___x_5216_;
goto v___jp_5154_;
}
}
else
{
size_t v___x_5217_; size_t v___x_5218_; lean_object* v___x_5219_; 
v___x_5217_ = ((size_t)0ULL);
v___x_5218_ = lean_usize_of_nat(v___x_5211_);
v___x_5219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5210_, v___x_5217_, v___x_5218_, v___x_5204_);
v___y_5155_ = v_a_5209_;
v___y_5156_ = v___x_5219_;
goto v___jp_5154_;
}
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_del_object(v___x_4976_);
lean_dec(v_snd_4974_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4963_);
lean_dec(v_fst_4961_);
lean_del_object(v___x_4959_);
lean_dec(v_fst_4957_);
lean_dec(v___x_4926_);
v_a_5220_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5208_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5208_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_del_object(v___x_4976_);
lean_dec(v_snd_4974_);
lean_dec(v_fst_4973_);
lean_del_object(v___x_4971_);
lean_dec(v_fst_4969_);
lean_del_object(v___x_4967_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4963_);
lean_dec(v_fst_4961_);
lean_del_object(v___x_4959_);
lean_dec(v_fst_4957_);
lean_dec_ref_known(v_envLinterModule_4941_, 1);
lean_dec(v___x_4926_);
v_a_5228_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5197_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5197_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
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
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_dec_ref_known(v_envLinterModule_4941_, 1);
lean_dec_ref(v_b_4930_);
lean_dec(v___x_4926_);
v_a_5247_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_4948_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_4948_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
lean_dec_ref_known(v_envLinterModule_4941_, 1);
lean_dec_ref(v_b_4930_);
lean_dec(v___x_4926_);
v_a_5255_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_4946_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_4946_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
v___jp_4932_:
{
size_t v___x_4934_; size_t v___x_4935_; 
v___x_4934_ = ((size_t)1ULL);
v___x_4935_ = lean_usize_add(v_i_4929_, v___x_4934_);
v_i_4929_ = v___x_4935_;
v_b_4930_ = v_a_4933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5263_, lean_object* v_checkImports_5264_, lean_object* v_args_5265_, lean_object* v___x_5266_, lean_object* v_as_5267_, lean_object* v_sz_5268_, lean_object* v_i_5269_, lean_object* v_b_5270_, lean_object* v___y_5271_){
_start:
{
size_t v_sz_boxed_5272_; size_t v_i_boxed_5273_; lean_object* v_res_5274_; 
v_sz_boxed_5272_ = lean_unbox_usize(v_sz_5268_);
lean_dec(v_sz_5268_);
v_i_boxed_5273_ = lean_unbox_usize(v_i_5269_);
lean_dec(v_i_5269_);
v_res_5274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5263_, v_checkImports_5264_, v_args_5265_, v___x_5266_, v_as_5267_, v_sz_boxed_5272_, v_i_boxed_5273_, v_b_5270_);
lean_dec_ref(v_as_5267_);
lean_dec_ref(v_args_5265_);
lean_dec_ref(v_checkImports_5264_);
lean_dec(v___x_5263_);
return v_res_5274_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; 
v___x_5275_ = l_Lean_NameSet_empty;
v___x_5276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5275_);
lean_ctor_set(v___x_5276_, 1, v___x_5275_);
return v___x_5276_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5277_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5278_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
lean_ctor_set(v___x_5279_, 1, v___x_5277_);
return v___x_5279_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5280_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5281_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5281_);
lean_ctor_set(v___x_5282_, 1, v___x_5280_);
return v___x_5282_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5284_; lean_object* v___x_5285_; 
v___x_5284_ = 0;
v___x_5285_ = lean_box_uint32(v___x_5284_);
return v___x_5285_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5286_; lean_object* v___x_5287_; 
v___x_5286_ = 1;
v___x_5287_ = lean_box_uint32(v___x_5286_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5288_){
_start:
{
lean_object* v_mods_5290_; uint8_t v_mode_5291_; lean_object* v_checks_5292_; lean_object* v_srcSearchPath_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; uint8_t v_anyFailed_5296_; 
v_mods_5290_ = lean_ctor_get(v_args_5288_, 1);
lean_inc_ref(v_mods_5290_);
v_mode_5291_ = lean_ctor_get_uint8(v_args_5288_, sizeof(void*)*4 + 1);
v_checks_5292_ = lean_ctor_get(v_args_5288_, 2);
v_srcSearchPath_5293_ = lean_ctor_get(v_args_5288_, 3);
v___x_5294_ = lean_array_get_size(v_mods_5290_);
v___x_5295_ = lean_unsigned_to_nat(0u);
v_anyFailed_5296_ = lean_nat_dec_eq(v___x_5294_, v___x_5295_);
if (v_anyFailed_5296_ == 0)
{
lean_object* v___x_5297_; 
v___x_5297_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; size_t v_sz_5299_; size_t v___x_5300_; lean_object* v_checkImports_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; size_t v_sz_5308_; lean_object* v___x_5309_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5298_);
lean_dec_ref_known(v___x_5297_, 1);
v_sz_5299_ = lean_array_size(v_checks_5292_);
v___x_5300_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5292_);
v_checkImports_5301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5294_, v_sz_5299_, v___x_5300_, v_checks_5292_);
lean_inc(v_srcSearchPath_5293_);
v___x_5302_ = l_List_appendTR___redArg(v_srcSearchPath_5293_, v_a_5298_);
v___x_5303_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5304_ = lean_box(v_anyFailed_5296_);
v___x_5305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5304_);
lean_ctor_set(v___x_5305_, 1, v___x_5303_);
v___x_5306_ = lean_box(v_anyFailed_5296_);
v___x_5307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5306_);
lean_ctor_set(v___x_5307_, 1, v___x_5305_);
v_sz_5308_ = lean_array_size(v_mods_5290_);
v___x_5309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5294_, v_checkImports_5301_, v_args_5288_, v___x_5302_, v_mods_5290_, v_sz_5308_, v___x_5300_, v___x_5307_);
lean_dec_ref(v_mods_5290_);
lean_dec_ref(v_args_5288_);
lean_dec_ref(v_checkImports_5301_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5381_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5312_ = v___x_5309_;
v_isShared_5313_ = v_isSharedCheck_5381_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5309_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5381_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
switch(v_mode_5291_)
{
case 0:
{
lean_object* v_fst_5314_; uint8_t v___x_5315_; 
v_fst_5314_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_fst_5314_);
lean_dec(v_a_5310_);
v___x_5315_ = lean_unbox(v_fst_5314_);
lean_dec(v_fst_5314_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5316_; lean_object* v___x_5318_; 
v___x_5316_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5316_);
v___x_5318_ = v___x_5312_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5316_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
v___x_5320_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5320_);
v___x_5322_ = v___x_5312_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
case 1:
{
lean_object* v_snd_5324_; lean_object* v_snd_5325_; lean_object* v_fst_5326_; lean_object* v_fst_5327_; lean_object* v___x_5328_; 
v_snd_5324_ = lean_ctor_get(v_a_5310_, 1);
lean_inc(v_snd_5324_);
lean_del_object(v___x_5312_);
lean_dec(v_a_5310_);
v_snd_5325_ = lean_ctor_get(v_snd_5324_, 1);
lean_inc(v_snd_5325_);
v_fst_5326_ = lean_ctor_get(v_snd_5324_, 0);
lean_inc(v_fst_5326_);
lean_dec(v_snd_5324_);
v_fst_5327_ = lean_ctor_get(v_snd_5325_, 0);
lean_inc(v_fst_5327_);
lean_dec(v_snd_5325_);
v___x_5328_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5327_);
lean_dec(v_fst_5327_);
if (lean_obj_tag(v___x_5328_) == 0)
{
lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5341_; 
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v___x_5328_, 0);
lean_dec(v_unused_5342_);
v___x_5330_ = v___x_5328_;
v_isShared_5331_ = v_isSharedCheck_5341_;
goto v_resetjp_5329_;
}
else
{
lean_dec(v___x_5328_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5341_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
uint8_t v___x_5332_; 
v___x_5332_ = lean_unbox(v_fst_5326_);
lean_dec(v_fst_5326_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5333_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5331_ == 0)
{
lean_ctor_set(v___x_5330_, 0, v___x_5333_);
v___x_5335_ = v___x_5330_;
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
if (v_isShared_5331_ == 0)
{
lean_ctor_set(v___x_5330_, 0, v___x_5337_);
v___x_5339_ = v___x_5330_;
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
}
else
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec(v_fst_5326_);
v_a_5343_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5328_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5328_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
default: 
{
lean_object* v_snd_5351_; lean_object* v_snd_5352_; lean_object* v_snd_5353_; lean_object* v_fst_5354_; lean_object* v_fst_5355_; lean_object* v___x_5356_; size_t v_sz_5357_; lean_object* v___x_5358_; 
v_snd_5351_ = lean_ctor_get(v_a_5310_, 1);
lean_del_object(v___x_5312_);
v_snd_5352_ = lean_ctor_get(v_snd_5351_, 1);
v_snd_5353_ = lean_ctor_get(v_snd_5352_, 1);
lean_inc(v_snd_5353_);
v_fst_5354_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_fst_5354_);
lean_dec(v_a_5310_);
v_fst_5355_ = lean_ctor_get(v_snd_5353_, 0);
lean_inc(v_fst_5355_);
lean_dec(v_snd_5353_);
v___x_5356_ = lean_box(0);
v_sz_5357_ = lean_array_size(v_fst_5355_);
v___x_5358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5355_, v_sz_5357_, v___x_5300_, v___x_5356_);
lean_dec(v_fst_5355_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5371_; 
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5372_);
v___x_5360_ = v___x_5358_;
v_isShared_5361_ = v_isSharedCheck_5371_;
goto v_resetjp_5359_;
}
else
{
lean_dec(v___x_5358_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5371_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
uint8_t v___x_5362_; 
v___x_5362_ = lean_unbox(v_fst_5354_);
lean_dec(v_fst_5354_);
if (v___x_5362_ == 0)
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
v___x_5363_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v___x_5363_);
v___x_5365_ = v___x_5360_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
else
{
lean_object* v___x_5367_; lean_object* v___x_5369_; 
v___x_5367_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v___x_5367_);
v___x_5369_ = v___x_5360_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5367_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec(v_fst_5354_);
v_a_5373_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5358_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5358_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
v_a_5382_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5309_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5309_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
lean_dec_ref(v_mods_5290_);
lean_dec_ref(v_args_5288_);
v_a_5390_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5297_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5297_);
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
else
{
lean_object* v___x_5398_; lean_object* v___x_5399_; 
lean_dec_ref(v_mods_5290_);
lean_dec_ref(v_args_5288_);
v___x_5398_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5399_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5398_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5407_; 
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5407_ == 0)
{
lean_object* v_unused_5408_; 
v_unused_5408_ = lean_ctor_get(v___x_5399_, 0);
lean_dec(v_unused_5408_);
v___x_5401_ = v___x_5399_;
v_isShared_5402_ = v_isSharedCheck_5407_;
goto v_resetjp_5400_;
}
else
{
lean_dec(v___x_5399_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5407_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5403_; lean_object* v___x_5405_; 
v___x_5403_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 0, v___x_5403_);
v___x_5405_ = v___x_5401_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
else
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5416_; 
v_a_5409_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5411_ = v___x_5399_;
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5399_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5414_; 
if (v_isShared_5412_ == 0)
{
v___x_5414_ = v___x_5411_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5409_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Lake_BuiltinLint_run(v_args_5417_);
return v_res_5419_;
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
