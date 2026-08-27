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
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1_value;
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
uint8_t v___y_359_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_i_357_, v___x_362_);
v___x_364_ = lean_nat_dec_le(v___x_363_, v_stopPos_356_);
lean_dec(v___x_363_);
if (v___x_364_ == 0)
{
return v_i_357_;
}
else
{
if (v___x_364_ == 0)
{
v___y_359_ = v___x_364_;
goto v___jp_358_;
}
else
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_string_utf8_get(v_s_355_, v_i_357_);
v___x_366_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_365_);
v___y_359_ = v___x_366_;
goto v___jp_358_;
}
}
v___jp_358_:
{
if (v___y_359_ == 0)
{
return v_i_357_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_string_utf8_next(v_s_355_, v_i_357_);
lean_dec(v_i_357_);
v_i_357_ = v___x_360_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_367_, lean_object* v_stopPos_368_, lean_object* v_i_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_367_, v_stopPos_368_, v_i_369_);
lean_dec(v_stopPos_368_);
lean_dec_ref(v_s_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_e_374_; lean_object* v___x_375_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_string_utf8_byte_size(v_line_371_);
v_e_374_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_371_, v___x_373_, v___x_372_);
v___x_375_ = lean_string_utf8_extract(v_line_371_, v___x_372_, v_e_374_);
lean_dec(v_e_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_376_);
lean_dec_ref(v_line_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_382_);
lean_dec_ref(v_s_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
return v_x_384_;
}
else
{
lean_object* v_key_386_; lean_object* v_value_387_; lean_object* v_tail_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_key_386_ = lean_ctor_get(v_x_385_, 0);
v_value_387_ = lean_ctor_get(v_x_385_, 1);
v_tail_388_ = lean_ctor_get(v_x_385_, 2);
lean_inc(v_value_387_);
lean_inc(v_key_386_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_key_386_);
lean_ctor_set(v___x_389_, 1, v_value_387_);
v___x_390_ = lean_array_push(v_x_384_, v___x_389_);
v_x_384_ = v___x_390_;
v_x_385_ = v_tail_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_392_, v_x_393_);
lean_dec(v_x_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_395_, size_t v_i_396_, size_t v_stop_397_, lean_object* v_b_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_eq(v_i_396_, v_stop_397_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; size_t v___x_402_; size_t v___x_403_; 
v___x_400_ = lean_array_uget_borrowed(v_as_395_, v_i_396_);
v___x_401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_398_, v___x_400_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_add(v_i_396_, v___x_402_);
v_i_396_ = v___x_403_;
v_b_398_ = v___x_401_;
goto _start;
}
else
{
return v_b_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_stop_407_, lean_object* v_b_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_stop_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_407_);
lean_dec(v_stop_407_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_405_, v_i_boxed_409_, v_stop_boxed_410_, v_b_408_);
lean_dec_ref(v_as_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_putStr_415_; lean_object* v___x_416_; 
v___x_414_ = lean_get_stderr();
v_putStr_415_ = lean_ctor_get(v___x_414_, 4);
lean_inc_ref(v_putStr_415_);
lean_dec_ref(v___x_414_);
v___x_416_ = lean_apply_2(v_putStr_415_, v_s_412_, lean_box(0));
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_420_){
_start:
{
uint32_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = 10;
v___x_423_ = lean_string_push(v_s_420_, v___x_422_);
v___x_424_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
return v_x_428_;
}
else
{
lean_object* v_key_430_; lean_object* v_value_431_; lean_object* v_tail_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_key_430_ = lean_ctor_get(v_x_429_, 0);
v_value_431_ = lean_ctor_get(v_x_429_, 1);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
lean_inc(v_value_431_);
lean_inc(v_key_430_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_key_430_);
lean_ctor_set(v___x_433_, 1, v_value_431_);
v___x_434_ = lean_array_push(v_x_428_, v___x_433_);
v_x_428_ = v___x_434_;
v_x_429_ = v_tail_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_436_, v_x_437_);
lean_dec(v_x_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; size_t v___x_446_; size_t v___x_447_; 
v___x_444_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
v___x_445_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_442_, v___x_444_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_440_, v___x_446_);
v_i_440_ = v___x_447_;
v_b_442_ = v___x_445_;
goto _start;
}
else
{
return v_b_442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_449_, lean_object* v_i_450_, lean_object* v_stop_451_, lean_object* v_b_452_){
_start:
{
size_t v_i_boxed_453_; size_t v_stop_boxed_454_; lean_object* v_res_455_; 
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_stop_boxed_454_ = lean_unbox_usize(v_stop_451_);
lean_dec(v_stop_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_449_, v_i_boxed_453_, v_stop_boxed_454_, v_b_452_);
lean_dec_ref(v_as_449_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_fst_458_; lean_object* v_fst_459_; uint8_t v___x_460_; 
v_fst_458_ = lean_ctor_get(v_b_457_, 0);
v_fst_459_ = lean_ctor_get(v_a_456_, 0);
v___x_460_ = lean_nat_dec_lt(v_fst_458_, v_fst_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_461_, v_b_462_);
lean_dec_ref(v_b_462_);
lean_dec_ref(v_a_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_465_, lean_object* v_pivot_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_k_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_lt(v_k_469_, v_hi_465_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_k_469_);
v___x_471_ = lean_array_fswap(v_as_467_, v_i_468_, v_hi_465_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_i_468_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v_fst_473_; lean_object* v___x_474_; lean_object* v_fst_475_; uint8_t v___x_476_; 
v_fst_473_ = lean_ctor_get(v_pivot_466_, 0);
v___x_474_ = lean_array_fget_borrowed(v_as_467_, v_k_469_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
v___x_476_ = lean_nat_dec_lt(v_fst_473_, v_fst_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_k_469_, v___x_477_);
lean_dec(v_k_469_);
v_k_469_ = v___x_478_;
goto _start;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_array_fswap(v_as_467_, v_i_468_, v_k_469_);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v_i_468_, v___x_481_);
lean_dec(v_i_468_);
v___x_483_ = lean_nat_add(v_k_469_, v___x_481_);
lean_dec(v_k_469_);
v_as_467_ = v___x_480_;
v_i_468_ = v___x_482_;
v_k_469_ = v___x_483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_485_, lean_object* v_pivot_486_, lean_object* v_as_487_, lean_object* v_i_488_, lean_object* v_k_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_485_, v_pivot_486_, v_as_487_, v_i_488_, v_k_489_);
lean_dec_ref(v_pivot_486_);
lean_dec(v_hi_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_491_, lean_object* v_as_492_, lean_object* v_lo_493_, lean_object* v_hi_494_){
_start:
{
lean_object* v___y_496_; uint8_t v___x_506_; 
v___x_506_ = lean_nat_dec_lt(v_lo_493_, v_hi_494_);
if (v___x_506_ == 0)
{
lean_dec(v_lo_493_);
return v_as_492_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_mid_509_; lean_object* v___y_511_; lean_object* v___y_517_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_507_ = lean_nat_add(v_lo_493_, v_hi_494_);
v___x_508_ = lean_unsigned_to_nat(1u);
v_mid_509_ = lean_nat_shiftr(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
v___x_522_ = lean_array_fget_borrowed(v_as_492_, v_mid_509_);
v___x_523_ = lean_array_fget_borrowed(v_as_492_, v_lo_493_);
v___x_524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
v___y_517_ = v_as_492_;
goto v___jp_516_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_array_fswap(v_as_492_, v_lo_493_, v_mid_509_);
v___y_517_ = v___x_525_;
goto v___jp_516_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_array_fget_borrowed(v___y_511_, v_mid_509_);
v___x_513_ = lean_array_fget_borrowed(v___y_511_, v_hi_494_);
v___x_514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_mid_509_);
v___y_496_ = v___y_511_;
goto v___jp_495_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = lean_array_fswap(v___y_511_, v_mid_509_, v_hi_494_);
lean_dec(v_mid_509_);
v___y_496_ = v___x_515_;
goto v___jp_495_;
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_array_fget_borrowed(v___y_517_, v_hi_494_);
v___x_519_ = lean_array_fget_borrowed(v___y_517_, v_lo_493_);
v___x_520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
v___y_511_ = v___y_517_;
goto v___jp_510_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_array_fswap(v___y_517_, v_lo_493_, v_hi_494_);
v___y_511_ = v___x_521_;
goto v___jp_510_;
}
}
}
v___jp_495_:
{
lean_object* v_pivot_497_; lean_object* v___x_498_; lean_object* v_fst_499_; lean_object* v_snd_500_; uint8_t v___x_501_; 
v_pivot_497_ = lean_array_fget(v___y_496_, v_hi_494_);
lean_inc_n(v_lo_493_, 2);
v___x_498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_494_, v_pivot_497_, v___y_496_, v_lo_493_, v_lo_493_);
lean_dec(v_pivot_497_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_fst_499_);
v_snd_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_snd_500_);
lean_dec_ref(v___x_498_);
v___x_501_ = lean_nat_dec_le(v_hi_494_, v_fst_499_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_491_, v_snd_500_, v_lo_493_, v_fst_499_);
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_add(v_fst_499_, v___x_503_);
lean_dec(v_fst_499_);
v_as_492_ = v___x_502_;
v_lo_493_ = v___x_504_;
goto _start;
}
else
{
lean_dec(v_fst_499_);
lean_dec(v_lo_493_);
return v_snd_500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_526_, lean_object* v_as_527_, lean_object* v_lo_528_, lean_object* v_hi_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_526_, v_as_527_, v_lo_528_, v_hi_529_);
lean_dec(v_hi_529_);
lean_dec(v_n_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v_a_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_it_537_; lean_object* v_startInclusive_538_; lean_object* v_endExclusive_539_; 
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v_currPos_543_; lean_object* v_searcher_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_567_; 
v_currPos_543_ = lean_ctor_get(v_a_534_, 0);
v_searcher_544_ = lean_ctor_get(v_a_534_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_567_ == 0)
{
v___x_546_ = v_a_534_;
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_searcher_544_);
lean_inc(v_currPos_543_);
lean_dec(v_a_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v_decide_548_; 
v_decide_548_ = lean_nat_dec_eq(v_searcher_544_, v___x_533_);
if (v_decide_548_ == 0)
{
uint32_t v___x_549_; uint32_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = 10;
v___x_550_ = lean_string_utf8_get_fast(v_a_531_, v_searcher_544_);
v___x_551_ = lean_uint32_dec_eq(v___x_550_, v___x_549_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_string_utf8_next_fast(v_a_531_, v_searcher_544_);
lean_dec(v_searcher_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_552_);
v___x_554_ = v___x_546_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_currPos_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_556_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v_a_534_ = v___x_554_;
goto _start;
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_slice_560_; lean_object* v_nextIt_562_; 
v___x_557_ = lean_string_utf8_next_fast(v_a_531_, v_searcher_544_);
v___x_558_ = lean_nat_sub(v___x_557_, v_searcher_544_);
v___x_559_ = lean_nat_add(v_searcher_544_, v___x_558_);
lean_dec(v___x_558_);
v_slice_560_ = l_String_Slice_subslice_x21(v___x_532_, v_currPos_543_, v_searcher_544_);
lean_inc(v___x_559_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_559_);
lean_ctor_set(v___x_546_, 0, v___x_559_);
v_nextIt_562_ = v___x_546_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_559_);
v_nextIt_562_ = v_reuseFailAlloc_565_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v_startInclusive_563_; lean_object* v_endExclusive_564_; 
v_startInclusive_563_ = lean_ctor_get(v_slice_560_, 0);
lean_inc(v_startInclusive_563_);
v_endExclusive_564_ = lean_ctor_get(v_slice_560_, 1);
lean_inc(v_endExclusive_564_);
lean_dec_ref(v_slice_560_);
v_it_537_ = v_nextIt_562_;
v_startInclusive_538_ = v_startInclusive_563_;
v_endExclusive_539_ = v_endExclusive_564_;
goto v___jp_536_;
}
}
}
else
{
lean_object* v___x_566_; 
lean_del_object(v___x_546_);
lean_dec(v_searcher_544_);
v___x_566_ = lean_box(1);
lean_inc(v___x_533_);
v_it_537_ = v___x_566_;
v_startInclusive_538_ = v_currPos_543_;
v_endExclusive_539_ = v___x_533_;
goto v___jp_536_;
}
}
}
else
{
lean_dec(v___x_533_);
lean_dec_ref(v_a_531_);
return v_b_535_;
}
v___jp_536_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc_ref(v_a_531_);
v___x_540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_540_, 0, v_a_531_);
lean_ctor_set(v___x_540_, 1, v_startInclusive_538_);
lean_ctor_set(v___x_540_, 2, v_endExclusive_539_);
v___x_541_ = lean_array_push(v_b_535_, v___x_540_);
v_a_534_ = v_it_537_;
v_b_535_ = v___x_541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_a_571_, lean_object* v_b_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_568_, v___x_569_, v___x_570_, v_a_571_, v_b_572_);
lean_dec_ref(v___x_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_577_ == 0)
{
return v_bs_576_;
}
else
{
lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_bs_x27_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_v_578_ = lean_array_uget(v_bs_576_, v_i_575_);
v___x_579_ = lean_unsigned_to_nat(0u);
v_bs_x27_580_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_579_);
v___x_581_ = l_String_Slice_toString(v_v_578_);
lean_dec(v_v_578_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_575_, v___x_582_);
v___x_584_ = lean_array_uset(v_bs_x27_580_, v_i_575_, v___x_581_);
v_i_575_ = v___x_583_;
v_bs_576_ = v___x_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_586_, lean_object* v_i_587_, lean_object* v_bs_588_){
_start:
{
size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v_sz_boxed_589_ = lean_unbox_usize(v_sz_586_);
lean_dec(v_sz_586_);
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_589_, v_i_boxed_590_, v_bs_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
return v_x_592_;
}
else
{
lean_object* v_key_594_; lean_object* v_value_595_; lean_object* v_tail_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_619_; 
v_key_594_ = lean_ctor_get(v_x_593_, 0);
v_value_595_ = lean_ctor_get(v_x_593_, 1);
v_tail_596_ = lean_ctor_get(v_x_593_, 2);
v_isSharedCheck_619_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_619_ == 0)
{
v___x_598_ = v_x_593_;
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_tail_596_);
lean_inc(v_value_595_);
lean_inc(v_key_594_);
lean_dec(v_x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v_fold_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_600_ = lean_array_get_size(v_x_592_);
v___x_601_ = lean_uint64_of_nat(v_key_594_);
v___x_602_ = 32ULL;
v___x_603_ = lean_uint64_shift_right(v___x_601_, v___x_602_);
v_fold_604_ = lean_uint64_xor(v___x_601_, v___x_603_);
v___x_605_ = 16ULL;
v___x_606_ = lean_uint64_shift_right(v_fold_604_, v___x_605_);
v___x_607_ = lean_uint64_xor(v_fold_604_, v___x_606_);
v___x_608_ = lean_uint64_to_usize(v___x_607_);
v___x_609_ = lean_usize_of_nat(v___x_600_);
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_sub(v___x_609_, v___x_610_);
v___x_612_ = lean_usize_land(v___x_608_, v___x_611_);
v___x_613_ = lean_array_uget_borrowed(v_x_592_, v___x_612_);
lean_inc(v___x_613_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 2, v___x_613_);
v___x_615_ = v___x_598_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_key_594_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_value_595_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_613_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_array_uset(v_x_592_, v___x_612_, v___x_615_);
v_x_592_ = v___x_616_;
v_x_593_ = v_tail_596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_620_, lean_object* v_source_621_, lean_object* v_target_622_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_array_get_size(v_source_621_);
v___x_624_ = lean_nat_dec_lt(v_i_620_, v___x_623_);
if (v___x_624_ == 0)
{
lean_dec_ref(v_source_621_);
lean_dec(v_i_620_);
return v_target_622_;
}
else
{
lean_object* v_es_625_; lean_object* v___x_626_; lean_object* v_source_627_; lean_object* v_target_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_es_625_ = lean_array_fget(v_source_621_, v_i_620_);
v___x_626_ = lean_box(0);
v_source_627_ = lean_array_fset(v_source_621_, v_i_620_, v___x_626_);
v_target_628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_622_, v_es_625_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_i_620_, v___x_629_);
lean_dec(v_i_620_);
v_i_620_ = v___x_630_;
v_source_621_ = v_source_627_;
v_target_622_ = v_target_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_nbuckets_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_633_ = lean_array_get_size(v_data_632_);
v___x_634_ = lean_unsigned_to_nat(2u);
v_nbuckets_635_ = lean_nat_mul(v___x_633_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_box(0);
v___x_638_ = lean_mk_array(v_nbuckets_635_, v___x_637_);
v___x_639_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_636_, v_data_632_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
uint8_t v___x_642_; 
v___x_642_ = 0;
return v___x_642_;
}
else
{
lean_object* v_key_643_; lean_object* v_tail_644_; uint8_t v___x_645_; 
v_key_643_ = lean_ctor_get(v_x_641_, 0);
v_tail_644_ = lean_ctor_get(v_x_641_, 2);
v___x_645_ = lean_nat_dec_eq(v_key_643_, v_a_640_);
if (v___x_645_ == 0)
{
v_x_641_ = v_tail_644_;
goto _start;
}
else
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_647_, lean_object* v_x_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_647_, v_x_648_);
lean_dec(v_x_648_);
lean_dec(v_a_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_651_, lean_object* v_b_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_dec(v_b_652_);
lean_dec(v_a_651_);
return v_x_653_;
}
else
{
lean_object* v_key_654_; lean_object* v_value_655_; lean_object* v_tail_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_668_; 
v_key_654_ = lean_ctor_get(v_x_653_, 0);
v_value_655_ = lean_ctor_get(v_x_653_, 1);
v_tail_656_ = lean_ctor_get(v_x_653_, 2);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_668_ == 0)
{
v___x_658_ = v_x_653_;
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_tail_656_);
lean_inc(v_value_655_);
lean_inc(v_key_654_);
lean_dec(v_x_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_eq(v_key_654_, v_a_651_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_651_, v_b_652_, v_tail_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 2, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_key_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_value_655_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_666_; 
lean_dec(v_value_655_);
lean_dec(v_key_654_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_b_652_);
lean_ctor_set(v___x_658_, 0, v_a_651_);
v___x_666_ = v___x_658_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_b_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_tail_656_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_669_, lean_object* v_a_670_, lean_object* v_b_671_){
_start:
{
lean_object* v_size_672_; lean_object* v_buckets_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_716_; 
v_size_672_ = lean_ctor_get(v_m_669_, 0);
v_buckets_673_ = lean_ctor_get(v_m_669_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_m_669_);
if (v_isSharedCheck_716_ == 0)
{
v___x_675_ = v_m_669_;
v_isShared_676_ = v_isSharedCheck_716_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_buckets_673_);
lean_inc(v_size_672_);
lean_dec(v_m_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_716_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v_fold_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v_bkt_690_; uint8_t v___x_691_; 
v___x_677_ = lean_array_get_size(v_buckets_673_);
v___x_678_ = lean_uint64_of_nat(v_a_670_);
v___x_679_ = 32ULL;
v___x_680_ = lean_uint64_shift_right(v___x_678_, v___x_679_);
v_fold_681_ = lean_uint64_xor(v___x_678_, v___x_680_);
v___x_682_ = 16ULL;
v___x_683_ = lean_uint64_shift_right(v_fold_681_, v___x_682_);
v___x_684_ = lean_uint64_xor(v_fold_681_, v___x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = lean_usize_of_nat(v___x_677_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_sub(v___x_686_, v___x_687_);
v___x_689_ = lean_usize_land(v___x_685_, v___x_688_);
v_bkt_690_ = lean_array_uget_borrowed(v_buckets_673_, v___x_689_);
v___x_691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_670_, v_bkt_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v_size_x27_693_; lean_object* v___x_694_; lean_object* v_buckets_x27_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v_size_x27_693_ = lean_nat_add(v_size_672_, v___x_692_);
lean_dec(v_size_672_);
lean_inc(v_bkt_690_);
v___x_694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_694_, 0, v_a_670_);
lean_ctor_set(v___x_694_, 1, v_b_671_);
lean_ctor_set(v___x_694_, 2, v_bkt_690_);
v_buckets_x27_695_ = lean_array_uset(v_buckets_673_, v___x_689_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(4u);
v___x_697_ = lean_nat_mul(v_size_x27_693_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(3u);
v___x_699_ = lean_nat_div(v___x_697_, v___x_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_array_get_size(v_buckets_x27_695_);
v___x_701_ = lean_nat_dec_le(v___x_699_, v___x_700_);
lean_dec(v___x_699_);
if (v___x_701_ == 0)
{
lean_object* v_val_702_; lean_object* v___x_704_; 
v_val_702_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_695_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_val_702_);
lean_ctor_set(v___x_675_, 0, v_size_x27_693_);
v___x_704_ = v___x_675_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_size_x27_693_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_val_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_707_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_buckets_x27_695_);
lean_ctor_set(v___x_675_, 0, v_size_x27_693_);
v___x_707_ = v___x_675_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_size_x27_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_buckets_x27_695_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_object* v___x_709_; lean_object* v_buckets_x27_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
lean_inc(v_bkt_690_);
v___x_709_ = lean_box(0);
v_buckets_x27_710_ = lean_array_uset(v_buckets_673_, v___x_689_, v___x_709_);
v___x_711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_670_, v_b_671_, v_bkt_690_);
v___x_712_ = lean_array_uset(v_buckets_x27_710_, v___x_689_, v___x_711_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_712_);
v___x_714_ = v___x_675_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_size_672_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_717_, lean_object* v_as_718_, size_t v_i_719_, size_t v_stop_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_eq(v_i_719_, v_stop_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_array_uget_borrowed(v_as_718_, v_i_719_);
v___x_723_ = lean_name_eq(v_a_717_, v___x_722_);
if (v___x_723_ == 0)
{
size_t v___x_724_; size_t v___x_725_; 
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_719_, v___x_724_);
v_i_719_ = v___x_725_;
goto _start;
}
else
{
return v___x_723_;
}
}
else
{
uint8_t v___x_727_; 
v___x_727_ = 0;
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_728_, lean_object* v_as_729_, lean_object* v_i_730_, lean_object* v_stop_731_){
_start:
{
size_t v_i_boxed_732_; size_t v_stop_boxed_733_; uint8_t v_res_734_; lean_object* v_r_735_; 
v_i_boxed_732_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_stop_boxed_733_ = lean_unbox_usize(v_stop_731_);
lean_dec(v_stop_731_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_728_, v_as_729_, v_i_boxed_732_, v_stop_boxed_733_);
lean_dec_ref(v_as_729_);
lean_dec(v_a_728_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_as_736_);
v___x_740_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
return v___x_740_;
}
else
{
if (v___x_740_ == 0)
{
return v___x_740_;
}
else
{
size_t v___x_741_; size_t v___x_742_; uint8_t v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_739_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_737_, v_as_736_, v___x_741_, v___x_742_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_as_744_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_748_, lean_object* v_fallback_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_inc(v_fallback_749_);
return v_fallback_749_;
}
else
{
lean_object* v_key_751_; lean_object* v_value_752_; lean_object* v_tail_753_; uint8_t v___x_754_; 
v_key_751_ = lean_ctor_get(v_x_750_, 0);
v_value_752_ = lean_ctor_get(v_x_750_, 1);
v_tail_753_ = lean_ctor_get(v_x_750_, 2);
v___x_754_ = lean_nat_dec_eq(v_key_751_, v_a_748_);
if (v___x_754_ == 0)
{
v_x_750_ = v_tail_753_;
goto _start;
}
else
{
lean_inc(v_value_752_);
return v_value_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_756_, lean_object* v_fallback_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_756_, v_fallback_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec(v_fallback_757_);
lean_dec(v_a_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_fallback_762_){
_start:
{
lean_object* v_buckets_763_; lean_object* v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v_fold_768_; uint64_t v___x_769_; uint64_t v___x_770_; uint64_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_buckets_763_ = lean_ctor_get(v_m_760_, 1);
v___x_764_ = lean_array_get_size(v_buckets_763_);
v___x_765_ = lean_uint64_of_nat(v_a_761_);
v___x_766_ = 32ULL;
v___x_767_ = lean_uint64_shift_right(v___x_765_, v___x_766_);
v_fold_768_ = lean_uint64_xor(v___x_765_, v___x_767_);
v___x_769_ = 16ULL;
v___x_770_ = lean_uint64_shift_right(v_fold_768_, v___x_769_);
v___x_771_ = lean_uint64_xor(v_fold_768_, v___x_770_);
v___x_772_ = lean_uint64_to_usize(v___x_771_);
v___x_773_ = lean_usize_of_nat(v___x_764_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_sub(v___x_773_, v___x_774_);
v___x_776_ = lean_usize_land(v___x_772_, v___x_775_);
v___x_777_ = lean_array_uget_borrowed(v_buckets_763_, v___x_776_);
v___x_778_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_761_, v_fallback_762_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_779_, lean_object* v_a_780_, lean_object* v_fallback_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_779_, v_a_780_, v_fallback_781_);
lean_dec(v_fallback_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_m_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_785_, size_t v_sz_786_, size_t v_i_787_, lean_object* v_b_788_){
_start:
{
lean_object* v_a_791_; uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_788_);
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v_fst_798_; lean_object* v_snd_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_a_797_ = lean_array_uget_borrowed(v_as_785_, v_i_787_);
v_fst_798_ = lean_ctor_get(v_a_797_, 0);
v_snd_799_ = lean_ctor_get(v_a_797_, 1);
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_788_, v_fst_798_, v___x_800_);
v___x_802_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_801_, v_snd_799_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_inc(v_snd_799_);
v___x_803_ = lean_array_push(v___x_801_, v_snd_799_);
lean_inc(v_fst_798_);
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_788_, v_fst_798_, v___x_803_);
v_a_791_ = v___x_804_;
goto v___jp_790_;
}
else
{
lean_dec(v___x_801_);
v_a_791_ = v_b_788_;
goto v___jp_790_;
}
}
v___jp_790_:
{
size_t v___x_792_; size_t v___x_793_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_787_, v___x_792_);
v_i_787_ = v___x_793_;
v_b_788_ = v_a_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_805_, lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_){
_start:
{
size_t v_sz_boxed_810_; size_t v_i_boxed_811_; lean_object* v_res_812_; 
v_sz_boxed_810_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_811_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_805_, v_sz_boxed_810_, v_i_boxed_811_, v_b_808_);
lean_dec_ref(v_as_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_putStr_816_; lean_object* v___x_817_; 
v___x_815_ = lean_get_stdout();
v_putStr_816_ = lean_ctor_get(v___x_815_, 4);
lean_inc_ref(v_putStr_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = lean_apply_2(v_putStr_816_, v_s_813_, lean_box(0));
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_821_){
_start:
{
uint32_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = 10;
v___x_824_ = lean_string_push(v_s_821_, v___x_823_);
v___x_825_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_826_);
return v_res_828_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_829_, lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_830_, v___x_829_);
v___x_833_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_831_, v___x_829_);
v___x_834_ = lean_string_dec_lt(v___x_832_, v___x_833_);
lean_dec_ref(v___x_833_);
lean_dec_ref(v___x_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_835_, lean_object* v_a_836_, lean_object* v_b_837_){
_start:
{
uint8_t v___x_11497__boxed_838_; uint8_t v_res_839_; lean_object* v_r_840_; 
v___x_11497__boxed_838_ = lean_unbox(v___x_835_);
v_res_839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11497__boxed_838_, v_a_836_, v_b_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_841_, lean_object* v___x_842_, lean_object* v_hi_843_, lean_object* v_pivot_844_, lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_k_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_nat_dec_lt(v_k_847_, v_hi_843_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_k_847_);
lean_dec(v_pivot_844_);
v___x_849_ = lean_array_fswap(v_as_845_, v_i_846_, v_hi_843_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_i_846_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
return v___x_850_;
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_851_ = lean_nat_dec_lt(v___x_841_, v___x_842_);
v___x_852_ = lean_array_fget_borrowed(v_as_845_, v_k_847_);
lean_inc(v___x_852_);
v___x_853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_852_, v___x_851_);
lean_inc(v_pivot_844_);
v___x_854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_844_, v___x_851_);
v___x_855_ = lean_string_dec_lt(v___x_853_, v___x_854_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v___x_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_k_847_, v___x_856_);
lean_dec(v_k_847_);
v_k_847_ = v___x_857_;
goto _start;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_859_ = lean_array_fswap(v_as_845_, v_i_846_, v_k_847_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_i_846_, v___x_860_);
lean_dec(v_i_846_);
v___x_862_ = lean_nat_add(v_k_847_, v___x_860_);
lean_dec(v_k_847_);
v_as_845_ = v___x_859_;
v_i_846_ = v___x_861_;
v_k_847_ = v___x_862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v_hi_866_, lean_object* v_pivot_867_, lean_object* v_as_868_, lean_object* v_i_869_, lean_object* v_k_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_864_, v___x_865_, v_hi_866_, v_pivot_867_, v_as_868_, v_i_869_, v_k_870_);
lean_dec(v_hi_866_);
lean_dec(v___x_865_);
lean_dec(v___x_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_n_874_, lean_object* v_as_875_, lean_object* v_lo_876_, lean_object* v_hi_877_){
_start:
{
lean_object* v___y_879_; uint8_t v___x_889_; 
v___x_889_ = lean_nat_dec_lt(v_lo_876_, v_hi_877_);
if (v___x_889_ == 0)
{
lean_dec(v_lo_876_);
return v_as_875_;
}
else
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_mid_893_; lean_object* v___y_895_; lean_object* v___y_901_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_890_ = lean_nat_dec_lt(v___x_872_, v___x_873_);
v___x_891_ = lean_nat_add(v_lo_876_, v_hi_877_);
v___x_892_ = lean_unsigned_to_nat(1u);
v_mid_893_ = lean_nat_shiftr(v___x_891_, v___x_892_);
lean_dec(v___x_891_);
v___x_906_ = lean_array_fget_borrowed(v_as_875_, v_mid_893_);
v___x_907_ = lean_array_fget_borrowed(v_as_875_, v_lo_876_);
lean_inc(v___x_907_);
lean_inc(v___x_906_);
v___x_908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_890_, v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
v___y_901_ = v_as_875_;
goto v___jp_900_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_array_fswap(v_as_875_, v_lo_876_, v_mid_893_);
v___y_901_ = v___x_909_;
goto v___jp_900_;
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_array_fget_borrowed(v___y_895_, v_mid_893_);
v___x_897_ = lean_array_fget_borrowed(v___y_895_, v_hi_877_);
lean_inc(v___x_897_);
lean_inc(v___x_896_);
v___x_898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_890_, v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_dec(v_mid_893_);
v___y_879_ = v___y_895_;
goto v___jp_878_;
}
else
{
lean_object* v___x_899_; 
v___x_899_ = lean_array_fswap(v___y_895_, v_mid_893_, v_hi_877_);
lean_dec(v_mid_893_);
v___y_879_ = v___x_899_;
goto v___jp_878_;
}
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_array_fget_borrowed(v___y_901_, v_hi_877_);
v___x_903_ = lean_array_fget_borrowed(v___y_901_, v_lo_876_);
lean_inc(v___x_903_);
lean_inc(v___x_902_);
v___x_904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_890_, v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
v___y_895_ = v___y_901_;
goto v___jp_894_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_array_fswap(v___y_901_, v_lo_876_, v_hi_877_);
v___y_895_ = v___x_905_;
goto v___jp_894_;
}
}
}
v___jp_878_:
{
lean_object* v_pivot_880_; lean_object* v___x_881_; lean_object* v_fst_882_; lean_object* v_snd_883_; uint8_t v___x_884_; 
v_pivot_880_ = lean_array_fget(v___y_879_, v_hi_877_);
lean_inc_n(v_lo_876_, 2);
v___x_881_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_872_, v___x_873_, v_hi_877_, v_pivot_880_, v___y_879_, v_lo_876_, v_lo_876_);
v_fst_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_fst_882_);
v_snd_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_snd_883_);
lean_dec_ref(v___x_881_);
v___x_884_ = lean_nat_dec_le(v_hi_877_, v_fst_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_872_, v___x_873_, v_n_874_, v_snd_883_, v_lo_876_, v_fst_882_);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_add(v_fst_882_, v___x_886_);
lean_dec(v_fst_882_);
v_as_875_ = v___x_885_;
v_lo_876_ = v___x_887_;
goto _start;
}
else
{
lean_dec(v_fst_882_);
lean_dec(v_lo_876_);
return v_snd_883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v_n_912_, lean_object* v_as_913_, lean_object* v_lo_914_, lean_object* v_hi_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_910_, v___x_911_, v_n_912_, v_as_913_, v_lo_914_, v_hi_915_);
lean_dec(v_hi_915_);
lean_dec(v_n_912_);
lean_dec(v___x_911_);
lean_dec(v___x_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v___x_921_, size_t v_sz_922_, size_t v_i_923_, lean_object* v_bs_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_923_, v_sz_922_);
if (v___x_925_ == 0)
{
lean_dec_ref(v___x_919_);
return v_bs_924_;
}
else
{
uint8_t v___x_926_; lean_object* v_v_927_; lean_object* v___x_928_; lean_object* v_bs_x27_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
v___x_926_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
v_v_927_ = lean_array_uget(v_bs_924_, v_i_923_);
v___x_928_ = lean_unsigned_to_nat(0u);
v_bs_x27_929_ = lean_array_uset(v_bs_924_, v_i_923_, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_919_);
v___x_931_ = lean_string_append(v___x_919_, v___x_930_);
v___x_932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_927_, v___x_926_);
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
v___x_936_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_923_, v___x_938_);
v___x_940_ = lean_array_uset(v_bs_x27_929_, v_i_923_, v___x_937_);
v_i_923_ = v___x_939_;
v_bs_924_ = v___x_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v___x_944_, lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_bs_947_){
_start:
{
size_t v_sz_boxed_948_; size_t v_i_boxed_949_; lean_object* v_res_950_; 
v_sz_boxed_948_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_949_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_942_, v___x_943_, v___x_944_, v_sz_boxed_948_, v_i_boxed_949_, v_bs_947_);
lean_dec(v___x_944_);
lean_dec(v___x_943_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_951_, size_t v_sz_952_, size_t v_i_953_, lean_object* v_b_954_){
_start:
{
lean_object* v_a_957_; uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_b_954_);
return v___x_962_;
}
else
{
lean_object* v_a_963_; lean_object* v_fst_964_; lean_object* v_snd_965_; lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1006_; 
v_a_963_ = lean_array_uget_borrowed(v_as_951_, v_i_953_);
v_fst_964_ = lean_ctor_get(v_a_963_, 0);
v_snd_965_ = lean_ctor_get(v_a_963_, 1);
v_fst_966_ = lean_ctor_get(v_b_954_, 0);
v_snd_967_ = lean_ctor_get(v_b_954_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_b_954_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_969_ = v_b_954_;
v_isShared_970_ = v_isSharedCheck_1006_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_b_954_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1006_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_sub(v_fst_964_, v___x_971_);
v___x_973_ = lean_array_get_size(v_fst_966_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_976_; 
lean_dec(v___x_972_);
if (v_isShared_970_ == 0)
{
v___x_976_ = v___x_969_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_snd_967_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v_a_957_ = v___x_976_;
goto v___jp_956_;
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v___x_995_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___x_1000_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_array_fget_borrowed(v_fst_966_, v___x_972_);
v___x_980_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_979_);
v___x_995_ = lean_array_get_size(v_snd_965_);
v___x_1000_ = lean_nat_dec_eq(v___x_995_, v___x_978_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___y_1003_; uint8_t v___x_1005_; 
v___x_1001_ = lean_nat_sub(v___x_995_, v___x_971_);
v___x_1005_ = lean_nat_dec_le(v___x_978_, v___x_1001_);
if (v___x_1005_ == 0)
{
lean_inc(v___x_1001_);
v___y_1003_ = v___x_1001_;
goto v___jp_1002_;
}
else
{
v___y_1003_ = v___x_978_;
goto v___jp_1002_;
}
v___jp_1002_:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_le(v___y_1003_, v___x_1001_);
if (v___x_1004_ == 0)
{
lean_dec(v___x_1001_);
lean_inc(v___y_1003_);
v___y_997_ = v___y_1003_;
v___y_998_ = v___y_1003_;
goto v___jp_996_;
}
else
{
v___y_997_ = v___y_1003_;
v___y_998_ = v___x_1001_;
goto v___jp_996_;
}
}
}
else
{
lean_inc(v_snd_965_);
v___y_982_ = v_snd_965_;
goto v___jp_981_;
}
v___jp_981_:
{
size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v_sz_983_ = lean_array_size(v___y_982_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_980_, v___x_972_, v___x_973_, v_sz_983_, v___x_984_, v___y_982_);
lean_inc(v___x_972_);
v___x_986_ = l_Array_extract___redArg(v_fst_966_, v___x_978_, v___x_972_);
v___x_987_ = l_Array_append___redArg(v___x_986_, v___x_985_);
v___x_988_ = l_Array_extract___redArg(v_fst_966_, v___x_972_, v___x_973_);
lean_dec(v_fst_966_);
v___x_989_ = l_Array_append___redArg(v___x_987_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_array_get_size(v___x_985_);
lean_dec_ref(v___x_985_);
v___x_991_ = lean_nat_add(v_snd_967_, v___x_990_);
lean_dec(v_snd_967_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_991_);
lean_ctor_set(v___x_969_, 0, v___x_989_);
v___x_993_ = v___x_969_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
v_a_957_ = v___x_993_;
goto v___jp_956_;
}
}
v___jp_996_:
{
lean_object* v___x_999_; 
lean_inc(v_snd_965_);
v___x_999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_972_, v___x_973_, v___x_995_, v_snd_965_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
v___y_982_ = v___x_999_;
goto v___jp_981_;
}
}
}
}
v___jp_956_:
{
size_t v___x_958_; size_t v___x_959_; 
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_953_, v___x_958_);
v_i_953_ = v___x_959_;
v_b_954_ = v_a_957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1007_, lean_object* v_sz_1008_, lean_object* v_i_1009_, lean_object* v_b_1010_, lean_object* v___y_1011_){
_start:
{
size_t v_sz_boxed_1012_; size_t v_i_boxed_1013_; lean_object* v_res_1014_; 
v_sz_boxed_1012_ = lean_unbox_usize(v_sz_1008_);
lean_dec(v_sz_1008_);
v_i_boxed_1013_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1007_, v_sz_boxed_1012_, v_i_boxed_1013_, v_b_1010_);
lean_dec_ref(v_as_1007_);
return v_res_1014_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_unsigned_to_nat(16u);
v___x_1017_ = lean_mk_array(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1031_, size_t v_sz_1032_, size_t v_i_1033_, lean_object* v_b_1034_){
_start:
{
lean_object* v_a_1037_; uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_lt(v_i_1033_, v_sz_1032_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_b_1034_);
return v___x_1042_;
}
else
{
lean_object* v_a_1043_; lean_object* v_snd_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1153_; 
v_a_1043_ = lean_array_uget_borrowed(v_as_1031_, v_i_1033_);
v_snd_1044_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_snd_1044_);
v_fst_1045_ = lean_ctor_get(v_snd_1044_, 0);
v_snd_1046_ = lean_ctor_get(v_snd_1044_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_snd_1044_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1048_ = v_snd_1044_;
v_isShared_1049_ = v_isSharedCheck_1153_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v_snd_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1153_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; size_t v_sz_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_1052_ = lean_array_size(v_snd_1046_);
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1046_, v_sz_1052_, v___x_1053_, v___x_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___x_1070_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = lean_box(0);
v___x_1070_ = l_IO_FS_readFile(v_fst_1045_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_size_1075_; lean_object* v_buckets_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; size_t v_sz_1079_; lean_object* v___x_1080_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1124_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
lean_dec(v_snd_1046_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_n(v_a_1071_, 2);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = lean_string_utf8_byte_size(v_a_1071_);
v___x_1073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1073_, 0, v_a_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1050_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
v___x_1074_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_1073_);
v_size_1075_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_size_1075_);
v_buckets_1076_ = lean_ctor_get(v_a_1055_, 1);
lean_inc_ref(v_buckets_1076_);
lean_dec(v_a_1055_);
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1078_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1071_, v___x_1073_, v___x_1072_, v___x_1074_, v___x_1077_);
lean_dec_ref_known(v___x_1073_, 3);
v_sz_1079_ = lean_array_size(v___x_1078_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1079_, v___x_1053_, v___x_1078_);
v___x_1130_ = lean_mk_empty_array_with_capacity(v_size_1075_);
lean_dec(v_size_1075_);
v___x_1131_ = lean_array_get_size(v_buckets_1076_);
v___x_1132_ = lean_nat_dec_lt(v___x_1050_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v_buckets_1076_);
v___y_1124_ = v___x_1130_;
goto v___jp_1123_;
}
else
{
size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_usize_of_nat(v___x_1131_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1076_, v___x_1053_, v___x_1133_, v___x_1130_);
lean_dec_ref(v_buckets_1076_);
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
v___jp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___x_1050_);
lean_ctor_set(v___x_1048_, 0, v___x_1080_);
v___x_1085_ = v___x_1048_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1050_);
v___x_1085_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v_sz_1086_; lean_object* v___x_1087_; 
v_sz_1086_ = lean_array_size(v___y_1083_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1083_, v_sz_1086_, v___x_1053_, v___x_1085_);
lean_dec_ref(v___y_1083_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; uint8_t v___x_1091_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v_fst_1089_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_fst_1089_);
v_snd_1090_ = lean_ctor_get(v_a_1088_, 1);
lean_inc(v_snd_1090_);
lean_dec(v_a_1088_);
v___x_1091_ = lean_nat_dec_lt(v___x_1050_, v_snd_1090_);
if (v___x_1091_ == 0)
{
lean_dec(v_snd_1090_);
lean_dec(v_fst_1089_);
lean_dec(v_fst_1045_);
v_a_1037_ = v___x_1056_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1090_);
v___x_1093_ = l_Nat_reprFast(v_snd_1090_);
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_nat_dec_eq(v_snd_1090_, v___y_1082_);
lean_dec(v_snd_1090_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1058_ = v___x_1096_;
v___y_1059_ = v_fst_1089_;
v___y_1060_ = v___x_1098_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1058_ = v___x_1096_;
v___y_1059_ = v_fst_1089_;
v___y_1060_ = v___x_1099_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_fst_1045_);
v_a_1100_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1087_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1087_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
v___jp_1109_:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1110_, v___y_1112_, v___y_1111_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec(v___y_1110_);
v___y_1082_ = v___y_1113_;
v___y_1083_ = v___x_1115_;
goto v___jp_1081_;
}
v___jp_1116_:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_nat_dec_le(v___y_1121_, v___y_1118_);
if (v___x_1122_ == 0)
{
lean_dec(v___y_1118_);
lean_inc(v___y_1121_);
v___y_1110_ = v___y_1117_;
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1119_;
v___y_1113_ = v___y_1120_;
v___y_1114_ = v___y_1121_;
goto v___jp_1109_;
}
else
{
v___y_1110_ = v___y_1117_;
v___y_1111_ = v___y_1121_;
v___y_1112_ = v___y_1119_;
v___y_1113_ = v___y_1120_;
v___y_1114_ = v___y_1118_;
goto v___jp_1109_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_array_get_size(v___y_1124_);
v___x_1127_ = lean_nat_dec_eq(v___x_1126_, v___x_1050_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_nat_sub(v___x_1126_, v___x_1125_);
v___x_1129_ = lean_nat_dec_le(v___x_1050_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_inc(v___x_1128_);
v___y_1117_ = v___x_1126_;
v___y_1118_ = v___x_1128_;
v___y_1119_ = v___y_1124_;
v___y_1120_ = v___x_1125_;
v___y_1121_ = v___x_1128_;
goto v___jp_1116_;
}
else
{
v___y_1117_ = v___x_1126_;
v___y_1118_ = v___x_1128_;
v___y_1119_ = v___y_1124_;
v___y_1120_ = v___x_1125_;
v___y_1121_ = v___x_1050_;
goto v___jp_1116_;
}
}
else
{
v___y_1082_ = v___x_1125_;
v___y_1083_ = v___y_1124_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref_known(v___x_1070_, 1);
lean_dec(v_a_1055_);
lean_del_object(v___x_1048_);
v___x_1135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1136_ = lean_string_append(v___x_1135_, v_fst_1045_);
lean_dec(v_fst_1045_);
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
v___x_1139_ = lean_array_get_size(v_snd_1046_);
lean_dec(v_snd_1046_);
v___x_1140_ = l_Nat_reprFast(v___x_1139_);
v___x_1141_ = lean_string_append(v___x_1138_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___x_1144_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
v_a_1037_ = v___x_1056_;
goto v___jp_1036_;
}
else
{
return v___x_1144_;
}
}
v___jp_1057_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1061_ = lean_string_append(v___y_1058_, v___y_1060_);
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
v___x_1064_ = lean_string_append(v___x_1063_, v_fst_1045_);
v___x_1065_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref_known(v___x_1065_, 1);
v___x_1066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_1067_ = lean_array_to_list(v___y_1059_);
v___x_1068_ = l_String_intercalate(v___x_1066_, v___x_1067_);
v___x_1069_ = l_IO_FS_writeFile(v_fst_1045_, v___x_1068_);
lean_dec_ref(v___x_1068_);
lean_dec(v_fst_1045_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_dec_ref_known(v___x_1069_, 1);
v_a_1037_ = v___x_1056_;
goto v___jp_1036_;
}
else
{
return v___x_1069_;
}
}
else
{
lean_dec(v___y_1059_);
lean_dec(v_fst_1045_);
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1048_);
lean_dec(v_snd_1046_);
lean_dec(v_fst_1045_);
v_a_1145_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1054_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1054_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
v___jp_1036_:
{
size_t v___x_1038_; size_t v___x_1039_; 
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1033_, v___x_1038_);
v_i_1033_ = v___x_1039_;
v_b_1034_ = v_a_1037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1154_, v_sz_boxed_1159_, v_i_boxed_1160_, v_b_1157_);
lean_dec_ref(v_as_1154_);
return v_res_1161_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
uint8_t v___x_1164_; 
v___x_1164_ = 0;
return v___x_1164_;
}
else
{
lean_object* v_key_1165_; lean_object* v_tail_1166_; uint8_t v___x_1167_; 
v_key_1165_ = lean_ctor_get(v_x_1163_, 0);
v_tail_1166_ = lean_ctor_get(v_x_1163_, 2);
v___x_1167_ = lean_string_dec_eq(v_key_1165_, v_a_1162_);
if (v___x_1167_ == 0)
{
v_x_1163_ = v_tail_1166_;
goto _start;
}
else
{
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1169_, lean_object* v_x_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1169_, v_x_1170_);
lean_dec(v_x_1170_);
lean_dec_ref(v_a_1169_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1173_, lean_object* v_b_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_dec(v_b_1174_);
lean_dec_ref(v_a_1173_);
return v_x_1175_;
}
else
{
lean_object* v_key_1176_; lean_object* v_value_1177_; lean_object* v_tail_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1190_; 
v_key_1176_ = lean_ctor_get(v_x_1175_, 0);
v_value_1177_ = lean_ctor_get(v_x_1175_, 1);
v_tail_1178_ = lean_ctor_get(v_x_1175_, 2);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1180_ = v_x_1175_;
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_tail_1178_);
lean_inc(v_value_1177_);
lean_inc(v_key_1176_);
lean_dec(v_x_1175_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_string_dec_eq(v_key_1176_, v_a_1173_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1173_, v_b_1174_, v_tail_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 2, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_key_1176_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_value_1177_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v___x_1188_; 
lean_dec(v_value_1177_);
lean_dec(v_key_1176_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_b_1174_);
lean_ctor_set(v___x_1180_, 0, v_a_1173_);
v___x_1188_ = v___x_1180_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_b_1174_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_tail_1178_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
return v_x_1191_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1218_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1197_ = v_x_1192_;
v_isShared_1198_ = v_isSharedCheck_1218_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_tail_1195_);
lean_inc(v_value_1194_);
lean_inc(v_key_1193_);
lean_dec(v_x_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1218_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v_fold_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1199_ = lean_array_get_size(v_x_1191_);
v___x_1200_ = lean_string_hash(v_key_1193_);
v___x_1201_ = 32ULL;
v___x_1202_ = lean_uint64_shift_right(v___x_1200_, v___x_1201_);
v_fold_1203_ = lean_uint64_xor(v___x_1200_, v___x_1202_);
v___x_1204_ = 16ULL;
v___x_1205_ = lean_uint64_shift_right(v_fold_1203_, v___x_1204_);
v___x_1206_ = lean_uint64_xor(v_fold_1203_, v___x_1205_);
v___x_1207_ = lean_uint64_to_usize(v___x_1206_);
v___x_1208_ = lean_usize_of_nat(v___x_1199_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_sub(v___x_1208_, v___x_1209_);
v___x_1211_ = lean_usize_land(v___x_1207_, v___x_1210_);
v___x_1212_ = lean_array_uget_borrowed(v_x_1191_, v___x_1211_);
lean_inc(v___x_1212_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 2, v___x_1212_);
v___x_1214_ = v___x_1197_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_key_1193_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_value_1194_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_array_uset(v_x_1191_, v___x_1211_, v___x_1214_);
v_x_1191_ = v___x_1215_;
v_x_1192_ = v_tail_1195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1219_, lean_object* v_source_1220_, lean_object* v_target_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_array_get_size(v_source_1220_);
v___x_1223_ = lean_nat_dec_lt(v_i_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v_source_1220_);
lean_dec(v_i_1219_);
return v_target_1221_;
}
else
{
lean_object* v_es_1224_; lean_object* v___x_1225_; lean_object* v_source_1226_; lean_object* v_target_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_es_1224_ = lean_array_fget(v_source_1220_, v_i_1219_);
v___x_1225_ = lean_box(0);
v_source_1226_ = lean_array_fset(v_source_1220_, v_i_1219_, v___x_1225_);
v_target_1227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1221_, v_es_1224_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_i_1219_, v___x_1228_);
lean_dec(v_i_1219_);
v_i_1219_ = v___x_1229_;
v_source_1220_ = v_source_1226_;
v_target_1221_ = v_target_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_nbuckets_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1232_ = lean_array_get_size(v_data_1231_);
v___x_1233_ = lean_unsigned_to_nat(2u);
v_nbuckets_1234_ = lean_nat_mul(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_mk_array(v_nbuckets_1234_, v___x_1236_);
v___x_1238_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1235_, v_data_1231_, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1239_, lean_object* v_a_1240_, lean_object* v_b_1241_){
_start:
{
lean_object* v_size_1242_; lean_object* v_buckets_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1286_; 
v_size_1242_ = lean_ctor_get(v_m_1239_, 0);
v_buckets_1243_ = lean_ctor_get(v_m_1239_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_m_1239_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1245_ = v_m_1239_;
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_buckets_1243_);
lean_inc(v_size_1242_);
lean_dec(v_m_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; uint64_t v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v_fold_1251_; uint64_t v___x_1252_; uint64_t v___x_1253_; uint64_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v_bkt_1260_; uint8_t v___x_1261_; 
v___x_1247_ = lean_array_get_size(v_buckets_1243_);
v___x_1248_ = lean_string_hash(v_a_1240_);
v___x_1249_ = 32ULL;
v___x_1250_ = lean_uint64_shift_right(v___x_1248_, v___x_1249_);
v_fold_1251_ = lean_uint64_xor(v___x_1248_, v___x_1250_);
v___x_1252_ = 16ULL;
v___x_1253_ = lean_uint64_shift_right(v_fold_1251_, v___x_1252_);
v___x_1254_ = lean_uint64_xor(v_fold_1251_, v___x_1253_);
v___x_1255_ = lean_uint64_to_usize(v___x_1254_);
v___x_1256_ = lean_usize_of_nat(v___x_1247_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_sub(v___x_1256_, v___x_1257_);
v___x_1259_ = lean_usize_land(v___x_1255_, v___x_1258_);
v_bkt_1260_ = lean_array_uget_borrowed(v_buckets_1243_, v___x_1259_);
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1240_, v_bkt_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v_size_x27_1263_; lean_object* v___x_1264_; lean_object* v_buckets_x27_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v_size_x27_1263_ = lean_nat_add(v_size_1242_, v___x_1262_);
lean_dec(v_size_1242_);
lean_inc(v_bkt_1260_);
v___x_1264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1264_, 0, v_a_1240_);
lean_ctor_set(v___x_1264_, 1, v_b_1241_);
lean_ctor_set(v___x_1264_, 2, v_bkt_1260_);
v_buckets_x27_1265_ = lean_array_uset(v_buckets_1243_, v___x_1259_, v___x_1264_);
v___x_1266_ = lean_unsigned_to_nat(4u);
v___x_1267_ = lean_nat_mul(v_size_x27_1263_, v___x_1266_);
v___x_1268_ = lean_unsigned_to_nat(3u);
v___x_1269_ = lean_nat_div(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_array_get_size(v_buckets_x27_1265_);
v___x_1271_ = lean_nat_dec_le(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
if (v___x_1271_ == 0)
{
lean_object* v_val_1272_; lean_object* v___x_1274_; 
v_val_1272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1265_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_val_1272_);
lean_ctor_set(v___x_1245_, 0, v_size_x27_1263_);
v___x_1274_ = v___x_1245_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_size_x27_1263_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_val_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
else
{
lean_object* v___x_1277_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_buckets_x27_1265_);
lean_ctor_set(v___x_1245_, 0, v_size_x27_1263_);
v___x_1277_ = v___x_1245_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_size_x27_1263_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_buckets_x27_1265_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v_buckets_x27_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_inc(v_bkt_1260_);
v___x_1279_ = lean_box(0);
v_buckets_x27_1280_ = lean_array_uset(v_buckets_1243_, v___x_1259_, v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1240_, v_b_1241_, v_bkt_1260_);
v___x_1282_ = lean_array_uset(v_buckets_x27_1280_, v___x_1259_, v___x_1281_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1282_);
v___x_1284_ = v___x_1245_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_size_1242_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1287_, lean_object* v_fallback_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_inc(v_fallback_1288_);
return v_fallback_1288_;
}
else
{
lean_object* v_key_1290_; lean_object* v_value_1291_; lean_object* v_tail_1292_; uint8_t v___x_1293_; 
v_key_1290_ = lean_ctor_get(v_x_1289_, 0);
v_value_1291_ = lean_ctor_get(v_x_1289_, 1);
v_tail_1292_ = lean_ctor_get(v_x_1289_, 2);
v___x_1293_ = lean_string_dec_eq(v_key_1290_, v_a_1287_);
if (v___x_1293_ == 0)
{
v_x_1289_ = v_tail_1292_;
goto _start;
}
else
{
lean_inc(v_value_1291_);
return v_value_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1295_, lean_object* v_fallback_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1295_, v_fallback_1296_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec(v_fallback_1296_);
lean_dec_ref(v_a_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1299_, lean_object* v_a_1300_, lean_object* v_fallback_1301_){
_start:
{
lean_object* v_buckets_1302_; lean_object* v___x_1303_; uint64_t v___x_1304_; uint64_t v___x_1305_; uint64_t v___x_1306_; uint64_t v_fold_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_buckets_1302_ = lean_ctor_get(v_m_1299_, 1);
v___x_1303_ = lean_array_get_size(v_buckets_1302_);
v___x_1304_ = lean_string_hash(v_a_1300_);
v___x_1305_ = 32ULL;
v___x_1306_ = lean_uint64_shift_right(v___x_1304_, v___x_1305_);
v_fold_1307_ = lean_uint64_xor(v___x_1304_, v___x_1306_);
v___x_1308_ = 16ULL;
v___x_1309_ = lean_uint64_shift_right(v_fold_1307_, v___x_1308_);
v___x_1310_ = lean_uint64_xor(v_fold_1307_, v___x_1309_);
v___x_1311_ = lean_uint64_to_usize(v___x_1310_);
v___x_1312_ = lean_usize_of_nat(v___x_1303_);
v___x_1313_ = ((size_t)1ULL);
v___x_1314_ = lean_usize_sub(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_usize_land(v___x_1311_, v___x_1314_);
v___x_1316_ = lean_array_uget_borrowed(v_buckets_1302_, v___x_1315_);
v___x_1317_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1300_, v_fallback_1301_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1318_, lean_object* v_a_1319_, lean_object* v_fallback_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1318_, v_a_1319_, v_fallback_1320_);
lean_dec(v_fallback_1320_);
lean_dec_ref(v_a_1319_);
lean_dec_ref(v_m_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1324_, size_t v_sz_1325_, size_t v_i_1326_, lean_object* v_b_1327_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_lt(v_i_1326_, v_sz_1325_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_b_1327_);
return v___x_1330_;
}
else
{
lean_object* v_a_1331_; lean_object* v_file_1332_; lean_object* v_pos_1333_; lean_object* v_option_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1360_; 
v_a_1331_ = lean_array_uget_borrowed(v_as_1324_, v_i_1326_);
v_file_1332_ = lean_ctor_get(v_a_1331_, 0);
v_pos_1333_ = lean_ctor_get(v_a_1331_, 1);
lean_inc_ref(v_pos_1333_);
v_option_1334_ = lean_ctor_get(v_a_1331_, 2);
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1332_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_file_1332_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1327_, v_file_1332_, v___x_1336_);
lean_dec_ref_known(v___x_1336_, 2);
v_fst_1338_ = lean_ctor_get(v___x_1337_, 0);
v_snd_1339_ = lean_ctor_get(v___x_1337_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1341_ = v___x_1337_;
v_isShared_1342_ = v_isSharedCheck_1360_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_inc(v_fst_1338_);
lean_dec(v___x_1337_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1360_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_line_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1358_; 
v_line_1343_ = lean_ctor_get(v_pos_1333_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_pos_1333_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_pos_1333_, 1);
lean_dec(v_unused_1359_);
v___x_1345_ = v_pos_1333_;
v_isShared_1346_ = v_isSharedCheck_1358_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_line_1343_);
lean_dec(v_pos_1333_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1358_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
lean_inc(v_option_1334_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_option_1334_);
lean_ctor_set(v___x_1341_, 0, v_line_1343_);
v___x_1348_ = v___x_1341_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_line_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_option_1334_);
v___x_1348_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_array_push(v_snd_1339_, v___x_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1349_);
lean_ctor_set(v___x_1345_, 0, v_fst_1338_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_fst_1338_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; 
lean_inc_ref(v_file_1332_);
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1327_, v_file_1332_, v___x_1351_);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1326_, v___x_1353_);
v_i_1326_ = v___x_1354_;
v_b_1327_ = v___x_1352_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1361_, lean_object* v_sz_1362_, lean_object* v_i_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_){
_start:
{
size_t v_sz_boxed_1366_; size_t v_i_boxed_1367_; lean_object* v_res_1368_; 
v_sz_boxed_1366_ = lean_unbox_usize(v_sz_1362_);
lean_dec(v_sz_1362_);
v_i_boxed_1367_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1361_, v_sz_boxed_1366_, v_i_boxed_1367_, v_b_1364_);
lean_dec_ref(v_as_1361_);
return v_res_1368_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_unsigned_to_nat(16u);
v___x_1371_ = lean_mk_array(v___x_1370_, v___x_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_byFile_1374_; 
v___x_1372_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1373_ = lean_unsigned_to_nat(0u);
v_byFile_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1374_, 0, v___x_1373_);
lean_ctor_set(v_byFile_1374_, 1, v___x_1372_);
return v_byFile_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_byFile_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = lean_unsigned_to_nat(0u);
v_byFile_1378_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1379_ = lean_array_size(v_records_1375_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1375_, v_sz_1379_, v___x_1380_, v_byFile_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___y_1384_; lean_object* v_size_1396_; lean_object* v_buckets_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_size_1396_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_size_1396_);
v_buckets_1397_ = lean_ctor_get(v_a_1382_, 1);
lean_inc_ref(v_buckets_1397_);
lean_dec(v_a_1382_);
v___x_1398_ = lean_mk_empty_array_with_capacity(v_size_1396_);
lean_dec(v_size_1396_);
v___x_1399_ = lean_array_get_size(v_buckets_1397_);
v___x_1400_ = lean_nat_dec_lt(v___x_1377_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v_buckets_1397_);
v___y_1384_ = v___x_1398_;
goto v___jp_1383_;
}
else
{
size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_usize_of_nat(v___x_1399_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1397_, v___x_1380_, v___x_1401_, v___x_1398_);
lean_dec_ref(v_buckets_1397_);
v___y_1384_ = v___x_1402_;
goto v___jp_1383_;
}
v___jp_1383_:
{
lean_object* v___x_1385_; size_t v_sz_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_box(0);
v_sz_1386_ = lean_array_size(v___y_1384_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1384_, v_sz_1386_, v___x_1380_, v___x_1385_);
lean_dec_ref(v___y_1384_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1387_, 0);
lean_dec(v_unused_1395_);
v___x_1389_ = v___x_1387_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v___x_1387_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1385_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1381_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1381_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1411_);
lean_dec_ref(v_records_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_, lean_object* v_a_1416_, lean_object* v_fallback_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1415_, v_a_1416_, v_fallback_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1419_, lean_object* v_m_1420_, lean_object* v_a_1421_, lean_object* v_fallback_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1419_, v_m_1420_, v_a_1421_, v_fallback_1422_);
lean_dec(v_fallback_1422_);
lean_dec_ref(v_a_1421_);
lean_dec_ref(v_m_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1424_, lean_object* v_m_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1425_, v_a_1426_, v_b_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1429_, lean_object* v_m_1430_, lean_object* v_a_1431_, lean_object* v_fallback_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1430_, v_a_1431_, v_fallback_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_, lean_object* v_fallback_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1434_, v_m_1435_, v_a_1436_, v_fallback_1437_);
lean_dec(v_fallback_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_m_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1439_, lean_object* v_m_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1440_, v_a_1441_, v_b_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1444_, lean_object* v___x_1445_, lean_object* v___x_1446_, lean_object* v_inst_1447_, lean_object* v_R_1448_, lean_object* v_a_1449_, lean_object* v_b_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1444_, v___x_1445_, v___x_1446_, v_a_1449_, v_b_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1452_, lean_object* v___x_1453_, lean_object* v___x_1454_, lean_object* v_inst_1455_, lean_object* v_R_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1452_, v___x_1453_, v___x_1454_, v_inst_1455_, v_R_1456_, v_a_1457_, v_b_1458_);
lean_dec_ref(v___x_1453_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1460_, lean_object* v___x_1461_, lean_object* v_n_1462_, lean_object* v_as_1463_, lean_object* v_lo_1464_, lean_object* v_hi_1465_, lean_object* v_w_1466_, lean_object* v_hlo_1467_, lean_object* v_hhi_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1460_, v___x_1461_, v_n_1462_, v_as_1463_, v_lo_1464_, v_hi_1465_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v_n_1472_, lean_object* v_as_1473_, lean_object* v_lo_1474_, lean_object* v_hi_1475_, lean_object* v_w_1476_, lean_object* v_hlo_1477_, lean_object* v_hhi_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1470_, v___x_1471_, v_n_1472_, v_as_1473_, v_lo_1474_, v_hi_1475_, v_w_1476_, v_hlo_1477_, v_hhi_1478_);
lean_dec(v_hi_1475_);
lean_dec(v_n_1472_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1480_, lean_object* v_as_1481_, lean_object* v_lo_1482_, lean_object* v_hi_1483_, lean_object* v_w_1484_, lean_object* v_hlo_1485_, lean_object* v_hhi_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1480_, v_as_1481_, v_lo_1482_, v_hi_1483_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1488_, lean_object* v_as_1489_, lean_object* v_lo_1490_, lean_object* v_hi_1491_, lean_object* v_w_1492_, lean_object* v_hlo_1493_, lean_object* v_hhi_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1488_, v_as_1489_, v_lo_1490_, v_hi_1491_, v_w_1492_, v_hlo_1493_, v_hhi_1494_);
lean_dec(v_hi_1491_);
lean_dec(v_n_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1496_, lean_object* v_a_1497_, lean_object* v_fallback_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1497_, v_fallback_1498_, v_x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1501_, lean_object* v_a_1502_, lean_object* v_fallback_1503_, lean_object* v_x_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1501_, v_a_1502_, v_fallback_1503_, v_x_1504_);
lean_dec(v_x_1504_);
lean_dec(v_fallback_1503_);
lean_dec_ref(v_a_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1506_, lean_object* v_a_1507_, lean_object* v_x_1508_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1507_, v_x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1510_, v_a_1511_, v_x_1512_);
lean_dec(v_x_1512_);
lean_dec_ref(v_a_1511_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1515_, lean_object* v_data_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v_x_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1519_, v_b_1520_, v_x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1523_, lean_object* v_a_1524_, lean_object* v_fallback_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1524_, v_fallback_1525_, v_x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1528_, lean_object* v_a_1529_, lean_object* v_fallback_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1528_, v_a_1529_, v_fallback_1530_, v_x_1531_);
lean_dec(v_x_1531_);
lean_dec(v_fallback_1530_);
lean_dec(v_a_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1533_, lean_object* v_a_1534_, lean_object* v_x_1535_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1534_, v_x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1537_, lean_object* v_a_1538_, lean_object* v_x_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1537_, v_a_1538_, v_x_1539_);
lean_dec(v_x_1539_);
lean_dec(v_a_1538_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1542_, lean_object* v_data_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1545_, lean_object* v_a_1546_, lean_object* v_b_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1546_, v_b_1547_, v_x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v_n_1552_, lean_object* v_lo_1553_, lean_object* v_hi_1554_, lean_object* v_hhi_1555_, lean_object* v_pivot_1556_, lean_object* v_as_1557_, lean_object* v_i_1558_, lean_object* v_k_1559_, lean_object* v_ilo_1560_, lean_object* v_ik_1561_, lean_object* v_w_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1550_, v___x_1551_, v_hi_1554_, v_pivot_1556_, v_as_1557_, v_i_1558_, v_k_1559_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1564_, lean_object* v___x_1565_, lean_object* v_n_1566_, lean_object* v_lo_1567_, lean_object* v_hi_1568_, lean_object* v_hhi_1569_, lean_object* v_pivot_1570_, lean_object* v_as_1571_, lean_object* v_i_1572_, lean_object* v_k_1573_, lean_object* v_ilo_1574_, lean_object* v_ik_1575_, lean_object* v_w_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1564_, v___x_1565_, v_n_1566_, v_lo_1567_, v_hi_1568_, v_hhi_1569_, v_pivot_1570_, v_as_1571_, v_i_1572_, v_k_1573_, v_ilo_1574_, v_ik_1575_, v_w_1576_);
lean_dec(v_hi_1568_);
lean_dec(v_lo_1567_);
lean_dec(v_n_1566_);
lean_dec(v___x_1565_);
lean_dec(v___x_1564_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1578_, lean_object* v_lo_1579_, lean_object* v_hi_1580_, lean_object* v_hhi_1581_, lean_object* v_pivot_1582_, lean_object* v_as_1583_, lean_object* v_i_1584_, lean_object* v_k_1585_, lean_object* v_ilo_1586_, lean_object* v_ik_1587_, lean_object* v_w_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1580_, v_pivot_1582_, v_as_1583_, v_i_1584_, v_k_1585_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1590_, lean_object* v_lo_1591_, lean_object* v_hi_1592_, lean_object* v_hhi_1593_, lean_object* v_pivot_1594_, lean_object* v_as_1595_, lean_object* v_i_1596_, lean_object* v_k_1597_, lean_object* v_ilo_1598_, lean_object* v_ik_1599_, lean_object* v_w_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1590_, v_lo_1591_, v_hi_1592_, v_hhi_1593_, v_pivot_1594_, v_as_1595_, v_i_1596_, v_k_1597_, v_ilo_1598_, v_ik_1599_, v_w_1600_);
lean_dec_ref(v_pivot_1594_);
lean_dec(v_hi_1592_);
lean_dec(v_lo_1591_);
lean_dec(v_n_1590_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1602_, lean_object* v_i_1603_, lean_object* v_source_1604_, lean_object* v_target_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1603_, v_source_1604_, v_target_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1607_, lean_object* v_i_1608_, lean_object* v_source_1609_, lean_object* v_target_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1608_, v_source_1609_, v_target_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1617_, v_x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v_env_1624_; lean_object* v___x_1625_; lean_object* v_env_1626_; lean_object* v___x_1627_; lean_object* v_toEnvExtension_1628_; lean_object* v_asyncMode_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; 
v___x_1623_ = lean_st_ref_get(v___y_1621_);
v_env_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc_ref(v_env_1624_);
lean_dec(v___x_1623_);
v___x_1625_ = lean_st_ref_get(v___y_1621_);
v_env_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_ref(v_env_1626_);
lean_dec(v___x_1625_);
v___x_1627_ = l_Lean_declRangeExt;
v_toEnvExtension_1628_ = lean_ctor_get(v___x_1627_, 0);
v_asyncMode_1629_ = lean_ctor_get(v_toEnvExtension_1628_, 2);
v___x_1630_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1631_ = 0;
lean_inc(v_declName_1620_);
v___x_1632_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1630_, v___x_1627_, v_env_1624_, v_declName_1620_, v_asyncMode_1629_, v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = 1;
v___x_1634_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1630_, v___x_1627_, v_env_1626_, v_declName_1620_, v_asyncMode_1629_, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; 
lean_dec_ref(v_env_1626_);
lean_dec(v_declName_1620_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1637_, v___y_1638_);
lean_dec(v___y_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v_env_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1644_ = lean_st_ref_get(v___y_1642_);
v_env_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc_ref(v_env_1645_);
lean_dec(v___x_1644_);
v___x_1646_ = l_Lean_isRecCore(v_env_1645_, v_declName_1641_);
v___x_1647_ = lean_box(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1649_, v___y_1650_);
lean_dec(v___y_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_ranges_1658_; lean_object* v___x_1664_; lean_object* v_env_1665_; lean_object* v___x_1666_; lean_object* v_a_1667_; uint8_t v___y_1673_; uint8_t v___x_1677_; 
v___x_1664_ = lean_st_ref_get(v___y_1655_);
v_env_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref_n(v_env_1665_, 2);
lean_dec(v___x_1664_);
lean_inc_n(v_declName_1653_, 2);
v___x_1666_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1653_, v___y_1655_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
v___x_1677_ = l_Lean_isAuxRecursor(v_env_1665_, v_declName_1653_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; 
lean_inc(v_declName_1653_);
v___x_1678_ = l_Lean_isNoConfusion(v_env_1665_, v_declName_1653_);
v___y_1673_ = v___x_1678_;
goto v___jp_1672_;
}
else
{
lean_dec_ref(v_env_1665_);
v___y_1673_ = v___x_1677_;
goto v___jp_1672_;
}
v___jp_1657_:
{
if (lean_obj_tag(v_ranges_1658_) == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = l_Lean_builtinDeclRanges;
v___x_1660_ = lean_st_ref_get(v___x_1659_);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1660_, v_declName_1653_);
lean_dec(v_declName_1653_);
lean_dec(v___x_1660_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; 
lean_dec(v_declName_1653_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_ranges_1658_);
return v___x_1663_;
}
}
v___jp_1668_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_a_1671_; 
v___x_1669_ = l_Lean_Name_getPrefix(v_declName_1653_);
v___x_1670_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1669_, v___y_1655_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
v_ranges_1658_ = v_a_1671_;
goto v___jp_1657_;
}
v___jp_1672_:
{
if (v___y_1673_ == 0)
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_unbox(v_a_1667_);
lean_dec(v_a_1667_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v_a_1676_; 
lean_inc(v_declName_1653_);
v___x_1675_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1653_, v___y_1655_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
v_ranges_1658_ = v_a_1676_;
goto v___jp_1657_;
}
else
{
goto v___jp_1668_;
}
}
else
{
lean_dec(v_a_1667_);
goto v___jp_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1684_, lean_object* v_site_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
if (lean_obj_tag(v_site_1685_) == 0)
{
lean_object* v_name_1689_; lean_object* v___x_1690_; 
v_name_1689_ = lean_ctor_get(v_site_1685_, 0);
lean_inc(v_name_1689_);
lean_dec_ref_known(v_site_1685_, 1);
v___x_1690_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1689_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1712_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1712_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1712_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
if (lean_obj_tag(v_a_1691_) == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(0);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1711_; 
v_val_1699_ = lean_ctor_get(v_a_1691_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1701_ = v_a_1691_;
v_isShared_1702_ = v_isSharedCheck_1711_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_val_1699_);
lean_dec(v_a_1691_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1711_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_range_1703_; lean_object* v_pos_1704_; lean_object* v___x_1706_; 
v_range_1703_ = lean_ctor_get(v_val_1699_, 0);
lean_inc_ref(v_range_1703_);
lean_dec(v_val_1699_);
v_pos_1704_ = lean_ctor_get(v_range_1703_, 0);
lean_inc_ref(v_pos_1704_);
lean_dec_ref(v_range_1703_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v_pos_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_pos_1704_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1706_);
v___x_1708_ = v___x_1693_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1690_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1690_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_n_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1752_; 
v_n_1721_ = lean_ctor_get(v_site_1685_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_site_1685_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1723_ = v_site_1685_;
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_n_1721_);
lean_dec(v_site_1685_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_st_ref_get(v_a_1687_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_ref(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1727_ = l_Lean_getVersoModuleDoc_x3f(v_env_1726_, v_failMod_1684_);
lean_dec_ref(v_env_1726_);
if (lean_obj_tag(v___x_1727_) == 1)
{
lean_object* v_val_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1747_; 
v_val_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_val_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_array_get_size(v_val_1728_);
v___x_1733_ = lean_nat_dec_lt(v_n_1721_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_del_object(v___x_1730_);
lean_dec(v_val_1728_);
lean_dec(v_n_1721_);
v___x_1734_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1734_);
v___x_1736_ = v___x_1723_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v_declarationRange_1739_; lean_object* v_pos_1740_; lean_object* v___x_1742_; 
v___x_1738_ = lean_array_fget(v_val_1728_, v_n_1721_);
lean_dec(v_n_1721_);
lean_dec(v_val_1728_);
v_declarationRange_1739_ = lean_ctor_get(v___x_1738_, 2);
lean_inc_ref(v_declarationRange_1739_);
lean_dec(v___x_1738_);
v_pos_1740_ = lean_ctor_get(v_declarationRange_1739_, 0);
lean_inc_ref(v_pos_1740_);
lean_dec_ref(v_declarationRange_1739_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_pos_1740_);
v___x_1742_ = v___x_1730_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_pos_1740_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1742_);
v___x_1744_ = v___x_1723_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_dec(v___x_1727_);
lean_dec(v_n_1721_);
v___x_1748_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1748_);
v___x_1750_ = v___x_1723_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1753_, lean_object* v_site_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1753_, v_site_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_failMod_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1759_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1769_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v_name_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_name_1783_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_name_1783_);
lean_dec_ref_known(v_x_1782_, 1);
v___x_1784_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1785_ = 1;
v___x_1786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1783_, v___x_1785_);
v___x_1787_ = lean_string_append(v___x_1784_, v___x_1786_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v_n_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_n_1790_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_n_1790_);
lean_dec_ref_known(v_x_1782_, 1);
v___x_1791_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_n_1790_, v___x_1792_);
lean_dec(v_n_1790_);
v___x_1794_ = l_Nat_reprFast(v___x_1793_);
v___x_1795_ = lean_string_append(v___x_1791_, v___x_1794_);
lean_dec_ref(v___x_1794_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_env_1800_; lean_object* v___x_1801_; lean_object* v_toEnvExtension_1802_; lean_object* v_asyncMode_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_merged_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v___x_1799_ = lean_st_ref_get(v___y_1797_);
v_env_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_ref(v_env_1800_);
lean_dec(v___x_1799_);
v___x_1801_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1802_ = lean_ctor_get(v___x_1801_, 0);
v_asyncMode_1803_ = lean_ctor_get(v_toEnvExtension_1802_, 2);
v___x_1804_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1805_ = lean_box(0);
v___x_1806_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1804_, v___x_1801_, v_env_1800_, v_asyncMode_1803_, v___x_1805_);
v_merged_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v___x_1806_, 1);
lean_dec(v_unused_1816_);
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_merged_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v_merged_1807_);
lean_ctor_set(v___x_1809_, 0, v_o_1796_);
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_o_1796_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_merged_1807_);
v___x_1812_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1817_, v___y_1818_);
lean_dec(v___y_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1821_, v___y_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1831_, lean_object* v_opt_1832_){
_start:
{
lean_object* v_name_1833_; lean_object* v_defValue_1834_; lean_object* v_map_1835_; lean_object* v___x_1836_; 
v_name_1833_ = lean_ctor_get(v_opt_1832_, 0);
v_defValue_1834_ = lean_ctor_get(v_opt_1832_, 1);
v_map_1835_ = lean_ctor_get(v_opts_1831_, 0);
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1835_, v_name_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_unbox(v_defValue_1834_);
return v___x_1837_;
}
else
{
lean_object* v_val_1838_; 
v_val_1838_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1836_, 1);
if (lean_obj_tag(v_val_1838_) == 1)
{
uint8_t v_v_1839_; 
v_v_1839_ = lean_ctor_get_uint8(v_val_1838_, 0);
lean_dec_ref_known(v_val_1838_, 0);
return v_v_1839_;
}
else
{
uint8_t v___x_1840_; 
lean_dec(v_val_1838_);
v___x_1840_ = lean_unbox(v_defValue_1834_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1841_, lean_object* v_opt_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1841_, v_opt_1842_);
lean_dec_ref(v_opt_1842_);
lean_dec_ref(v_opts_1841_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1845_, lean_object* v_opt_1846_){
_start:
{
lean_object* v_name_1847_; lean_object* v_defValue_1848_; lean_object* v_map_1849_; lean_object* v___x_1850_; 
v_name_1847_ = lean_ctor_get(v_opt_1846_, 0);
v_defValue_1848_ = lean_ctor_get(v_opt_1846_, 1);
v_map_1849_ = lean_ctor_get(v_opts_1845_, 0);
v___x_1850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1849_, v_name_1847_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_inc(v_defValue_1848_);
return v_defValue_1848_;
}
else
{
lean_object* v_val_1851_; 
v_val_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v___x_1850_, 1);
if (lean_obj_tag(v_val_1851_) == 3)
{
lean_object* v_v_1852_; 
v_v_1852_ = lean_ctor_get(v_val_1851_, 0);
lean_inc(v_v_1852_);
lean_dec_ref_known(v_val_1851_, 1);
return v_v_1852_;
}
else
{
lean_dec(v_val_1851_);
lean_inc(v_defValue_1848_);
return v_defValue_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1853_, lean_object* v_opt_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1853_, v_opt_1854_);
lean_dec_ref(v_opt_1854_);
lean_dec_ref(v_opts_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_options_1860_; lean_object* v___x_1861_; lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
v_options_1860_ = lean_ctor_get(v_c_1856_, 6);
lean_inc_ref(v_options_1860_);
lean_dec_ref(v_c_1856_);
v___x_1861_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1860_, v___y_1858_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1866_ = l_Lean_linter_doc_deferred;
v___x_1867_ = l_Lean_Linter_getLinterValue(v___x_1866_, v_a_1862_);
lean_dec(v_a_1862_);
v___x_1868_ = lean_box(v___x_1867_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1868_);
v___x_1870_ = v___x_1864_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1878_, lean_object* v_docCheckedModules_1879_, uint8_t v___y_1880_, lean_object* v_m_1881_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1878_, v_m_1881_);
if (v___x_1882_ == 0)
{
return v___x_1882_;
}
else
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_NameSet_contains(v_docCheckedModules_1879_, v_m_1881_);
if (v___x_1883_ == 0)
{
return v___y_1880_;
}
else
{
uint8_t v___x_1884_; 
v___x_1884_ = 0;
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1885_, lean_object* v_docCheckedModules_1886_, lean_object* v___y_1887_, lean_object* v_m_1888_){
_start:
{
uint8_t v___y_7017__boxed_1889_; uint8_t v_res_1890_; lean_object* v_r_1891_; 
v___y_7017__boxed_1889_ = lean_unbox(v___y_1887_);
v_res_1890_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1885_, v_docCheckedModules_1886_, v___y_7017__boxed_1889_, v_m_1888_);
lean_dec(v_m_1888_);
lean_dec(v_docCheckedModules_1886_);
lean_dec(v_pkgRoot_1885_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_1899_, lean_object* v_sp_1900_, lean_object* v_as_1901_, size_t v_sz_1902_, size_t v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_a_1909_; uint8_t v_unlocated_1913_; 
v_unlocated_1913_ = lean_usize_dec_lt(v_i_1903_, v_sz_1902_);
if (v_unlocated_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_sp_1900_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_b_1904_);
return v___x_1914_;
}
else
{
lean_object* v_a_1915_; lean_object* v_snd_1916_; lean_object* v_fst_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_2046_; 
v_a_1915_ = lean_array_uget_borrowed(v_as_1901_, v_i_1903_);
v_snd_1916_ = lean_ctor_get(v_a_1915_, 1);
lean_inc(v_snd_1916_);
v_fst_1917_ = lean_ctor_get(v_snd_1916_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_snd_1916_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_snd_1916_, 1);
lean_dec(v_unused_2047_);
v___x_1919_ = v_snd_1916_;
v_isShared_1920_ = v_isSharedCheck_2046_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_fst_1917_);
lean_dec(v_snd_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_2046_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_fst_1921_; lean_object* v_site_1922_; lean_object* v___x_1923_; 
v_fst_1921_ = lean_ctor_get(v_a_1915_, 0);
v_site_1922_ = lean_ctor_get(v_fst_1917_, 0);
lean_inc_ref_n(v_site_1922_, 2);
lean_dec(v_fst_1917_);
v___x_1923_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_1921_, v_site_1922_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
if (lean_obj_tag(v_a_1924_) == 0)
{
lean_object* v_fst_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1964_; 
v_fst_1925_ = lean_ctor_get(v_b_1904_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_b_1904_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_b_1904_, 1);
lean_dec(v_unused_1965_);
v___x_1927_ = v_b_1904_;
v_isShared_1928_ = v_isSharedCheck_1964_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_fst_1925_);
lean_dec(v_b_1904_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1964_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v_name_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1929_ = l_Lean_linter_doc_deferred;
v_name_1930_ = lean_ctor_get(v___x_1929_, 0);
v___x_1931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_1932_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_1922_);
v___x_1933_ = lean_string_append(v___x_1931_, v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_1935_ = lean_string_append(v___x_1933_, v___x_1934_);
lean_inc(v_fst_1921_);
v___x_1936_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1921_, v___x_1899_);
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_1939_ = lean_string_append(v___x_1937_, v___x_1938_);
lean_inc(v_name_1930_);
v___x_1940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1930_, v___x_1899_);
v___x_1941_ = lean_string_append(v___x_1939_, v___x_1940_);
lean_dec_ref(v___x_1940_);
v___x_1942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1943_ = lean_string_append(v___x_1941_, v___x_1942_);
v___x_1944_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec_ref_known(v___x_1944_, 1);
lean_del_object(v___x_1919_);
v___x_1945_ = lean_box(v_unlocated_1913_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1945_);
v___x_1947_ = v___x_1927_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_fst_1925_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v_a_1909_ = v___x_1947_;
goto v___jp_1908_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1927_);
lean_dec(v_fst_1925_);
lean_dec(v_sp_1900_);
v_a_1949_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1951_ = v___x_1944_;
v_isShared_1952_ = v_isSharedCheck_1963_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1944_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1963_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_ref_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v_ref_1953_ = lean_ctor_get(v___y_1905_, 5);
v___x_1954_ = lean_io_error_to_string(v_a_1949_);
v___x_1955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___x_1956_ = l_Lean_MessageData_ofFormat(v___x_1955_);
lean_inc(v_ref_1953_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1956_);
lean_ctor_set(v___x_1919_, 0, v_ref_1953_);
v___x_1958_ = v___x_1919_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_ref_1953_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1958_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_site_1922_);
v_fst_1966_ = lean_ctor_get(v_b_1904_, 0);
v_snd_1967_ = lean_ctor_get(v_b_1904_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_b_1904_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1969_ = v_b_1904_;
v_isShared_1970_ = v_isSharedCheck_2037_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v_b_1904_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2037_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_val_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2036_; 
v_val_1971_ = lean_ctor_get(v_a_1924_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_1924_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1973_ = v_a_1924_;
v_isShared_1974_ = v_isSharedCheck_2036_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_val_1971_);
lean_dec(v_a_1924_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2036_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_1921_);
lean_inc(v_sp_1900_);
v___x_1976_ = l_Lean_SearchPath_findWithExt(v_sp_1900_, v___x_1975_, v_fst_1921_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v___x_1978_; lean_object* v_name_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec(v_val_1971_);
lean_dec(v_snd_1967_);
v___x_1978_ = l_Lean_linter_doc_deferred;
v_name_1979_ = lean_ctor_get(v___x_1978_, 0);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_1921_);
v___x_1981_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1921_, v___x_1899_);
v___x_1982_ = lean_string_append(v___x_1980_, v___x_1981_);
lean_dec_ref(v___x_1981_);
v___x_1983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_1984_ = lean_string_append(v___x_1982_, v___x_1983_);
lean_inc(v_name_1979_);
v___x_1985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1979_, v___x_1899_);
v___x_1986_ = lean_string_append(v___x_1984_, v___x_1985_);
lean_dec_ref(v___x_1985_);
v___x_1987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_1988_ = lean_string_append(v___x_1986_, v___x_1987_);
v___x_1989_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec_ref_known(v___x_1989_, 1);
lean_del_object(v___x_1973_);
lean_del_object(v___x_1919_);
v___x_1990_ = lean_box(v_unlocated_1913_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v___x_1990_);
v___x_1992_ = v___x_1969_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_a_1909_ = v___x_1992_;
goto v___jp_1908_;
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1969_);
lean_dec(v_fst_1966_);
lean_dec(v_sp_1900_);
v_a_1994_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1996_ = v___x_1989_;
v_isShared_1997_ = v_isSharedCheck_2010_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1989_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2010_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_ref_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_ref_1998_ = lean_ctor_get(v___y_1905_, 5);
v___x_1999_ = lean_io_error_to_string(v_a_1994_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 3);
lean_ctor_set(v___x_1973_, 0, v___x_1999_);
v___x_2001_ = v___x_1973_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = l_Lean_MessageData_ofFormat(v___x_2001_);
lean_inc(v_ref_1998_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_2002_);
lean_ctor_set(v___x_1919_, 0, v_ref_1998_);
v___x_2004_ = v___x_1919_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_ref_1998_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2004_);
v___x_2006_ = v___x_1996_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2012_; lean_object* v_name_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_del_object(v___x_1973_);
lean_del_object(v___x_1919_);
v_val_2011_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v_a_1977_, 1);
v___x_2012_ = l_Lean_linter_doc_deferred;
v_name_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_name_2013_);
v___x_2014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2014_, 0, v_val_2011_);
lean_ctor_set(v___x_2014_, 1, v_val_1971_);
lean_ctor_set(v___x_2014_, 2, v_name_2013_);
v___x_2015_ = lean_array_push(v_fst_1966_, v___x_2014_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2015_);
v___x_2017_ = v___x_1969_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_snd_1967_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v_a_1909_ = v___x_2017_;
goto v___jp_1908_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_val_1971_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_dec(v_sp_1900_);
v_a_2019_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2021_ = v___x_1976_;
v_isShared_2022_ = v_isSharedCheck_2035_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1976_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2035_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v_ref_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v_ref_2023_ = lean_ctor_get(v___y_1905_, 5);
v___x_2024_ = lean_io_error_to_string(v_a_2019_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 3);
lean_ctor_set(v___x_1973_, 0, v___x_2024_);
v___x_2026_ = v___x_1973_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = l_Lean_MessageData_ofFormat(v___x_2026_);
lean_inc(v_ref_2023_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_2027_);
lean_ctor_set(v___x_1919_, 0, v_ref_2023_);
v___x_2029_ = v___x_1919_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_ref_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2029_);
v___x_2031_ = v___x_2021_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
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
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_site_1922_);
lean_del_object(v___x_1919_);
lean_dec_ref(v_b_1904_);
lean_dec(v_sp_1900_);
v_a_2038_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1923_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1923_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
v___jp_1908_:
{
size_t v___x_1910_; size_t v___x_1911_; 
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1903_, v___x_1910_);
v_i_1903_ = v___x_1911_;
v_b_1904_ = v_a_1909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2048_, lean_object* v_sp_2049_, lean_object* v_as_2050_, lean_object* v_sz_2051_, lean_object* v_i_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v___x_7041__boxed_2057_; size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v___x_7041__boxed_2057_ = lean_unbox(v___x_2048_);
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2051_);
lean_dec(v_sz_2051_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_7041__boxed_2057_, v_sp_2049_, v_as_2050_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_as_2050_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_2067_, uint8_t v___y_2068_, lean_object* v_as_2069_, size_t v_sz_2070_, size_t v_i_2071_, lean_object* v_b_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_a_2076_; uint8_t v___x_2080_; 
v___x_2080_ = lean_usize_dec_lt(v_i_2071_, v_sz_2070_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_sp_2067_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_b_2072_);
return v___x_2081_;
}
else
{
lean_object* v_a_2082_; lean_object* v_snd_2083_; lean_object* v_fst_2084_; lean_object* v_fst_2085_; lean_object* v_snd_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2181_; 
v_a_2082_ = lean_array_uget_borrowed(v_as_2069_, v_i_2071_);
v_snd_2083_ = lean_ctor_get(v_a_2082_, 1);
lean_inc(v_snd_2083_);
v_fst_2084_ = lean_ctor_get(v_snd_2083_, 0);
lean_inc(v_fst_2084_);
v_fst_2085_ = lean_ctor_get(v_a_2082_, 0);
v_snd_2086_ = lean_ctor_get(v_snd_2083_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_snd_2083_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_snd_2083_, 0);
lean_dec(v_unused_2182_);
v___x_2088_ = v_snd_2083_;
v_isShared_2089_ = v_isSharedCheck_2181_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snd_2086_);
lean_dec(v_snd_2083_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2181_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_site_2090_; lean_object* v_sourceString_2091_; lean_object* v___x_2092_; lean_object* v___y_2094_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_site_2090_ = lean_ctor_get(v_fst_2084_, 0);
lean_inc_ref(v_site_2090_);
v_sourceString_2091_ = lean_ctor_get(v_fst_2084_, 2);
lean_inc_ref(v_sourceString_2091_);
lean_dec(v_fst_2084_);
v___x_2092_ = lean_box(0);
v___x_2173_ = lean_string_utf8_byte_size(v_sourceString_2091_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_nat_dec_eq(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2177_ = lean_string_append(v___x_2176_, v_sourceString_2091_);
lean_dec_ref(v_sourceString_2091_);
v___x_2178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2179_ = lean_string_append(v___x_2177_, v___x_2178_);
v___y_2094_ = v___x_2179_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2180_; 
lean_dec_ref(v_sourceString_2091_);
v___x_2180_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2094_ = v___x_2180_;
goto v___jp_2093_;
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2085_);
lean_inc(v_sp_2067_);
v___x_2096_ = l_Lean_SearchPath_findWithExt(v_sp_2067_, v___x_2095_, v_fst_2085_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
if (lean_obj_tag(v_a_2097_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2098_ = l_Lean_MessageData_toString(v_snd_2086_);
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2085_);
v___x_2100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2085_, v___y_2068_);
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_2103_ = lean_string_append(v___x_2101_, v___x_2102_);
v___x_2104_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2090_);
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = lean_string_append(v___x_2105_, v___y_2094_);
lean_dec_ref(v___y_2094_);
v___x_2107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2108_ = lean_string_append(v___x_2106_, v___x_2107_);
v___x_2109_ = lean_string_append(v___x_2108_, v___x_2098_);
lean_dec_ref(v___x_2098_);
v___x_2110_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2109_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref_known(v___x_2110_, 1);
lean_del_object(v___x_2088_);
v_a_2076_ = v___x_2092_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_sp_2067_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_ref_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v_ref_2115_ = lean_ctor_get(v___y_2073_, 5);
v___x_2116_ = lean_io_error_to_string(v_a_2111_);
v___x_2117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = l_Lean_MessageData_ofFormat(v___x_2117_);
lean_inc(v_ref_2115_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2118_);
lean_ctor_set(v___x_2088_, 0, v_ref_2115_);
v___x_2120_ = v___x_2088_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_ref_2115_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2120_);
v___x_2122_ = v___x_2113_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_val_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2157_; 
v_val_2126_ = lean_ctor_get(v_a_2097_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2128_ = v_a_2097_;
v_isShared_2129_ = v_isSharedCheck_2157_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_val_2126_);
lean_dec(v_a_2097_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2157_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2130_ = l_Lean_MessageData_toString(v_snd_2086_);
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2132_ = lean_string_append(v_val_2126_, v___x_2131_);
v___x_2133_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2090_);
v___x_2134_ = lean_string_append(v___x_2132_, v___x_2133_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = lean_string_append(v___x_2134_, v___y_2094_);
lean_dec_ref(v___y_2094_);
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2137_ = lean_string_append(v___x_2135_, v___x_2136_);
v___x_2138_ = lean_string_append(v___x_2137_, v___x_2130_);
lean_dec_ref(v___x_2130_);
v___x_2139_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_dec_ref_known(v___x_2139_, 1);
lean_del_object(v___x_2128_);
lean_del_object(v___x_2088_);
v_a_2076_ = v___x_2092_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_sp_2067_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2156_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2156_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_ref_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v_ref_2144_ = lean_ctor_get(v___y_2073_, 5);
v___x_2145_ = lean_io_error_to_string(v_a_2140_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 3);
lean_ctor_set(v___x_2128_, 0, v___x_2145_);
v___x_2147_ = v___x_2128_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_MessageData_ofFormat(v___x_2147_);
lean_inc(v_ref_2144_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2148_);
lean_ctor_set(v___x_2088_, 0, v_ref_2144_);
v___x_2150_ = v___x_2088_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_ref_2144_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2150_);
v___x_2152_ = v___x_2142_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
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
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___y_2094_);
lean_dec_ref(v_site_2090_);
lean_dec(v_snd_2086_);
lean_dec(v_sp_2067_);
v_a_2158_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2160_ = v___x_2096_;
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2096_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_ref_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_ref_2162_ = lean_ctor_get(v___y_2073_, 5);
v___x_2163_ = lean_io_error_to_string(v_a_2158_);
v___x_2164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
v___x_2165_ = l_Lean_MessageData_ofFormat(v___x_2164_);
lean_inc(v_ref_2162_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2165_);
lean_ctor_set(v___x_2088_, 0, v_ref_2162_);
v___x_2167_ = v___x_2088_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_ref_2162_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2167_);
v___x_2169_ = v___x_2160_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
v___jp_2075_:
{
size_t v___x_2077_; size_t v___x_2078_; 
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_add(v_i_2071_, v___x_2077_);
v_i_2071_ = v___x_2078_;
v_b_2072_ = v_a_2076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2183_, lean_object* v___y_2184_, lean_object* v_as_2185_, lean_object* v_sz_2186_, lean_object* v_i_2187_, lean_object* v_b_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___y_7333__boxed_2191_; size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v___y_7333__boxed_2191_ = lean_unbox(v___y_2184_);
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2186_);
lean_dec(v_sz_2186_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2183_, v___y_7333__boxed_2191_, v_as_2185_, v_sz_boxed_2192_, v_i_boxed_2193_, v_b_2188_, v___y_2189_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v_as_2185_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2195_, lean_object* v_as_2196_, size_t v_sz_2197_, size_t v_i_2198_, lean_object* v_b_2199_){
_start:
{
lean_object* v_a_2202_; uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_lt(v_i_2198_, v_sz_2197_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_b_2199_);
return v___x_2207_;
}
else
{
lean_object* v_a_2208_; uint8_t v___x_2209_; 
v_a_2208_ = lean_array_uget_borrowed(v_as_2196_, v_i_2198_);
v___x_2209_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2195_, v_a_2208_);
if (v___x_2209_ == 0)
{
v_a_2202_ = v_b_2199_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2210_; 
lean_inc(v_a_2208_);
v___x_2210_ = l_Lean_NameSet_insert(v_b_2199_, v_a_2208_);
v_a_2202_ = v___x_2210_;
goto v___jp_2201_;
}
}
v___jp_2201_:
{
size_t v___x_2203_; size_t v___x_2204_; 
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2198_, v___x_2203_);
v_i_2198_ = v___x_2204_;
v_b_2199_ = v_a_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2211_, lean_object* v_as_2212_, lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_){
_start:
{
size_t v_sz_boxed_2217_; size_t v_i_boxed_2218_; lean_object* v_res_2219_; 
v_sz_boxed_2217_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2211_, v_as_2212_, v_sz_boxed_2217_, v_i_boxed_2218_, v_b_2215_);
lean_dec_ref(v_as_2212_);
lean_dec(v_pkgRoot_2211_);
return v_res_2219_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_unsigned_to_nat(32u);
v___x_2227_ = lean_mk_empty_array_with_capacity(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2229_ = ((size_t)5ULL);
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = lean_unsigned_to_nat(32u);
v___x_2232_ = lean_mk_empty_array_with_capacity(v___x_2231_);
v___x_2233_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2234_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
lean_ctor_set(v___x_2234_, 2, v___x_2230_);
lean_ctor_set(v___x_2234_, 3, v___x_2230_);
lean_ctor_set_usize(v___x_2234_, 4, v___x_2229_);
return v___x_2234_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2235_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = l_Lean_NameSet_empty;
v___x_2241_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
lean_ctor_set(v___x_2242_, 2, v___x_2240_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = l_Lean_firstFrontendMacroScope;
v___x_2245_ = lean_nat_add(v___x_2244_, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2256_; uint64_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2257_ = 0ULL;
v___x_2258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set_uint64(v___x_2258_, sizeof(void*)*1, v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v_unlocated_2261_; lean_object* v___x_2262_; 
v___x_2259_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2260_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2261_ = 1;
v___x_2262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2260_);
lean_ctor_set(v___x_2262_, 2, v___x_2259_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*3, v_unlocated_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = l_Lean_Options_empty;
v___x_2266_ = l_Lean_Core_getMaxHeartbeats(v___x_2265_);
return v___x_2266_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2267_ = l_Lean_diagnostics;
v___x_2268_ = l_Lean_Options_empty;
v___x_2269_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2270_, lean_object* v_linterOpts_2271_, lean_object* v_sp_2272_, lean_object* v_env_2273_, lean_object* v_pkgRoot_2274_, lean_object* v_docCheckedModules_2275_){
_start:
{
lean_object* v___y_2278_; lean_object* v_a_2279_; lean_object* v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2308_; lean_object* v_a_2312_; uint8_t v___y_2316_; lean_object* v_a_2317_; uint8_t v_lintOnly_2333_; uint8_t v_mode_2334_; lean_object* v___f_2335_; lean_object* v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; uint8_t v___y_2343_; lean_object* v_fileName_2344_; lean_object* v_fileMap_2345_; lean_object* v_currRecDepth_2346_; lean_object* v_ref_2347_; lean_object* v_currNamespace_2348_; lean_object* v_openDecls_2349_; lean_object* v_initHeartbeats_2350_; lean_object* v_maxHeartbeats_2351_; lean_object* v_quotContext_2352_; lean_object* v_currMacroScope_2353_; lean_object* v_cancelTk_x3f_2354_; uint8_t v_suppressElabErrors_2355_; lean_object* v_inheritedTraceOptions_2356_; lean_object* v___y_2357_; lean_object* v___y_2386_; lean_object* v___y_2387_; uint8_t v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2391_; uint8_t v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2409_; lean_object* v___y_2410_; uint8_t v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; uint8_t v___y_2417_; uint8_t v___y_2418_; uint8_t v___y_2439_; 
v_lintOnly_2333_ = lean_ctor_get_uint8(v_args_2270_, sizeof(void*)*4);
v_mode_2334_ = lean_ctor_get_uint8(v_args_2270_, sizeof(void*)*4 + 1);
v___f_2335_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2333_ == 0)
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = l_Lean_linter_doc_deferred;
v___x_2478_ = l_Lean_Linter_getLinterValue(v___x_2477_, v_linterOpts_2271_);
v___y_2439_ = v___x_2478_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2479_; lean_object* v_name_2480_; uint8_t v___x_2481_; 
v___x_2479_ = l_Lean_linter_doc_deferred;
v_name_2480_ = lean_ctor_get(v___x_2479_, 0);
v___x_2481_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2480_, v_linterOpts_2271_);
v___y_2439_ = v___x_2481_;
goto v___jp_2438_;
}
v___jp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; size_t v_sz_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2280_ = lean_st_ref_get(v___y_2278_);
lean_dec(v___y_2278_);
lean_dec(v___x_2280_);
v___x_2281_ = l_Lean_Environment_header(v_env_2273_);
lean_dec_ref(v_env_2273_);
v___x_2282_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2281_);
v_sz_2283_ = lean_array_size(v___x_2282_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2274_, v___x_2282_, v_sz_2283_, v___x_2284_, v_docCheckedModules_2275_);
lean_dec_ref(v___x_2282_);
lean_dec(v_pkgRoot_2274_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_a_2279_);
lean_ctor_set(v___x_2290_, 1, v_a_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2290_);
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_a_2279_);
v_a_2295_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2285_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2285_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
v___jp_2303_:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2306_, 0, v___y_2305_);
v___y_2278_ = v___y_2304_;
v_a_2279_ = v___x_2306_;
goto v___jp_2277_;
}
v___jp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___y_2308_);
lean_ctor_set(v___x_2309_, 1, v_docCheckedModules_2275_);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_mk_io_user_error(v_a_2312_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
v___jp_2315_:
{
if (lean_obj_tag(v_a_2317_) == 0)
{
lean_object* v_msg_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_msg_2318_ = lean_ctor_get(v_a_2317_, 1);
lean_inc_ref(v_msg_2318_);
lean_dec_ref_known(v_a_2317_, 2);
v___x_2319_ = l_Lean_MessageData_toString(v_msg_2318_);
v___x_2320_ = lean_mk_io_user_error(v___x_2319_);
v___x_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v_id_2322_; lean_object* v___x_2323_; 
v_id_2322_ = lean_ctor_get(v_a_2317_, 0);
lean_inc(v_id_2322_);
lean_dec_ref_known(v_a_2317_, 2);
v___x_2323_ = l_Lean_InternalExceptionId_getName(v_id_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_id_2322_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2326_ = l_Lean_Name_toString(v_a_2324_, v___y_2316_);
v___x_2327_ = lean_string_append(v___x_2325_, v___x_2326_);
lean_dec_ref(v___x_2326_);
v_a_2312_ = v___x_2327_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec_ref_known(v___x_2323_, 1);
v___x_2328_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2329_ = l_Nat_reprFast(v_id_2322_);
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v_a_2312_ = v___x_2332_;
goto v___jp_2311_;
}
}
}
v___jp_2336_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = l_Lean_maxRecDepth;
v___x_2359_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2340_, v___x_2358_);
lean_inc_ref(v___y_2340_);
v___x_2360_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2360_, 0, v_fileName_2344_);
lean_ctor_set(v___x_2360_, 1, v_fileMap_2345_);
lean_ctor_set(v___x_2360_, 2, v___y_2340_);
lean_ctor_set(v___x_2360_, 3, v_currRecDepth_2346_);
lean_ctor_set(v___x_2360_, 4, v___x_2359_);
lean_ctor_set(v___x_2360_, 5, v_ref_2347_);
lean_ctor_set(v___x_2360_, 6, v_currNamespace_2348_);
lean_ctor_set(v___x_2360_, 7, v_openDecls_2349_);
lean_ctor_set(v___x_2360_, 8, v_initHeartbeats_2350_);
lean_ctor_set(v___x_2360_, 9, v_maxHeartbeats_2351_);
lean_ctor_set(v___x_2360_, 10, v_quotContext_2352_);
lean_ctor_set(v___x_2360_, 11, v_currMacroScope_2353_);
lean_ctor_set(v___x_2360_, 12, v_cancelTk_x3f_2354_);
lean_ctor_set(v___x_2360_, 13, v_inheritedTraceOptions_2356_);
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*14, v___y_2342_);
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*14 + 1, v_suppressElabErrors_2355_);
v___x_2361_ = l_Lean_Doc_DeferredCheck_run(v___y_2338_, v___f_2335_, v___x_2360_, v___y_2357_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; uint8_t v___x_2363_; uint8_t v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = 1;
v___x_2364_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2334_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
lean_dec(v___y_2357_);
v___x_2365_ = lean_box(0);
v_sz_2366_ = lean_array_size(v_a_2362_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2272_, v___y_2343_, v_a_2362_, v_sz_2366_, v___x_2367_, v___x_2365_, v___x_2360_);
lean_dec_ref_known(v___x_2360_, 14);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
lean_dec_ref_known(v___x_2368_, 1);
v___x_2369_ = lean_array_get_size(v_a_2362_);
lean_dec(v_a_2362_);
v___x_2370_ = lean_nat_dec_eq(v___x_2369_, v___y_2337_);
lean_dec(v___y_2337_);
if (v___x_2370_ == 0)
{
v___y_2304_ = v___y_2341_;
v___y_2305_ = v___y_2343_;
goto v___jp_2303_;
}
else
{
v___y_2304_ = v___y_2341_;
v___y_2305_ = v___x_2364_;
goto v___jp_2303_;
}
}
else
{
lean_object* v_a_2371_; 
lean_dec(v_a_2362_);
lean_dec(v___y_2341_);
lean_dec(v___y_2337_);
lean_dec(v_docCheckedModules_2275_);
lean_dec(v_pkgRoot_2274_);
lean_dec_ref(v_env_2273_);
v_a_2371_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2368_, 1);
v___y_2316_ = v___y_2343_;
v_a_2317_ = v_a_2371_;
goto v___jp_2315_;
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; size_t v_sz_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2372_ = lean_mk_empty_array_with_capacity(v___y_2337_);
lean_dec(v___y_2337_);
v___x_2373_ = lean_box(v___y_2339_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v_sz_2375_ = lean_array_size(v_a_2362_);
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2364_, v_sp_2272_, v_a_2362_, v_sz_2375_, v___x_2376_, v___x_2374_, v___x_2360_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref_known(v___x_2360_, 14);
lean_dec(v_a_2362_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v_fst_2379_; lean_object* v_snd_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v_fst_2379_ = lean_ctor_get(v_a_2378_, 0);
lean_inc(v_fst_2379_);
v_snd_2380_ = lean_ctor_get(v_a_2378_, 1);
lean_inc(v_snd_2380_);
lean_dec(v_a_2378_);
v___x_2381_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2381_, 0, v_fst_2379_);
v___x_2382_ = lean_unbox(v_snd_2380_);
lean_dec(v_snd_2380_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2382_);
v___y_2278_ = v___y_2341_;
v_a_2279_ = v___x_2381_;
goto v___jp_2277_;
}
else
{
lean_object* v_a_2383_; 
lean_dec(v___y_2341_);
lean_dec(v_docCheckedModules_2275_);
lean_dec(v_pkgRoot_2274_);
lean_dec_ref(v_env_2273_);
v_a_2383_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2377_, 1);
v___y_2316_ = v___y_2343_;
v_a_2317_ = v_a_2383_;
goto v___jp_2315_;
}
}
}
else
{
lean_object* v_a_2384_; 
lean_dec_ref_known(v___x_2360_, 14);
lean_dec(v___y_2357_);
lean_dec(v___y_2341_);
lean_dec(v___y_2337_);
lean_dec(v_docCheckedModules_2275_);
lean_dec(v_pkgRoot_2274_);
lean_dec_ref(v_env_2273_);
lean_dec(v_sp_2272_);
v_a_2384_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2361_, 1);
v___y_2316_ = v___y_2343_;
v_a_2317_ = v_a_2384_;
goto v___jp_2315_;
}
}
v___jp_2385_:
{
lean_object* v_fileName_2395_; lean_object* v_fileMap_2396_; lean_object* v_currRecDepth_2397_; lean_object* v_ref_2398_; lean_object* v_currNamespace_2399_; lean_object* v_openDecls_2400_; lean_object* v_initHeartbeats_2401_; lean_object* v_maxHeartbeats_2402_; lean_object* v_quotContext_2403_; lean_object* v_currMacroScope_2404_; lean_object* v_cancelTk_x3f_2405_; uint8_t v_suppressElabErrors_2406_; lean_object* v_inheritedTraceOptions_2407_; 
v_fileName_2395_ = lean_ctor_get(v___y_2393_, 0);
lean_inc_ref(v_fileName_2395_);
v_fileMap_2396_ = lean_ctor_get(v___y_2393_, 1);
lean_inc_ref(v_fileMap_2396_);
v_currRecDepth_2397_ = lean_ctor_get(v___y_2393_, 3);
lean_inc(v_currRecDepth_2397_);
v_ref_2398_ = lean_ctor_get(v___y_2393_, 5);
lean_inc(v_ref_2398_);
v_currNamespace_2399_ = lean_ctor_get(v___y_2393_, 6);
lean_inc(v_currNamespace_2399_);
v_openDecls_2400_ = lean_ctor_get(v___y_2393_, 7);
lean_inc(v_openDecls_2400_);
v_initHeartbeats_2401_ = lean_ctor_get(v___y_2393_, 8);
lean_inc(v_initHeartbeats_2401_);
v_maxHeartbeats_2402_ = lean_ctor_get(v___y_2393_, 9);
lean_inc(v_maxHeartbeats_2402_);
v_quotContext_2403_ = lean_ctor_get(v___y_2393_, 10);
lean_inc(v_quotContext_2403_);
v_currMacroScope_2404_ = lean_ctor_get(v___y_2393_, 11);
lean_inc(v_currMacroScope_2404_);
v_cancelTk_x3f_2405_ = lean_ctor_get(v___y_2393_, 12);
lean_inc(v_cancelTk_x3f_2405_);
v_suppressElabErrors_2406_ = lean_ctor_get_uint8(v___y_2393_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2407_ = lean_ctor_get(v___y_2393_, 13);
lean_inc_ref(v_inheritedTraceOptions_2407_);
lean_dec_ref(v___y_2393_);
v___y_2337_ = v___y_2386_;
v___y_2338_ = v___y_2387_;
v___y_2339_ = v___y_2388_;
v___y_2340_ = v___y_2389_;
v___y_2341_ = v___y_2390_;
v___y_2342_ = v___y_2391_;
v___y_2343_ = v___y_2392_;
v_fileName_2344_ = v_fileName_2395_;
v_fileMap_2345_ = v_fileMap_2396_;
v_currRecDepth_2346_ = v_currRecDepth_2397_;
v_ref_2347_ = v_ref_2398_;
v_currNamespace_2348_ = v_currNamespace_2399_;
v_openDecls_2349_ = v_openDecls_2400_;
v_initHeartbeats_2350_ = v_initHeartbeats_2401_;
v_maxHeartbeats_2351_ = v_maxHeartbeats_2402_;
v_quotContext_2352_ = v_quotContext_2403_;
v_currMacroScope_2353_ = v_currMacroScope_2404_;
v_cancelTk_x3f_2354_ = v_cancelTk_x3f_2405_;
v_suppressElabErrors_2355_ = v_suppressElabErrors_2406_;
v_inheritedTraceOptions_2356_ = v_inheritedTraceOptions_2407_;
v___y_2357_ = v___y_2394_;
goto v___jp_2336_;
}
v___jp_2408_:
{
if (v___y_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v_nextMacroScope_2421_; lean_object* v_ngen_2422_; lean_object* v_auxDeclNGen_2423_; lean_object* v_traceState_2424_; lean_object* v_messages_2425_; lean_object* v_infoState_2426_; lean_object* v_snapshotTasks_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2436_; 
v___x_2419_ = lean_st_ref_take(v___y_2414_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2421_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2422_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2423_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2424_ = lean_ctor_get(v___x_2419_, 4);
v_messages_2425_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2426_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2427_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; 
v_unused_2437_ = lean_ctor_get(v___x_2419_, 5);
lean_dec(v_unused_2437_);
v___x_2429_ = v___x_2419_;
v_isShared_2430_ = v_isSharedCheck_2436_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snapshotTasks_2427_);
lean_inc(v_infoState_2426_);
lean_inc(v_messages_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_auxDeclNGen_2423_);
lean_inc(v_ngen_2422_);
lean_inc(v_nextMacroScope_2421_);
lean_inc(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2436_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = l_Lean_Kernel_enableDiag(v_env_2420_, v___y_2413_);
lean_inc_ref(v___y_2416_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v___y_2416_);
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_nextMacroScope_2421_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_ngen_2422_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v_auxDeclNGen_2423_);
lean_ctor_set(v_reuseFailAlloc_2435_, 4, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2435_, 5, v___y_2416_);
lean_ctor_set(v_reuseFailAlloc_2435_, 6, v_messages_2425_);
lean_ctor_set(v_reuseFailAlloc_2435_, 7, v_infoState_2426_);
lean_ctor_set(v_reuseFailAlloc_2435_, 8, v_snapshotTasks_2427_);
v___x_2433_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_st_ref_put(v___y_2414_, v___x_2433_);
lean_inc(v___y_2414_);
v___y_2386_ = v___y_2410_;
v___y_2387_ = v___y_2409_;
v___y_2388_ = v___y_2411_;
v___y_2389_ = v___y_2412_;
v___y_2390_ = v___y_2414_;
v___y_2391_ = v___y_2413_;
v___y_2392_ = v___y_2417_;
v___y_2393_ = v___y_2415_;
v___y_2394_ = v___y_2414_;
goto v___jp_2385_;
}
}
}
else
{
lean_inc(v___y_2414_);
v___y_2386_ = v___y_2410_;
v___y_2387_ = v___y_2409_;
v___y_2388_ = v___y_2411_;
v___y_2389_ = v___y_2412_;
v___y_2390_ = v___y_2414_;
v___y_2391_ = v___y_2413_;
v___y_2392_ = v___y_2417_;
v___y_2393_ = v___y_2415_;
v___y_2394_ = v___y_2414_;
goto v___jp_2385_;
}
}
v___jp_2438_:
{
if (v___y_2439_ == 0)
{
uint8_t v___x_2440_; uint8_t v___x_2441_; 
lean_dec(v_pkgRoot_2274_);
lean_dec_ref(v_env_2273_);
lean_dec(v_sp_2272_);
v___x_2440_ = 1;
v___x_2441_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2334_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2442_, 0, v___x_2441_);
v___y_2308_ = v___x_2442_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2444_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*1, v___y_2439_);
v___y_2308_ = v___x_2444_;
goto v___jp_2307_;
}
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_env_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; uint8_t v___x_2475_; uint8_t v___x_2476_; 
v___x_2445_ = lean_unsigned_to_nat(0u);
v___x_2446_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2447_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2448_ = lean_io_get_num_heartbeats();
v___x_2449_ = l_Lean_firstFrontendMacroScope;
v___x_2450_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2451_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_box(0);
v___x_2454_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2455_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2456_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2457_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2273_);
v___x_2458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2458_, 0, v_env_2273_);
lean_ctor_set(v___x_2458_, 1, v___x_2450_);
lean_ctor_set(v___x_2458_, 2, v___x_2451_);
lean_ctor_set(v___x_2458_, 3, v___x_2454_);
lean_ctor_set(v___x_2458_, 4, v___x_2455_);
lean_ctor_set(v___x_2458_, 5, v___x_2446_);
lean_ctor_set(v___x_2458_, 6, v___x_2447_);
lean_ctor_set(v___x_2458_, 7, v___x_2456_);
lean_ctor_set(v___x_2458_, 8, v___x_2457_);
v___x_2459_ = lean_st_mk_ref(v___x_2458_);
v___x_2460_ = l_Lean_inheritedTraceOptions;
v___x_2461_ = lean_st_ref_get(v___x_2460_);
v___x_2462_ = lean_st_ref_get(v___x_2459_);
v___x_2463_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2464_ = l_Lean_instInhabitedFileMap_default;
v___x_2465_ = l_Lean_Options_empty;
v___x_2466_ = lean_unsigned_to_nat(1000u);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2469_ = 0;
v___x_2470_ = lean_box(0);
lean_inc(v___x_2461_);
lean_inc(v___x_2448_);
v___x_2471_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2471_, 0, v___x_2463_);
lean_ctor_set(v___x_2471_, 1, v___x_2464_);
lean_ctor_set(v___x_2471_, 2, v___x_2465_);
lean_ctor_set(v___x_2471_, 3, v___x_2445_);
lean_ctor_set(v___x_2471_, 4, v___x_2466_);
lean_ctor_set(v___x_2471_, 5, v___x_2467_);
lean_ctor_set(v___x_2471_, 6, v___x_2452_);
lean_ctor_set(v___x_2471_, 7, v___x_2453_);
lean_ctor_set(v___x_2471_, 8, v___x_2448_);
lean_ctor_set(v___x_2471_, 9, v___x_2468_);
lean_ctor_set(v___x_2471_, 10, v___x_2452_);
lean_ctor_set(v___x_2471_, 11, v___x_2449_);
lean_ctor_set(v___x_2471_, 12, v___x_2470_);
lean_ctor_set(v___x_2471_, 13, v___x_2461_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*14, v___x_2469_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*14 + 1, v___x_2469_);
v_env_2472_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_ref(v_env_2472_);
lean_dec(v___x_2462_);
v___x_2473_ = lean_box(v___y_2439_);
lean_inc(v_docCheckedModules_2275_);
lean_inc(v_pkgRoot_2274_);
v___f_2474_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2474_, 0, v_pkgRoot_2274_);
lean_closure_set(v___f_2474_, 1, v_docCheckedModules_2275_);
lean_closure_set(v___f_2474_, 2, v___x_2473_);
v___x_2475_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2476_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2472_);
lean_dec_ref(v_env_2472_);
if (v___x_2475_ == 0)
{
if (v___x_2476_ == 0)
{
lean_dec_ref_known(v___x_2471_, 14);
lean_inc(v___x_2459_);
v___y_2337_ = v___x_2445_;
v___y_2338_ = v___f_2474_;
v___y_2339_ = v___x_2469_;
v___y_2340_ = v___x_2465_;
v___y_2341_ = v___x_2459_;
v___y_2342_ = v___x_2475_;
v___y_2343_ = v___y_2439_;
v_fileName_2344_ = v___x_2463_;
v_fileMap_2345_ = v___x_2464_;
v_currRecDepth_2346_ = v___x_2445_;
v_ref_2347_ = v___x_2467_;
v_currNamespace_2348_ = v___x_2452_;
v_openDecls_2349_ = v___x_2453_;
v_initHeartbeats_2350_ = v___x_2448_;
v_maxHeartbeats_2351_ = v___x_2468_;
v_quotContext_2352_ = v___x_2452_;
v_currMacroScope_2353_ = v___x_2449_;
v_cancelTk_x3f_2354_ = v___x_2470_;
v_suppressElabErrors_2355_ = v___x_2469_;
v_inheritedTraceOptions_2356_ = v___x_2461_;
v___y_2357_ = v___x_2459_;
goto v___jp_2336_;
}
else
{
lean_dec(v___x_2461_);
lean_dec(v___x_2448_);
v___y_2409_ = v___f_2474_;
v___y_2410_ = v___x_2445_;
v___y_2411_ = v___x_2469_;
v___y_2412_ = v___x_2465_;
v___y_2413_ = v___x_2475_;
v___y_2414_ = v___x_2459_;
v___y_2415_ = v___x_2471_;
v___y_2416_ = v___x_2446_;
v___y_2417_ = v___y_2439_;
v___y_2418_ = v___x_2475_;
goto v___jp_2408_;
}
}
else
{
lean_dec(v___x_2461_);
lean_dec(v___x_2448_);
v___y_2409_ = v___f_2474_;
v___y_2410_ = v___x_2445_;
v___y_2411_ = v___x_2469_;
v___y_2412_ = v___x_2465_;
v___y_2413_ = v___x_2475_;
v___y_2414_ = v___x_2459_;
v___y_2415_ = v___x_2471_;
v___y_2416_ = v___x_2446_;
v___y_2417_ = v___y_2439_;
v___y_2418_ = v___x_2476_;
goto v___jp_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2482_, lean_object* v_linterOpts_2483_, lean_object* v_sp_2484_, lean_object* v_env_2485_, lean_object* v_pkgRoot_2486_, lean_object* v_docCheckedModules_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2482_, v_linterOpts_2483_, v_sp_2484_, v_env_2485_, v_pkgRoot_2486_, v_docCheckedModules_2487_);
lean_dec_ref(v_linterOpts_2483_);
lean_dec_ref(v_args_2482_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2490_, uint8_t v___y_2491_, lean_object* v_as_2492_, size_t v_sz_2493_, size_t v_i_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2490_, v___y_2491_, v_as_2492_, v_sz_2493_, v_i_2494_, v_b_2495_, v___y_2496_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2500_, lean_object* v___y_2501_, lean_object* v_as_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v___y_8062__boxed_2509_; size_t v_sz_boxed_2510_; size_t v_i_boxed_2511_; lean_object* v_res_2512_; 
v___y_8062__boxed_2509_ = lean_unbox(v___y_2501_);
v_sz_boxed_2510_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2511_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2500_, v___y_8062__boxed_2509_, v_as_2502_, v_sz_boxed_2510_, v_i_boxed_2511_, v_b_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v_as_2502_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2513_, lean_object* v_as_2514_, size_t v_i_2515_, size_t v_stop_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v___y_2519_; uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_eq(v_i_2515_, v_stop_2516_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v_linter_2525_; uint8_t v___x_2526_; 
v___x_2524_ = lean_array_uget_borrowed(v_as_2514_, v_i_2515_);
v_linter_2525_ = lean_ctor_get(v___x_2524_, 0);
v___x_2526_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2525_, v_linterOpts_2513_);
if (v___x_2526_ == 0)
{
v___y_2519_ = v_b_2517_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2527_; 
lean_inc(v___x_2524_);
v___x_2527_ = lean_array_push(v_b_2517_, v___x_2524_);
v___y_2519_ = v___x_2527_;
goto v___jp_2518_;
}
}
else
{
return v_b_2517_;
}
v___jp_2518_:
{
size_t v___x_2520_; size_t v___x_2521_; 
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2515_, v___x_2520_);
v_i_2515_ = v___x_2521_;
v_b_2517_ = v___y_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2528_, lean_object* v_as_2529_, lean_object* v_i_2530_, lean_object* v_stop_2531_, lean_object* v_b_2532_){
_start:
{
size_t v_i_boxed_2533_; size_t v_stop_boxed_2534_; lean_object* v_res_2535_; 
v_i_boxed_2533_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_stop_boxed_2534_ = lean_unbox_usize(v_stop_2531_);
lean_dec(v_stop_2531_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2528_, v_as_2529_, v_i_boxed_2533_, v_stop_boxed_2534_, v_b_2532_);
lean_dec_ref(v_as_2529_);
lean_dec_ref(v_linterOpts_2528_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2538_, lean_object* v_as_2539_, size_t v_i_2540_, size_t v_stop_2541_, lean_object* v_b_2542_){
_start:
{
lean_object* v___y_2544_; uint8_t v___x_2548_; 
v___x_2548_ = lean_usize_dec_eq(v_i_2540_, v_stop_2541_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2575_; 
v___x_2549_ = lean_array_uget(v_as_2539_, v_i_2540_);
v_fst_2550_ = lean_ctor_get(v___x_2549_, 0);
v_snd_2551_ = lean_ctor_get(v___x_2549_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2553_ = v___x_2549_;
v_isShared_2554_ = v_isSharedCheck_2575_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_inc(v_fst_2550_);
lean_dec(v___x_2549_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2575_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___y_2556_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_array_get_size(v_snd_2551_);
v___x_2566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2567_ = lean_nat_dec_lt(v___x_2564_, v___x_2565_);
if (v___x_2567_ == 0)
{
lean_dec(v_snd_2551_);
v___y_2556_ = v___x_2566_;
goto v___jp_2555_;
}
else
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_nat_dec_le(v___x_2565_, v___x_2565_);
if (v___x_2568_ == 0)
{
if (v___x_2567_ == 0)
{
lean_dec(v_snd_2551_);
v___y_2556_ = v___x_2566_;
goto v___jp_2555_;
}
else
{
size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = lean_usize_of_nat(v___x_2565_);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2538_, v_snd_2551_, v___x_2569_, v___x_2570_, v___x_2566_);
lean_dec(v_snd_2551_);
v___y_2556_ = v___x_2571_;
goto v___jp_2555_;
}
}
else
{
size_t v___x_2572_; size_t v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = lean_usize_of_nat(v___x_2565_);
v___x_2574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2538_, v_snd_2551_, v___x_2572_, v___x_2573_, v___x_2566_);
lean_dec(v_snd_2551_);
v___y_2556_ = v___x_2574_;
goto v___jp_2555_;
}
}
v___jp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = lean_array_get_size(v___y_2556_);
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = lean_nat_dec_eq(v___x_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2561_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v___y_2556_);
v___x_2561_ = v___x_2553_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_fst_2550_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___y_2556_);
v___x_2561_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_array_push(v_b_2542_, v___x_2561_);
v___y_2544_ = v___x_2562_;
goto v___jp_2543_;
}
}
else
{
lean_dec_ref(v___y_2556_);
lean_del_object(v___x_2553_);
lean_dec(v_fst_2550_);
v___y_2544_ = v_b_2542_;
goto v___jp_2543_;
}
}
}
}
else
{
return v_b_2542_;
}
v___jp_2543_:
{
size_t v___x_2545_; size_t v___x_2546_; 
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_add(v_i_2540_, v___x_2545_);
v_i_2540_ = v___x_2546_;
v_b_2542_ = v___y_2544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2576_, lean_object* v_as_2577_, lean_object* v_i_2578_, lean_object* v_stop_2579_, lean_object* v_b_2580_){
_start:
{
size_t v_i_boxed_2581_; size_t v_stop_boxed_2582_; lean_object* v_res_2583_; 
v_i_boxed_2581_ = lean_unbox_usize(v_i_2578_);
lean_dec(v_i_2578_);
v_stop_boxed_2582_ = lean_unbox_usize(v_stop_2579_);
lean_dec(v_stop_2579_);
v_res_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2576_, v_as_2577_, v_i_boxed_2581_, v_stop_boxed_2582_, v_b_2580_);
lean_dec_ref(v_as_2577_);
lean_dec_ref(v_linterOpts_2576_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2584_, lean_object* v_as_2585_, lean_object* v_start_2586_, lean_object* v_stop_2587_){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2589_ = lean_nat_dec_lt(v_start_2586_, v_stop_2587_);
if (v___x_2589_ == 0)
{
return v___x_2588_;
}
else
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = lean_array_get_size(v_as_2585_);
v___x_2591_ = lean_nat_dec_le(v_stop_2587_, v___x_2590_);
if (v___x_2591_ == 0)
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_nat_dec_lt(v_start_2586_, v___x_2590_);
if (v___x_2592_ == 0)
{
return v___x_2588_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_usize_of_nat(v_start_2586_);
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2584_, v_as_2585_, v___x_2593_, v___x_2594_, v___x_2588_);
return v___x_2595_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_usize_of_nat(v_start_2586_);
v___x_2597_ = lean_usize_of_nat(v_stop_2587_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2584_, v_as_2585_, v___x_2596_, v___x_2597_, v___x_2588_);
return v___x_2598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2599_, lean_object* v_as_2600_, lean_object* v_start_2601_, lean_object* v_stop_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2599_, v_as_2600_, v_start_2601_, v_stop_2602_);
lean_dec(v_stop_2602_);
lean_dec(v_start_2601_);
lean_dec_ref(v_as_2600_);
lean_dec_ref(v_linterOpts_2599_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2604_, lean_object* v_init_2605_, lean_object* v_x_2606_){
_start:
{
if (lean_obj_tag(v_x_2606_) == 0)
{
lean_object* v_k_2608_; lean_object* v_v_2609_; lean_object* v_l_2610_; lean_object* v_r_2611_; lean_object* v___x_2612_; lean_object* v_a_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2628_; 
v_k_2608_ = lean_ctor_get(v_x_2606_, 1);
lean_inc(v_k_2608_);
v_v_2609_ = lean_ctor_get(v_x_2606_, 2);
lean_inc(v_v_2609_);
v_l_2610_ = lean_ctor_get(v_x_2606_, 3);
lean_inc(v_l_2610_);
v_r_2611_ = lean_ctor_get(v_x_2606_, 4);
lean_inc(v_r_2611_);
lean_dec_ref_known(v_x_2606_, 5);
lean_inc(v_fst_2604_);
v___x_2612_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2604_, v_init_2605_, v_l_2610_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v_a_2614_ = lean_ctor_get(v_a_2613_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2616_ = v_a_2613_;
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v_a_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v_anyUnlocated_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v_anyUnlocated_2618_ = 1;
v___x_2619_ = l_Lean_Name_toString(v_k_2608_, v_anyUnlocated_2618_);
lean_inc(v_fst_2604_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 0);
lean_ctor_set(v___x_2616_, 0, v_fst_2604_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_fst_2604_);
v___x_2621_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
double v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2622_ = lean_float_of_nat(v_v_2609_);
v___x_2623_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2623_, 0, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2619_);
lean_ctor_set(v___x_2624_, 1, v___x_2621_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
v___x_2625_ = lean_array_push(v_a_2614_, v___x_2624_);
v_init_2605_ = v___x_2625_;
v_x_2606_ = v_r_2611_;
goto _start;
}
}
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_fst_2604_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_init_2605_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2631_, lean_object* v_init_2632_, lean_object* v_x_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2631_, v_init_2632_, v_x_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2636_, lean_object* v_k_2637_, lean_object* v_fallback_2638_){
_start:
{
if (lean_obj_tag(v_t_2636_) == 0)
{
lean_object* v_k_2639_; lean_object* v_v_2640_; lean_object* v_l_2641_; lean_object* v_r_2642_; uint8_t v___x_2643_; 
v_k_2639_ = lean_ctor_get(v_t_2636_, 1);
v_v_2640_ = lean_ctor_get(v_t_2636_, 2);
v_l_2641_ = lean_ctor_get(v_t_2636_, 3);
v_r_2642_ = lean_ctor_get(v_t_2636_, 4);
v___x_2643_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2637_, v_k_2639_);
switch(v___x_2643_)
{
case 0:
{
v_t_2636_ = v_l_2641_;
goto _start;
}
case 1:
{
lean_inc(v_v_2640_);
return v_v_2640_;
}
default: 
{
v_t_2636_ = v_r_2642_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2638_);
return v_fallback_2638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2646_, lean_object* v_k_2647_, lean_object* v_fallback_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2646_, v_k_2647_, v_fallback_2648_);
lean_dec(v_fallback_2648_);
lean_dec(v_k_2647_);
lean_dec(v_t_2646_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2650_, size_t v_i_2651_, size_t v_stop_2652_, lean_object* v_b_2653_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_usize_dec_eq(v_i_2651_, v_stop_2652_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v_linter_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; size_t v___x_2662_; size_t v___x_2663_; 
v___x_2655_ = lean_array_uget_borrowed(v_as_2650_, v_i_2651_);
v_linter_2656_ = lean_ctor_get(v___x_2655_, 0);
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2653_, v_linter_2656_, v___x_2657_);
v___x_2659_ = lean_unsigned_to_nat(1u);
v___x_2660_ = lean_nat_add(v___x_2658_, v___x_2659_);
lean_dec(v___x_2658_);
lean_inc(v_linter_2656_);
v___x_2661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2656_, v___x_2660_, v_b_2653_);
v___x_2662_ = ((size_t)1ULL);
v___x_2663_ = lean_usize_add(v_i_2651_, v___x_2662_);
v_i_2651_ = v___x_2663_;
v_b_2653_ = v___x_2661_;
goto _start;
}
else
{
return v_b_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2665_, lean_object* v_i_2666_, lean_object* v_stop_2667_, lean_object* v_b_2668_){
_start:
{
size_t v_i_boxed_2669_; size_t v_stop_boxed_2670_; lean_object* v_res_2671_; 
v_i_boxed_2669_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_stop_boxed_2670_ = lean_unbox_usize(v_stop_2667_);
lean_dec(v_stop_2667_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2665_, v_i_boxed_2669_, v_stop_boxed_2670_, v_b_2668_);
lean_dec_ref(v_as_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2672_, size_t v_sz_2673_, size_t v_i_2674_, lean_object* v_b_2675_){
_start:
{
lean_object* v_a_2678_; uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_lt(v_i_2674_, v_sz_2673_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_b_2675_);
return v___x_2683_;
}
else
{
lean_object* v_a_2684_; lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___y_2688_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_a_2684_ = lean_array_uget_borrowed(v_as_2672_, v_i_2674_);
v_fst_2685_ = lean_ctor_get(v_a_2684_, 0);
v_snd_2686_ = lean_ctor_get(v_a_2684_, 1);
v___x_2710_ = lean_box(1);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_array_get_size(v_snd_2686_);
v___x_2713_ = lean_nat_dec_lt(v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
v___y_2688_ = v___x_2710_;
goto v___jp_2687_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_nat_dec_le(v___x_2712_, v___x_2712_);
if (v___x_2714_ == 0)
{
if (v___x_2713_ == 0)
{
v___y_2688_ = v___x_2710_;
goto v___jp_2687_;
}
else
{
size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = ((size_t)0ULL);
v___x_2716_ = lean_usize_of_nat(v___x_2712_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2686_, v___x_2715_, v___x_2716_, v___x_2710_);
v___y_2688_ = v___x_2717_;
goto v___jp_2687_;
}
}
else
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)0ULL);
v___x_2719_ = lean_usize_of_nat(v___x_2712_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2686_, v___x_2718_, v___x_2719_, v___x_2710_);
v___y_2688_ = v___x_2720_;
goto v___jp_2687_;
}
}
v___jp_2687_:
{
lean_object* v___x_2689_; 
lean_inc(v_fst_2685_);
v___x_2689_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2685_, v_b_2675_, v___y_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v_a_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v_a_2691_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_a_2691_);
lean_dec(v_a_2690_);
v_a_2678_ = v_a_2691_;
goto v___jp_2677_;
}
else
{
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
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
if (lean_obj_tag(v_a_2692_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; 
v_a_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v_a_2692_, 1);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 0);
lean_ctor_set(v___x_2694_, 0, v_a_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
else
{
lean_object* v_a_2700_; 
lean_del_object(v___x_2694_);
v_a_2700_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v_a_2692_, 1);
v_a_2678_ = v_a_2700_;
goto v___jp_2677_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2689_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2689_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
}
v___jp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2674_, v___x_2679_);
v_i_2674_ = v___x_2680_;
v_b_2675_ = v_a_2678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2721_, lean_object* v_sz_2722_, lean_object* v_i_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_){
_start:
{
size_t v_sz_boxed_2726_; size_t v_i_boxed_2727_; lean_object* v_res_2728_; 
v_sz_boxed_2726_ = lean_unbox_usize(v_sz_2722_);
lean_dec(v_sz_2722_);
v_i_boxed_2727_ = lean_unbox_usize(v_i_2723_);
lean_dec(v_i_2723_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2721_, v_sz_boxed_2726_, v_i_boxed_2727_, v_b_2724_);
lean_dec_ref(v_as_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2732_, lean_object* v_as_2733_, size_t v_sz_2734_, size_t v_i_2735_, lean_object* v_b_2736_){
_start:
{
lean_object* v_a_2739_; uint8_t v_anyUnlocated_2743_; 
v_anyUnlocated_2743_ = lean_usize_dec_lt(v_i_2735_, v_sz_2734_);
if (v_anyUnlocated_2743_ == 0)
{
lean_object* v___x_2744_; 
lean_dec(v_fst_2732_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_b_2736_);
return v___x_2744_;
}
else
{
lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2783_; 
v_fst_2745_ = lean_ctor_get(v_b_2736_, 0);
v_snd_2746_ = lean_ctor_get(v_b_2736_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_b_2736_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2748_ = v_b_2736_;
v_isShared_2749_ = v_isSharedCheck_2783_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snd_2746_);
lean_inc(v_fst_2745_);
lean_dec(v_b_2736_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2783_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_a_2750_; lean_object* v_position_x3f_2751_; 
v_a_2750_ = lean_array_uget_borrowed(v_as_2733_, v_i_2735_);
v_position_x3f_2751_ = lean_ctor_get(v_a_2750_, 2);
if (lean_obj_tag(v_position_x3f_2751_) == 0)
{
lean_object* v_linter_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v_snd_2746_);
v_linter_2752_ = lean_ctor_get(v_a_2750_, 0);
v___x_2753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2752_);
v___x_2754_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2752_, v_anyUnlocated_2743_);
v___x_2755_ = lean_string_append(v___x_2753_, v___x_2754_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2757_ = lean_string_append(v___x_2755_, v___x_2756_);
lean_inc(v_fst_2732_);
v___x_2758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2732_, v_anyUnlocated_2743_);
v___x_2759_ = lean_string_append(v___x_2757_, v___x_2758_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2761_ = lean_string_append(v___x_2759_, v___x_2760_);
v___x_2762_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_dec_ref_known(v___x_2762_, 1);
v___x_2763_ = lean_box(v_anyUnlocated_2743_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v___x_2763_);
v___x_2765_ = v___x_2748_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_fst_2745_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v_a_2739_ = v___x_2765_;
goto v___jp_2738_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_del_object(v___x_2748_);
lean_dec(v_fst_2745_);
lean_dec(v_fst_2732_);
v_a_2767_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2762_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2762_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_linter_2775_; lean_object* v_file_2776_; lean_object* v_val_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v_linter_2775_ = lean_ctor_get(v_a_2750_, 0);
v_file_2776_ = lean_ctor_get(v_a_2750_, 3);
v_val_2777_ = lean_ctor_get(v_position_x3f_2751_, 0);
lean_inc(v_linter_2775_);
lean_inc(v_val_2777_);
lean_inc_ref(v_file_2776_);
v___x_2778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2778_, 0, v_file_2776_);
lean_ctor_set(v___x_2778_, 1, v_val_2777_);
lean_ctor_set(v___x_2778_, 2, v_linter_2775_);
v___x_2779_ = lean_array_push(v_fst_2745_, v___x_2778_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2779_);
v___x_2781_ = v___x_2748_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_snd_2746_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v_a_2739_ = v___x_2781_;
goto v___jp_2738_;
}
}
}
}
v___jp_2738_:
{
size_t v___x_2740_; size_t v___x_2741_; 
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_add(v_i_2735_, v___x_2740_);
v_i_2735_ = v___x_2741_;
v_b_2736_ = v_a_2739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2784_, lean_object* v_as_2785_, lean_object* v_sz_2786_, lean_object* v_i_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_){
_start:
{
size_t v_sz_boxed_2790_; size_t v_i_boxed_2791_; lean_object* v_res_2792_; 
v_sz_boxed_2790_ = lean_unbox_usize(v_sz_2786_);
lean_dec(v_sz_2786_);
v_i_boxed_2791_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2784_, v_as_2785_, v_sz_boxed_2790_, v_i_boxed_2791_, v_b_2788_);
lean_dec_ref(v_as_2785_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2793_, size_t v_sz_2794_, size_t v_i_2795_, lean_object* v_b_2796_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_usize_dec_lt(v_i_2795_, v_sz_2794_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2799_, 0, v_b_2796_);
return v___x_2799_;
}
else
{
lean_object* v_a_2800_; lean_object* v_fst_2801_; lean_object* v_snd_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2827_; 
v_a_2800_ = lean_array_uget_borrowed(v_as_2793_, v_i_2795_);
v_fst_2801_ = lean_ctor_get(v_a_2800_, 0);
v_snd_2802_ = lean_ctor_get(v_a_2800_, 1);
v_fst_2803_ = lean_ctor_get(v_b_2796_, 0);
v_snd_2804_ = lean_ctor_get(v_b_2796_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_b_2796_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2806_ = v_b_2796_;
v_isShared_2807_ = v_isSharedCheck_2827_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_snd_2804_);
lean_inc(v_fst_2803_);
lean_dec(v_b_2796_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2827_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_fst_2803_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_snd_2804_);
v___x_2809_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
size_t v_sz_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v_sz_2810_ = lean_array_size(v_snd_2802_);
v___x_2811_ = ((size_t)0ULL);
lean_inc(v_fst_2801_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2801_, v_snd_2802_, v_sz_2810_, v___x_2811_, v___x_2809_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2825_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v_fst_2814_ = lean_ctor_get(v_a_2813_, 0);
v_snd_2815_ = lean_ctor_get(v_a_2813_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_a_2813_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2817_ = v_a_2813_;
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snd_2815_);
lean_inc(v_fst_2814_);
lean_dec(v_a_2813_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2825_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_fst_2814_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_snd_2815_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
size_t v___x_2821_; size_t v___x_2822_; 
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_add(v_i_2795_, v___x_2821_);
v_i_2795_ = v___x_2822_;
v_b_2796_ = v___x_2820_;
goto _start;
}
}
}
else
{
return v___x_2812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2828_, lean_object* v_sz_2829_, lean_object* v_i_2830_, lean_object* v_b_2831_, lean_object* v___y_2832_){
_start:
{
size_t v_sz_boxed_2833_; size_t v_i_boxed_2834_; lean_object* v_res_2835_; 
v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2829_);
lean_dec(v_sz_2829_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2830_);
lean_dec(v_i_2830_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2828_, v_sz_boxed_2833_, v_i_boxed_2834_, v_b_2831_);
lean_dec_ref(v_as_2828_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2836_, size_t v_sz_2837_, size_t v_i_2838_, lean_object* v_b_2839_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_lt(v_i_2838_, v_sz_2837_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2839_);
return v___x_2842_;
}
else
{
lean_object* v_a_2843_; lean_object* v_message_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2843_ = lean_array_uget_borrowed(v_as_2836_, v_i_2838_);
v_message_2844_ = lean_ctor_get(v_a_2843_, 1);
v___x_2845_ = 0;
lean_inc_ref(v_message_2844_);
v___x_2846_ = l_Lean_SerialMessage_toString(v_message_2844_, v___x_2845_);
v___x_2847_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; 
lean_dec_ref_known(v___x_2847_, 1);
v___x_2848_ = lean_box(0);
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_add(v_i_2838_, v___x_2849_);
v_i_2838_ = v___x_2850_;
v_b_2839_ = v___x_2848_;
goto _start;
}
else
{
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2852_, lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_b_2855_, lean_object* v___y_2856_){
_start:
{
size_t v_sz_boxed_2857_; size_t v_i_boxed_2858_; lean_object* v_res_2859_; 
v_sz_boxed_2857_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2852_, v_sz_boxed_2857_, v_i_boxed_2858_, v_b_2855_);
lean_dec_ref(v_as_2852_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2862_, size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_b_2865_){
_start:
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_usize_dec_lt(v_i_2864_, v_sz_2863_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_b_2865_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_a_2869_ = lean_array_uget_borrowed(v_as_2862_, v_i_2864_);
v_fst_2870_ = lean_ctor_get(v_a_2869_, 0);
v_snd_2871_ = lean_ctor_get(v_a_2869_, 1);
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_2870_);
v___x_2873_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2870_, v___x_2867_);
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
v___x_2877_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2876_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v___x_2878_; size_t v_sz_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
lean_dec_ref_known(v___x_2877_, 1);
v___x_2878_ = lean_box(0);
v_sz_2879_ = lean_array_size(v_snd_2871_);
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_2871_, v_sz_2879_, v___x_2880_, v___x_2878_);
if (lean_obj_tag(v___x_2881_) == 0)
{
size_t v___x_2882_; size_t v___x_2883_; 
lean_dec_ref_known(v___x_2881_, 1);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_i_2864_, v___x_2882_);
v_i_2864_ = v___x_2883_;
v_b_2865_ = v___x_2878_;
goto _start;
}
else
{
return v___x_2881_;
}
}
else
{
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_2885_, lean_object* v_sz_2886_, lean_object* v_i_2887_, lean_object* v_b_2888_, lean_object* v___y_2889_){
_start:
{
size_t v_sz_boxed_2890_; size_t v_i_boxed_2891_; lean_object* v_res_2892_; 
v_sz_boxed_2890_ = lean_unbox_usize(v_sz_2886_);
lean_dec(v_sz_2886_);
v_i_boxed_2891_ = lean_unbox_usize(v_i_2887_);
lean_dec(v_i_2887_);
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_2885_, v_sz_boxed_2890_, v_i_boxed_2891_, v_b_2888_);
lean_dec_ref(v_as_2885_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_2899_, lean_object* v_linterOpts_2900_, lean_object* v_env_2901_, lean_object* v_mod_2902_){
_start:
{
uint8_t v_lintOnly_2904_; uint8_t v_mode_2905_; lean_object* v___y_2907_; uint8_t v___y_2908_; lean_object* v___y_2976_; lean_object* v___x_2982_; lean_object* v_textGroups_2983_; 
v_lintOnly_2904_ = lean_ctor_get_uint8(v_args_2899_, sizeof(void*)*4);
v_mode_2905_ = lean_ctor_get_uint8(v_args_2899_, sizeof(void*)*4 + 1);
v___x_2982_ = l_Lean_Name_getRoot(v_mod_2902_);
v_textGroups_2983_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_2901_, v___x_2982_);
lean_dec(v___x_2982_);
if (v_lintOnly_2904_ == 0)
{
v___y_2976_ = v_textGroups_2983_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_array_get_size(v_textGroups_2983_);
v___x_2986_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2900_, v_textGroups_2983_, v___x_2984_, v___x_2985_);
lean_dec_ref(v_textGroups_2983_);
v___y_2976_ = v___x_2986_;
goto v___jp_2975_;
}
v___jp_2906_:
{
switch(v_mode_2905_)
{
case 0:
{
lean_object* v___x_2909_; size_t v_sz_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2909_ = lean_box(0);
v_sz_2910_ = lean_array_size(v___y_2907_);
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_2907_, v_sz_2910_, v___x_2911_, v___x_2909_);
lean_dec_ref(v___y_2907_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2921_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2916_, 0, v___y_2908_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_a_2922_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2912_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
case 1:
{
lean_object* v___x_2930_; size_t v_sz_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_2931_ = lean_array_size(v___y_2907_);
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_2907_, v_sz_2931_, v___x_2932_, v___x_2930_);
lean_dec_ref(v___y_2907_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2945_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_fst_2938_; lean_object* v_snd_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2943_; 
v_fst_2938_ = lean_ctor_get(v_a_2934_, 0);
lean_inc(v_fst_2938_);
v_snd_2939_ = lean_ctor_get(v_a_2934_, 1);
lean_inc(v_snd_2939_);
lean_dec(v_a_2934_);
v___x_2940_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2940_, 0, v_fst_2938_);
v___x_2941_ = lean_unbox(v_snd_2939_);
lean_dec(v_snd_2939_);
lean_ctor_set_uint8(v___x_2940_, sizeof(void*)*1, v___x_2941_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v___x_2940_);
v___x_2943_ = v___x_2936_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2940_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2933_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2933_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_2954_; size_t v_sz_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v_codeQualityEntries_2954_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__1));
v_sz_2955_ = lean_array_size(v___y_2907_);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_2907_, v_sz_2955_, v___x_2956_, v_codeQualityEntries_2954_);
lean_dec_ref(v___y_2907_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2966_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_a_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2962_);
v___x_2964_ = v___x_2960_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2957_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2957_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
v___jp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2977_ = lean_array_get_size(v___y_2976_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = lean_nat_dec_eq(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
uint8_t v___x_2980_; 
v___x_2980_ = 1;
v___y_2907_ = v___y_2976_;
v___y_2908_ = v___x_2980_;
goto v___jp_2906_;
}
else
{
uint8_t v___x_2981_; 
v___x_2981_ = 0;
v___y_2907_ = v___y_2976_;
v___y_2908_ = v___x_2981_;
goto v___jp_2906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_2987_, lean_object* v_linterOpts_2988_, lean_object* v_env_2989_, lean_object* v_mod_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_2987_, v_linterOpts_2988_, v_env_2989_, v_mod_2990_);
lean_dec(v_mod_2990_);
lean_dec_ref(v_env_2989_);
lean_dec_ref(v_linterOpts_2988_);
lean_dec_ref(v_args_2987_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_2993_, lean_object* v_t_2994_, lean_object* v_k_2995_, lean_object* v_fallback_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2994_, v_k_2995_, v_fallback_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_2998_, lean_object* v_t_2999_, lean_object* v_k_3000_, lean_object* v_fallback_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_2998_, v_t_2999_, v_k_3000_, v_fallback_3001_);
lean_dec(v_fallback_3001_);
lean_dec(v_k_3000_);
lean_dec(v_t_2999_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3003_, lean_object* v_____r_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3008_, 0, v___y_3003_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3010_, lean_object* v_____r_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v___y_15714__boxed_3015_; lean_object* v_res_3016_; 
v___y_15714__boxed_3015_ = lean_unbox(v___y_3010_);
v_res_3016_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15714__boxed_3015_, v_____r_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
return v_res_3016_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
lean_ctor_set(v___x_3022_, 3, v___x_3021_);
lean_ctor_set(v___x_3022_, 4, v___x_3020_);
lean_ctor_set(v___x_3022_, 5, v___x_3020_);
lean_ctor_set(v___x_3022_, 6, v___x_3020_);
lean_ctor_set(v___x_3022_, 7, v___x_3020_);
lean_ctor_set(v___x_3022_, 8, v___x_3020_);
lean_ctor_set(v___x_3022_, 9, v___x_3020_);
lean_ctor_set(v___x_3022_, 10, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_unsigned_to_nat(32u);
v___x_3024_ = lean_mk_empty_array_with_capacity(v___x_3023_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3026_ = ((size_t)5ULL);
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = lean_unsigned_to_nat(32u);
v___x_3029_ = lean_mk_empty_array_with_capacity(v___x_3028_);
v___x_3030_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3031_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3029_);
lean_ctor_set(v___x_3031_, 2, v___x_3027_);
lean_ctor_set(v___x_3031_, 3, v___x_3027_);
lean_ctor_set_usize(v___x_3031_, 4, v___x_3026_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_box(1);
v___x_3033_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3034_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3033_);
lean_ctor_set(v___x_3035_, 2, v___x_3032_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; lean_object* v_env_3041_; lean_object* v_options_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3040_ = lean_st_ref_get(v___y_3038_);
v_env_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_env_3041_);
lean_dec(v___x_3040_);
v_options_3042_ = lean_ctor_get(v___y_3037_, 2);
v___x_3043_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3044_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3042_);
v___x_3045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3045_, 0, v_env_3041_);
lean_ctor_set(v___x_3045_, 1, v___x_3043_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
lean_ctor_set(v___x_3045_, 3, v_options_3042_);
v___x_3046_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v_msgData_3036_);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_ref_3057_; lean_object* v___x_3058_; lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3067_; 
v_ref_3057_ = lean_ctor_get(v___y_3054_, 5);
v___x_3058_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3053_, v___y_3054_, v___y_3055_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
lean_inc(v_ref_3057_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_ref_3057_);
lean_ctor_set(v___x_3063_, 1, v_a_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 1);
lean_ctor_set(v___x_3061_, 0, v___x_3063_);
v___x_3065_ = v___x_3061_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3073_, lean_object* v_msg_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_fileName_3078_; lean_object* v_fileMap_3079_; lean_object* v_options_3080_; lean_object* v_currRecDepth_3081_; lean_object* v_maxRecDepth_3082_; lean_object* v_ref_3083_; lean_object* v_currNamespace_3084_; lean_object* v_openDecls_3085_; lean_object* v_initHeartbeats_3086_; lean_object* v_maxHeartbeats_3087_; lean_object* v_quotContext_3088_; lean_object* v_currMacroScope_3089_; uint8_t v_diag_3090_; lean_object* v_cancelTk_x3f_3091_; uint8_t v_suppressElabErrors_3092_; lean_object* v_inheritedTraceOptions_3093_; lean_object* v_ref_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_fileName_3078_ = lean_ctor_get(v___y_3075_, 0);
v_fileMap_3079_ = lean_ctor_get(v___y_3075_, 1);
v_options_3080_ = lean_ctor_get(v___y_3075_, 2);
v_currRecDepth_3081_ = lean_ctor_get(v___y_3075_, 3);
v_maxRecDepth_3082_ = lean_ctor_get(v___y_3075_, 4);
v_ref_3083_ = lean_ctor_get(v___y_3075_, 5);
v_currNamespace_3084_ = lean_ctor_get(v___y_3075_, 6);
v_openDecls_3085_ = lean_ctor_get(v___y_3075_, 7);
v_initHeartbeats_3086_ = lean_ctor_get(v___y_3075_, 8);
v_maxHeartbeats_3087_ = lean_ctor_get(v___y_3075_, 9);
v_quotContext_3088_ = lean_ctor_get(v___y_3075_, 10);
v_currMacroScope_3089_ = lean_ctor_get(v___y_3075_, 11);
v_diag_3090_ = lean_ctor_get_uint8(v___y_3075_, sizeof(void*)*14);
v_cancelTk_x3f_3091_ = lean_ctor_get(v___y_3075_, 12);
v_suppressElabErrors_3092_ = lean_ctor_get_uint8(v___y_3075_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3093_ = lean_ctor_get(v___y_3075_, 13);
v_ref_3094_ = l_Lean_replaceRef(v_ref_3073_, v_ref_3083_);
lean_inc_ref(v_inheritedTraceOptions_3093_);
lean_inc(v_cancelTk_x3f_3091_);
lean_inc(v_currMacroScope_3089_);
lean_inc(v_quotContext_3088_);
lean_inc(v_maxHeartbeats_3087_);
lean_inc(v_initHeartbeats_3086_);
lean_inc(v_openDecls_3085_);
lean_inc(v_currNamespace_3084_);
lean_inc(v_maxRecDepth_3082_);
lean_inc(v_currRecDepth_3081_);
lean_inc_ref(v_options_3080_);
lean_inc_ref(v_fileMap_3079_);
lean_inc_ref(v_fileName_3078_);
v___x_3095_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3095_, 0, v_fileName_3078_);
lean_ctor_set(v___x_3095_, 1, v_fileMap_3079_);
lean_ctor_set(v___x_3095_, 2, v_options_3080_);
lean_ctor_set(v___x_3095_, 3, v_currRecDepth_3081_);
lean_ctor_set(v___x_3095_, 4, v_maxRecDepth_3082_);
lean_ctor_set(v___x_3095_, 5, v_ref_3094_);
lean_ctor_set(v___x_3095_, 6, v_currNamespace_3084_);
lean_ctor_set(v___x_3095_, 7, v_openDecls_3085_);
lean_ctor_set(v___x_3095_, 8, v_initHeartbeats_3086_);
lean_ctor_set(v___x_3095_, 9, v_maxHeartbeats_3087_);
lean_ctor_set(v___x_3095_, 10, v_quotContext_3088_);
lean_ctor_set(v___x_3095_, 11, v_currMacroScope_3089_);
lean_ctor_set(v___x_3095_, 12, v_cancelTk_x3f_3091_);
lean_ctor_set(v___x_3095_, 13, v_inheritedTraceOptions_3093_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*14, v_diag_3090_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*14 + 1, v_suppressElabErrors_3092_);
v___x_3096_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3074_, v___x_3095_, v___y_3076_);
lean_dec_ref_known(v___x_3095_, 14);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3097_, lean_object* v_msg_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3097_, v_msg_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v_ref_3097_);
return v_res_3102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3105_ = l_Lean_stringToMessageData(v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3111_ = l_Lean_stringToMessageData(v___x_3110_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3114_ = l_Lean_stringToMessageData(v___x_3113_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3117_ = l_Lean_stringToMessageData(v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3120_ = l_Lean_stringToMessageData(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3123_ = l_Lean_stringToMessageData(v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3124_, lean_object* v_declHint_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v_env_3129_; uint8_t v___x_3130_; 
v___x_3128_ = lean_st_ref_get(v___y_3126_);
v_env_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc_ref(v_env_3129_);
lean_dec(v___x_3128_);
v___x_3130_ = l_Lean_Name_isAnonymous(v_declHint_3125_);
if (v___x_3130_ == 0)
{
uint8_t v_isExporting_3131_; 
v_isExporting_3131_ = lean_ctor_get_uint8(v_env_3129_, sizeof(void*)*8);
if (v_isExporting_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref(v_env_3129_);
lean_dec(v_declHint_3125_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_msg_3124_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
lean_inc_ref(v_env_3129_);
v___x_3133_ = l_Lean_Environment_setExporting(v_env_3129_, v___x_3130_);
lean_inc(v_declHint_3125_);
lean_inc_ref(v___x_3133_);
v___x_3134_ = l_Lean_Environment_contains(v___x_3133_, v_declHint_3125_, v_isExporting_3131_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
lean_dec_ref(v___x_3133_);
lean_dec_ref(v_env_3129_);
lean_dec(v_declHint_3125_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_msg_3124_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v_c_3141_; lean_object* v___x_3142_; 
v___x_3136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3138_ = l_Lean_Options_empty;
v___x_3139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3133_);
lean_ctor_set(v___x_3139_, 1, v___x_3136_);
lean_ctor_set(v___x_3139_, 2, v___x_3137_);
lean_ctor_set(v___x_3139_, 3, v___x_3138_);
lean_inc(v_declHint_3125_);
v___x_3140_ = l_Lean_MessageData_ofConstName(v_declHint_3125_, v___x_3130_);
v_c_3141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3141_, 0, v___x_3139_);
lean_ctor_set(v_c_3141_, 1, v___x_3140_);
v___x_3142_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3129_, v_declHint_3125_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec_ref(v_env_3129_);
lean_dec(v_declHint_3125_);
v___x_3143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v_c_3141_);
v___x_3145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_MessageData_note(v___x_3146_);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_msg_3124_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v_val_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3185_; 
v_val_3150_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3152_ = v___x_3142_;
v_isShared_3153_ = v_isSharedCheck_3185_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_val_3150_);
lean_dec(v___x_3142_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3185_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v_mod_3157_; uint8_t v___x_3158_; 
v___x_3154_ = lean_box(0);
v___x_3155_ = l_Lean_Environment_header(v_env_3129_);
lean_dec_ref(v_env_3129_);
v___x_3156_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3155_);
v_mod_3157_ = lean_array_get(v___x_3154_, v___x_3156_, v_val_3150_);
lean_dec(v_val_3150_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = l_Lean_isPrivateName(v_declHint_3125_);
lean_dec(v_declHint_3125_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v_c_3141_);
v___x_3161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_MessageData_ofName(v_mod_3157_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = l_Lean_MessageData_note(v___x_3166_);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_msg_3124_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3168_);
v___x_3170_ = v___x_3152_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3172_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v_c_3141_);
v___x_3174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_MessageData_ofName(v_mod_3157_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Lean_MessageData_note(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_msg_3124_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3181_);
v___x_3183_ = v___x_3152_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3186_; 
lean_dec_ref(v_env_3129_);
lean_dec(v_declHint_3125_);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v_msg_3124_);
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3187_, lean_object* v_declHint_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3187_, v_declHint_3188_, v___y_3189_);
lean_dec(v___y_3189_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3192_, lean_object* v_declHint_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3207_; 
v___x_3197_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3192_, v_declHint_3193_, v___y_3195_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3207_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3207_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3202_ = l_Lean_unknownIdentifierMessageTag;
v___x_3203_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v_a_3198_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3203_);
v___x_3205_ = v___x_3200_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3208_, lean_object* v_declHint_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3208_, v_declHint_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3214_, lean_object* v_msg_3215_, lean_object* v_declHint_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v___x_3222_; 
v___x_3220_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3215_, v_declHint_3216_, v___y_3217_, v___y_3218_);
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3214_, v_a_3221_, v___y_3217_, v___y_3218_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3223_, lean_object* v_msg_3224_, lean_object* v_declHint_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3223_, v_msg_3224_, v_declHint_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v_ref_3223_);
return v_res_3229_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3235_, lean_object* v_constName_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; uint8_t v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3240_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3241_ = 0;
lean_inc(v_constName_3236_);
v___x_3242_ = l_Lean_MessageData_ofConstName(v_constName_3236_, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3240_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3235_, v___x_3245_, v_constName_3236_, v___y_3237_, v___y_3238_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3247_, lean_object* v_constName_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3247_, v_constName_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v_ref_3247_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_ref_3257_; lean_object* v___x_3258_; 
v_ref_3257_ = lean_ctor_get(v___y_3254_, 5);
v___x_3258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3257_, v_constName_3253_, v___y_3254_, v___y_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v_env_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; 
v___x_3268_ = lean_st_ref_get(v___y_3266_);
v_env_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_ref(v_env_3269_);
lean_dec(v___x_3268_);
v___x_3270_ = 0;
lean_inc(v_constName_3264_);
v___x_3271_ = l_Lean_Environment_find_x3f(v_env_3269_, v_constName_3264_, v___x_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3264_, v___y_3265_, v___y_3266_);
return v___x_3272_;
}
else
{
lean_object* v_val_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_constName_3264_);
v_val_3273_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3271_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_val_3273_);
lean_dec(v___x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 0);
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_val_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
lean_inc(v_declName_3286_);
v___x_3290_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3317_; 
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3318_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3317_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3317_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v_env_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_st_ref_get(v___y_3288_);
v_env_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_ref(v_env_3295_);
lean_dec(v___x_3294_);
v___x_3296_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3295_, v_declName_3286_);
lean_dec(v_declName_3286_);
lean_dec_ref(v_env_3295_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3297_);
v___x_3299_ = v___x_3292_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
else
{
lean_object* v_val_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3316_; 
v_val_3301_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3303_ = v___x_3296_;
v_isShared_3304_ = v_isSharedCheck_3316_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_val_3301_);
lean_dec(v___x_3296_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3316_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v_env_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3305_ = lean_st_ref_get(v___y_3288_);
v_env_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc_ref(v_env_3306_);
lean_dec(v___x_3305_);
v___x_3307_ = lean_box(0);
v___x_3308_ = l_Lean_Environment_allImportedModuleNames(v_env_3306_);
lean_dec_ref(v_env_3306_);
v___x_3309_ = lean_array_get(v___x_3307_, v___x_3308_, v_val_3301_);
lean_dec(v_val_3301_);
lean_dec_ref(v___x_3308_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3309_);
v___x_3311_ = v___x_3303_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3311_);
v___x_3313_ = v___x_3292_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_declName_3286_);
v_a_3319_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3290_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3290_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3333_, lean_object* v_sp_3334_, lean_object* v___x_3335_, lean_object* v_as_3336_, size_t v_sz_3337_, size_t v_i_3338_, lean_object* v_b_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_a_3344_; uint8_t v___x_3348_; 
v___x_3348_ = lean_usize_dec_lt(v_i_3338_, v_sz_3337_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_b_3339_);
return v___x_3349_;
}
else
{
lean_object* v_a_3350_; lean_object* v_fst_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3486_; 
v_a_3350_ = lean_array_uget(v_as_3336_, v_i_3338_);
v_fst_3351_ = lean_ctor_get(v_a_3350_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_a_3350_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v_a_3350_, 1);
lean_dec(v_unused_3487_);
v___x_3353_ = v_a_3350_;
v_isShared_3354_ = v_isSharedCheck_3486_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_fst_3351_);
lean_dec(v_a_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3486_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; 
lean_inc(v_fst_3351_);
v___x_3355_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3351_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref_known(v___x_3355_, 1);
if (lean_obj_tag(v_a_3356_) == 0)
{
lean_object* v_fst_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3391_; 
v_fst_3357_ = lean_ctor_get(v_b_3339_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_b_3339_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v_b_3339_, 1);
lean_dec(v_unused_3392_);
v___x_3359_ = v_b_3339_;
v_isShared_3360_ = v_isSharedCheck_3391_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_fst_3357_);
lean_dec(v_b_3339_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3391_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_optName_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_optName_3361_ = lean_ctor_get(v_fst_3333_, 1);
v___x_3362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3351_, v___x_3348_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
lean_inc(v_optName_3361_);
v___x_3367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3361_, v___x_3348_);
v___x_3368_ = lean_string_append(v___x_3366_, v___x_3367_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3370_ = lean_string_append(v___x_3368_, v___x_3369_);
v___x_3371_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
lean_dec_ref_known(v___x_3371_, 1);
lean_del_object(v___x_3353_);
v___x_3372_ = lean_box(v___x_3348_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3372_);
v___x_3374_ = v___x_3359_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
v_a_3344_ = v___x_3374_;
goto v___jp_3343_;
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3390_; 
lean_del_object(v___x_3359_);
lean_dec(v_fst_3357_);
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v_a_3376_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3378_ = v___x_3371_;
v_isShared_3379_ = v_isSharedCheck_3390_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3371_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3390_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_ref_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v_ref_3380_ = lean_ctor_get(v___y_3340_, 5);
v___x_3381_ = lean_io_error_to_string(v_a_3376_);
v___x_3382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
v___x_3383_ = l_Lean_MessageData_ofFormat(v___x_3382_);
lean_inc(v_ref_3380_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3383_);
lean_ctor_set(v___x_3353_, 0, v_ref_3380_);
v___x_3385_ = v___x_3353_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_ref_3380_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3385_);
v___x_3387_ = v___x_3378_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3393_; lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3477_; 
v_fst_3393_ = lean_ctor_get(v_b_3339_, 0);
v_snd_3394_ = lean_ctor_get(v_b_3339_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_b_3339_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3396_ = v_b_3339_;
v_isShared_3397_ = v_isSharedCheck_3477_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3393_);
lean_dec(v_b_3339_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3477_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_val_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3476_; 
v_val_3398_ = lean_ctor_get(v_a_3356_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_a_3356_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3400_ = v_a_3356_;
v_isShared_3401_ = v_isSharedCheck_3476_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_val_3398_);
lean_dec(v_a_3356_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3476_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3351_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___y_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
if (lean_obj_tag(v_a_3403_) == 0)
{
lean_inc(v___x_3335_);
v___y_3405_ = v___x_3335_;
goto v___jp_3404_;
}
else
{
lean_object* v_val_3467_; 
v_val_3467_ = lean_ctor_get(v_a_3403_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_a_3403_, 1);
v___y_3405_ = v_val_3467_;
goto v___jp_3404_;
}
v___jp_3404_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3405_);
lean_inc(v_sp_3334_);
v___x_3407_ = l_Lean_SearchPath_findWithExt(v_sp_3334_, v___x_3406_, v___y_3405_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 0)
{
lean_object* v_optName_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v_val_3398_);
lean_dec(v_snd_3394_);
v_optName_3409_ = lean_ctor_get(v_fst_3333_, 1);
v___x_3410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3405_, v___x_3348_);
v___x_3412_ = lean_string_append(v___x_3410_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3414_ = lean_string_append(v___x_3412_, v___x_3413_);
lean_inc(v_optName_3409_);
v___x_3415_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3409_, v___x_3348_);
v___x_3416_ = lean_string_append(v___x_3414_, v___x_3415_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___x_3419_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_dec_ref_known(v___x_3419_, 1);
lean_del_object(v___x_3400_);
lean_del_object(v___x_3353_);
v___x_3420_ = lean_box(v___x_3348_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v___x_3420_);
v___x_3422_ = v___x_3396_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_fst_3393_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v_a_3344_ = v___x_3422_;
goto v___jp_3343_;
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3440_; 
lean_del_object(v___x_3396_);
lean_dec(v_fst_3393_);
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v_a_3424_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3426_ = v___x_3419_;
v_isShared_3427_ = v_isSharedCheck_3440_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3440_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_ref_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
v_ref_3428_ = lean_ctor_get(v___y_3340_, 5);
v___x_3429_ = lean_io_error_to_string(v_a_3424_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 3);
lean_ctor_set(v___x_3400_, 0, v___x_3429_);
v___x_3431_ = v___x_3400_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = l_Lean_MessageData_ofFormat(v___x_3431_);
lean_inc(v_ref_3428_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3432_);
lean_ctor_set(v___x_3353_, 0, v_ref_3428_);
v___x_3434_ = v___x_3353_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_ref_3428_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3436_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3434_);
v___x_3436_ = v___x_3426_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
else
{
lean_object* v_range_3441_; lean_object* v_val_3442_; lean_object* v_pos_3443_; lean_object* v_optName_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec(v___y_3405_);
lean_del_object(v___x_3400_);
lean_del_object(v___x_3353_);
v_range_3441_ = lean_ctor_get(v_val_3398_, 0);
lean_inc_ref(v_range_3441_);
lean_dec(v_val_3398_);
v_val_3442_ = lean_ctor_get(v_a_3408_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v_a_3408_, 1);
v_pos_3443_ = lean_ctor_get(v_range_3441_, 0);
lean_inc_ref(v_pos_3443_);
lean_dec_ref(v_range_3441_);
v_optName_3444_ = lean_ctor_get(v_fst_3333_, 1);
lean_inc(v_optName_3444_);
v___x_3445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3445_, 0, v_val_3442_);
lean_ctor_set(v___x_3445_, 1, v_pos_3443_);
lean_ctor_set(v___x_3445_, 2, v_optName_3444_);
v___x_3446_ = lean_array_push(v_fst_3393_, v___x_3445_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3446_);
v___x_3448_ = v___x_3396_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_snd_3394_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
v_a_3344_ = v___x_3448_;
goto v___jp_3343_;
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v___y_3405_);
lean_dec(v_val_3398_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v_a_3450_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3452_ = v___x_3407_;
v_isShared_3453_ = v_isSharedCheck_3466_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3407_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3466_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_ref_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v_ref_3454_ = lean_ctor_get(v___y_3340_, 5);
v___x_3455_ = lean_io_error_to_string(v_a_3450_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 3);
lean_ctor_set(v___x_3400_, 0, v___x_3455_);
v___x_3457_ = v___x_3400_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_MessageData_ofFormat(v___x_3457_);
lean_inc(v_ref_3454_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3458_);
lean_ctor_set(v___x_3353_, 0, v_ref_3454_);
v___x_3460_ = v___x_3353_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_ref_3454_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3460_);
v___x_3462_ = v___x_3452_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_del_object(v___x_3400_);
lean_dec(v_val_3398_);
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
lean_dec(v_fst_3393_);
lean_del_object(v___x_3353_);
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v_a_3468_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3402_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3402_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_del_object(v___x_3353_);
lean_dec(v_fst_3351_);
lean_dec_ref(v_b_3339_);
lean_dec(v___x_3335_);
lean_dec(v_sp_3334_);
lean_dec_ref(v_fst_3333_);
v_a_3478_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3355_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3355_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
v___jp_3343_:
{
size_t v___x_3345_; size_t v___x_3346_; 
v___x_3345_ = ((size_t)1ULL);
v___x_3346_ = lean_usize_add(v_i_3338_, v___x_3345_);
v_i_3338_ = v___x_3346_;
v_b_3339_ = v_a_3344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3488_, lean_object* v_sp_3489_, lean_object* v___x_3490_, lean_object* v_as_3491_, lean_object* v_sz_3492_, lean_object* v_i_3493_, lean_object* v_b_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
size_t v_sz_boxed_3498_; size_t v_i_boxed_3499_; lean_object* v_res_3500_; 
v_sz_boxed_3498_ = lean_unbox_usize(v_sz_3492_);
lean_dec(v_sz_3492_);
v_i_boxed_3499_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_res_3500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3488_, v_sp_3489_, v___x_3490_, v_as_3491_, v_sz_boxed_3498_, v_i_boxed_3499_, v_b_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_as_3491_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
if (lean_obj_tag(v_x_3502_) == 0)
{
return v_x_3501_;
}
else
{
lean_object* v_key_3503_; lean_object* v_value_3504_; lean_object* v_tail_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_key_3503_ = lean_ctor_get(v_x_3502_, 0);
v_value_3504_ = lean_ctor_get(v_x_3502_, 1);
v_tail_3505_ = lean_ctor_get(v_x_3502_, 2);
lean_inc(v_value_3504_);
lean_inc(v_key_3503_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v_key_3503_);
lean_ctor_set(v___x_3506_, 1, v_value_3504_);
v___x_3507_ = lean_array_push(v_x_3501_, v___x_3506_);
v_x_3501_ = v___x_3507_;
v_x_3502_ = v_tail_3505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3509_, lean_object* v_x_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3509_, v_x_3510_);
lean_dec(v_x_3510_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3512_, size_t v_i_3513_, size_t v_stop_3514_, lean_object* v_b_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_eq(v_i_3513_, v_stop_3514_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; size_t v___x_3519_; size_t v___x_3520_; 
v___x_3517_ = lean_array_uget_borrowed(v_as_3512_, v_i_3513_);
v___x_3518_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3515_, v___x_3517_);
v___x_3519_ = ((size_t)1ULL);
v___x_3520_ = lean_usize_add(v_i_3513_, v___x_3519_);
v_i_3513_ = v___x_3520_;
v_b_3515_ = v___x_3518_;
goto _start;
}
else
{
return v_b_3515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3522_, lean_object* v_i_3523_, lean_object* v_stop_3524_, lean_object* v_b_3525_){
_start:
{
size_t v_i_boxed_3526_; size_t v_stop_boxed_3527_; lean_object* v_res_3528_; 
v_i_boxed_3526_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_stop_boxed_3527_ = lean_unbox_usize(v_stop_3524_);
lean_dec(v_stop_3524_);
v_res_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3522_, v_i_boxed_3526_, v_stop_boxed_3527_, v_b_3525_);
lean_dec_ref(v_as_3522_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3529_, lean_object* v___x_3530_, lean_object* v_as_3531_, size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v___x_3530_);
lean_dec(v_sp_3529_);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_b_3534_);
return v___x_3539_;
}
else
{
lean_object* v_a_3540_; lean_object* v_fst_3541_; lean_object* v_snd_3542_; lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3578_; 
v_a_3540_ = lean_array_uget_borrowed(v_as_3531_, v_i_3533_);
v_fst_3541_ = lean_ctor_get(v_a_3540_, 0);
v_snd_3542_ = lean_ctor_get(v_a_3540_, 1);
v_fst_3543_ = lean_ctor_get(v_b_3534_, 0);
v_snd_3544_ = lean_ctor_get(v_b_3534_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_b_3534_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3546_ = v_b_3534_;
v_isShared_3547_ = v_isSharedCheck_3578_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_snd_3544_);
lean_inc(v_fst_3543_);
lean_dec(v_b_3534_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3578_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___y_3549_; lean_object* v_size_3569_; lean_object* v_buckets_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_size_3569_ = lean_ctor_get(v_snd_3542_, 0);
v_buckets_3570_ = lean_ctor_get(v_snd_3542_, 1);
v___x_3571_ = lean_mk_empty_array_with_capacity(v_size_3569_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3573_ = lean_array_get_size(v_buckets_3570_);
v___x_3574_ = lean_nat_dec_lt(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
v___y_3549_ = v___x_3571_;
goto v___jp_3548_;
}
else
{
size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = ((size_t)0ULL);
v___x_3576_ = lean_usize_of_nat(v___x_3573_);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3570_, v___x_3575_, v___x_3576_, v___x_3571_);
v___y_3549_ = v___x_3577_;
goto v___jp_3548_;
}
v___jp_3548_:
{
lean_object* v___x_3551_; 
if (v_isShared_3547_ == 0)
{
v___x_3551_ = v___x_3546_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_fst_3543_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_snd_3544_);
v___x_3551_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
size_t v_sz_3552_; size_t v___x_3553_; lean_object* v___x_3554_; 
v_sz_3552_ = lean_array_size(v___y_3549_);
v___x_3553_ = ((size_t)0ULL);
lean_inc(v___x_3530_);
lean_inc(v_sp_3529_);
lean_inc(v_fst_3541_);
v___x_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3541_, v_sp_3529_, v___x_3530_, v___y_3549_, v_sz_3552_, v___x_3553_, v___x_3551_, v___y_3535_, v___y_3536_);
lean_dec_ref(v___y_3549_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v_fst_3556_; lean_object* v_snd_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3567_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v_fst_3556_ = lean_ctor_get(v_a_3555_, 0);
v_snd_3557_ = lean_ctor_get(v_a_3555_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3559_ = v_a_3555_;
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snd_3557_);
lean_inc(v_fst_3556_);
lean_dec(v_a_3555_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_fst_3556_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_snd_3557_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
size_t v___x_3563_; size_t v___x_3564_; 
v___x_3563_ = ((size_t)1ULL);
v___x_3564_ = lean_usize_add(v_i_3533_, v___x_3563_);
v_i_3533_ = v___x_3564_;
v_b_3534_ = v___x_3562_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3530_);
lean_dec(v_sp_3529_);
return v___x_3554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3579_, lean_object* v___x_3580_, lean_object* v_as_3581_, lean_object* v_sz_3582_, lean_object* v_i_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_sz_boxed_3588_; size_t v_i_boxed_3589_; lean_object* v_res_3590_; 
v_sz_boxed_3588_ = lean_unbox_usize(v_sz_3582_);
lean_dec(v_sz_3582_);
v_i_boxed_3589_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3579_, v___x_3580_, v_as_3581_, v_sz_boxed_3588_, v_i_boxed_3589_, v_b_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec_ref(v_as_3581_);
return v_res_3590_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3591_, lean_object* v_as_3592_, size_t v_i_3593_, size_t v_stop_3594_){
_start:
{
uint8_t v___x_3595_; 
v___x_3595_ = lean_usize_dec_eq(v_i_3593_, v_stop_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v_snd_3597_; lean_object* v_size_3598_; uint8_t v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3596_ = lean_array_uget_borrowed(v_as_3592_, v_i_3593_);
v_snd_3597_ = lean_ctor_get(v___x_3596_, 1);
v_size_3598_ = lean_ctor_get(v_snd_3597_, 0);
v___x_3599_ = 1;
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = lean_nat_dec_eq(v_size_3598_, v___x_3600_);
if (v___x_3601_ == 0)
{
return v___x_3599_;
}
else
{
if (v___y_3591_ == 0)
{
size_t v___x_3602_; size_t v___x_3603_; 
v___x_3602_ = ((size_t)1ULL);
v___x_3603_ = lean_usize_add(v_i_3593_, v___x_3602_);
v_i_3593_ = v___x_3603_;
goto _start;
}
else
{
return v___x_3599_;
}
}
}
else
{
uint8_t v___x_3605_; 
v___x_3605_ = 0;
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3606_, lean_object* v_as_3607_, lean_object* v_i_3608_, lean_object* v_stop_3609_){
_start:
{
uint8_t v___y_16698__boxed_3610_; size_t v_i_boxed_3611_; size_t v_stop_boxed_3612_; uint8_t v_res_3613_; lean_object* v_r_3614_; 
v___y_16698__boxed_3610_ = lean_unbox(v___y_3606_);
v_i_boxed_3611_ = lean_unbox_usize(v_i_3608_);
lean_dec(v_i_3608_);
v_stop_boxed_3612_ = lean_unbox_usize(v_stop_3609_);
lean_dec(v_stop_3609_);
v_res_3613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16698__boxed_3610_, v_as_3607_, v_i_boxed_3611_, v_stop_boxed_3612_);
lean_dec_ref(v_as_3607_);
v_r_3614_ = lean_box(v_res_3613_);
return v_r_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3615_, lean_object* v_v_3616_, lean_object* v_t_3617_){
_start:
{
lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; 
if (lean_obj_tag(v_t_3617_) == 0)
{
lean_object* v_size_3632_; lean_object* v_k_3633_; lean_object* v_v_3634_; lean_object* v_l_3635_; lean_object* v_r_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3896_; 
v_size_3632_ = lean_ctor_get(v_t_3617_, 0);
v_k_3633_ = lean_ctor_get(v_t_3617_, 1);
v_v_3634_ = lean_ctor_get(v_t_3617_, 2);
v_l_3635_ = lean_ctor_get(v_t_3617_, 3);
v_r_3636_ = lean_ctor_get(v_t_3617_, 4);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_t_3617_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3638_ = v_t_3617_;
v_isShared_3639_ = v_isSharedCheck_3896_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_r_3636_);
lean_inc(v_l_3635_);
lean_inc(v_v_3634_);
lean_inc(v_k_3633_);
lean_inc(v_size_3632_);
lean_dec(v_t_3617_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3896_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; uint8_t v___y_3690_; lean_object* v_fst_3890_; lean_object* v_snd_3891_; lean_object* v_fst_3892_; lean_object* v_snd_3893_; uint8_t v___x_3894_; 
v_fst_3890_ = lean_ctor_get(v_k_3615_, 0);
v_snd_3891_ = lean_ctor_get(v_k_3615_, 1);
v_fst_3892_ = lean_ctor_get(v_k_3633_, 0);
v_snd_3893_ = lean_ctor_get(v_k_3633_, 1);
v___x_3894_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3890_, v_fst_3892_);
if (v___x_3894_ == 1)
{
uint8_t v___x_3895_; 
v___x_3895_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3891_, v_snd_3893_);
v___y_3690_ = v___x_3895_;
goto v___jp_3689_;
}
else
{
v___y_3690_ = v___x_3894_;
goto v___jp_3689_;
}
v___jp_3640_:
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = lean_nat_add(v___y_3643_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec(v___y_3643_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 3, v___y_3641_);
lean_ctor_set(v___x_3638_, 0, v___x_3648_);
v___x_3650_ = v___x_3638_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v___y_3641_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v_r_3636_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3651_, 0, v___y_3645_);
lean_ctor_set(v___x_3651_, 1, v___y_3646_);
lean_ctor_set(v___x_3651_, 2, v___y_3642_);
lean_ctor_set(v___x_3651_, 3, v___y_3644_);
lean_ctor_set(v___x_3651_, 4, v___x_3650_);
return v___x_3651_;
}
}
v___jp_3653_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_nat_add(v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec(v___y_3664_);
v___x_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v___y_3658_);
lean_ctor_set(v___x_3667_, 2, v___y_3657_);
lean_ctor_set(v___x_3667_, 3, v___y_3660_);
lean_ctor_set(v___x_3667_, 4, v___y_3659_);
v___x_3668_ = lean_nat_add(v___y_3661_, v___y_3656_);
lean_dec(v___y_3656_);
if (lean_obj_tag(v___y_3654_) == 0)
{
lean_object* v_size_3669_; 
v_size_3669_ = lean_ctor_get(v___y_3654_, 0);
lean_inc(v_size_3669_);
v___y_3641_ = v___y_3654_;
v___y_3642_ = v___y_3655_;
v___y_3643_ = v___x_3668_;
v___y_3644_ = v___x_3667_;
v___y_3645_ = v___y_3662_;
v___y_3646_ = v___y_3663_;
v___y_3647_ = v_size_3669_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(0u);
v___y_3641_ = v___y_3654_;
v___y_3642_ = v___y_3655_;
v___y_3643_ = v___x_3668_;
v___y_3644_ = v___x_3667_;
v___y_3645_ = v___y_3662_;
v___y_3646_ = v___y_3663_;
v___y_3647_ = v___x_3670_;
goto v___jp_3640_;
}
}
v___jp_3671_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_nat_add(v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec(v___y_3682_);
v___x_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_k_3633_);
lean_ctor_set(v___x_3685_, 2, v_v_3634_);
lean_ctor_set(v___x_3685_, 3, v_l_3635_);
lean_ctor_set(v___x_3685_, 4, v___y_3672_);
v___x_3686_ = lean_nat_add(v___y_3679_, v___y_3673_);
lean_dec(v___y_3673_);
if (lean_obj_tag(v___y_3675_) == 0)
{
lean_object* v_size_3687_; 
v_size_3687_ = lean_ctor_get(v___y_3675_, 0);
lean_inc(v_size_3687_);
v___y_3619_ = v___y_3674_;
v___y_3620_ = v___y_3676_;
v___y_3621_ = v___y_3675_;
v___y_3622_ = v___x_3685_;
v___y_3623_ = v___y_3678_;
v___y_3624_ = v___y_3677_;
v___y_3625_ = v___y_3680_;
v___y_3626_ = v___x_3686_;
v___y_3627_ = v___y_3681_;
v___y_3628_ = v_size_3687_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_unsigned_to_nat(0u);
v___y_3619_ = v___y_3674_;
v___y_3620_ = v___y_3676_;
v___y_3621_ = v___y_3675_;
v___y_3622_ = v___x_3685_;
v___y_3623_ = v___y_3678_;
v___y_3624_ = v___y_3677_;
v___y_3625_ = v___y_3680_;
v___y_3626_ = v___x_3686_;
v___y_3627_ = v___y_3681_;
v___y_3628_ = v___x_3688_;
goto v___jp_3618_;
}
}
v___jp_3689_:
{
switch(v___y_3690_)
{
case 0:
{
lean_object* v_impl_3691_; lean_object* v___x_3692_; 
lean_dec(v_size_3632_);
v_impl_3691_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3615_, v_v_3616_, v_l_3635_);
v___x_3692_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3636_) == 0)
{
lean_object* v_size_3693_; lean_object* v_size_3694_; lean_object* v_k_3695_; lean_object* v_v_3696_; lean_object* v_l_3697_; lean_object* v_r_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v_size_3693_ = lean_ctor_get(v_r_3636_, 0);
v_size_3694_ = lean_ctor_get(v_impl_3691_, 0);
lean_inc(v_size_3694_);
v_k_3695_ = lean_ctor_get(v_impl_3691_, 1);
lean_inc(v_k_3695_);
v_v_3696_ = lean_ctor_get(v_impl_3691_, 2);
lean_inc(v_v_3696_);
v_l_3697_ = lean_ctor_get(v_impl_3691_, 3);
lean_inc(v_l_3697_);
v_r_3698_ = lean_ctor_get(v_impl_3691_, 4);
lean_inc(v_r_3698_);
v___x_3699_ = lean_unsigned_to_nat(3u);
v___x_3700_ = lean_nat_mul(v___x_3699_, v_size_3693_);
v___x_3701_ = lean_nat_dec_lt(v___x_3700_, v_size_3694_);
lean_dec(v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec(v_r_3698_);
lean_dec(v_l_3697_);
lean_dec(v_v_3696_);
lean_dec(v_k_3695_);
lean_del_object(v___x_3638_);
v___x_3702_ = lean_nat_add(v___x_3692_, v_size_3694_);
lean_dec(v_size_3694_);
v___x_3703_ = lean_nat_add(v___x_3702_, v_size_3693_);
lean_dec(v___x_3702_);
v___x_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
lean_ctor_set(v___x_3704_, 1, v_k_3633_);
lean_ctor_set(v___x_3704_, 2, v_v_3634_);
lean_ctor_set(v___x_3704_, 3, v_impl_3691_);
lean_ctor_set(v___x_3704_, 4, v_r_3636_);
return v___x_3704_;
}
else
{
lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3741_; 
v_isSharedCheck_3741_ = !lean_is_exclusive(v_impl_3691_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; 
v_unused_3742_ = lean_ctor_get(v_impl_3691_, 4);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_impl_3691_, 3);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_impl_3691_, 2);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_impl_3691_, 1);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_impl_3691_, 0);
lean_dec(v_unused_3746_);
v___x_3706_ = v_impl_3691_;
v_isShared_3707_ = v_isSharedCheck_3741_;
goto v_resetjp_3705_;
}
else
{
lean_dec(v_impl_3691_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3741_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v_size_3708_; lean_object* v_size_3709_; lean_object* v_k_3710_; lean_object* v_v_3711_; lean_object* v_l_3712_; lean_object* v_r_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_size_3708_ = lean_ctor_get(v_l_3697_, 0);
v_size_3709_ = lean_ctor_get(v_r_3698_, 0);
v_k_3710_ = lean_ctor_get(v_r_3698_, 1);
v_v_3711_ = lean_ctor_get(v_r_3698_, 2);
v_l_3712_ = lean_ctor_get(v_r_3698_, 3);
v_r_3713_ = lean_ctor_get(v_r_3698_, 4);
v___x_3714_ = lean_unsigned_to_nat(2u);
v___x_3715_ = lean_nat_mul(v___x_3714_, v_size_3708_);
v___x_3716_ = lean_nat_dec_lt(v_size_3709_, v___x_3715_);
lean_dec(v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_inc(v_r_3713_);
lean_inc(v_l_3712_);
lean_inc(v_v_3711_);
lean_inc(v_k_3710_);
lean_del_object(v___x_3706_);
lean_dec(v_r_3698_);
v___x_3717_ = lean_nat_add(v___x_3692_, v_size_3694_);
lean_dec(v_size_3694_);
v___x_3718_ = lean_nat_add(v___x_3717_, v_size_3693_);
lean_dec(v___x_3717_);
v___x_3719_ = lean_nat_add(v___x_3692_, v_size_3708_);
if (lean_obj_tag(v_l_3712_) == 0)
{
lean_object* v_size_3720_; 
v_size_3720_ = lean_ctor_get(v_l_3712_, 0);
lean_inc(v_size_3720_);
lean_inc(v_size_3693_);
v___y_3654_ = v_r_3713_;
v___y_3655_ = v_v_3711_;
v___y_3656_ = v_size_3693_;
v___y_3657_ = v_v_3696_;
v___y_3658_ = v_k_3695_;
v___y_3659_ = v_l_3712_;
v___y_3660_ = v_l_3697_;
v___y_3661_ = v___x_3692_;
v___y_3662_ = v___x_3718_;
v___y_3663_ = v_k_3710_;
v___y_3664_ = v___x_3719_;
v___y_3665_ = v_size_3720_;
goto v___jp_3653_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3693_);
v___y_3654_ = v_r_3713_;
v___y_3655_ = v_v_3711_;
v___y_3656_ = v_size_3693_;
v___y_3657_ = v_v_3696_;
v___y_3658_ = v_k_3695_;
v___y_3659_ = v_l_3712_;
v___y_3660_ = v_l_3697_;
v___y_3661_ = v___x_3692_;
v___y_3662_ = v___x_3718_;
v___y_3663_ = v_k_3710_;
v___y_3664_ = v___x_3719_;
v___y_3665_ = v___x_3721_;
goto v___jp_3653_;
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_del_object(v___x_3638_);
v___x_3722_ = lean_nat_add(v___x_3692_, v_size_3694_);
lean_dec(v_size_3694_);
v___x_3723_ = lean_nat_add(v___x_3722_, v_size_3693_);
lean_dec(v___x_3722_);
v___x_3724_ = lean_nat_add(v___x_3692_, v_size_3693_);
v___x_3725_ = lean_nat_add(v___x_3724_, v_size_3709_);
lean_dec(v___x_3724_);
lean_inc_ref(v_r_3636_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 4, v_r_3636_);
lean_ctor_set(v___x_3706_, 3, v_r_3698_);
lean_ctor_set(v___x_3706_, 2, v_v_3634_);
lean_ctor_set(v___x_3706_, 1, v_k_3633_);
lean_ctor_set(v___x_3706_, 0, v___x_3725_);
v___x_3727_ = v___x_3706_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_r_3698_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_r_3636_);
v___x_3727_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
v_isSharedCheck_3734_ = !lean_is_exclusive(v_r_3636_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; 
v_unused_3735_ = lean_ctor_get(v_r_3636_, 4);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_r_3636_, 3);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_r_3636_, 2);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_r_3636_, 1);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_r_3636_, 0);
lean_dec(v_unused_3739_);
v___x_3729_ = v_r_3636_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v_r_3636_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 4, v___x_3727_);
lean_ctor_set(v___x_3729_, 3, v_l_3697_);
lean_ctor_set(v___x_3729_, 2, v_v_3696_);
lean_ctor_set(v___x_3729_, 1, v_k_3695_);
lean_ctor_set(v___x_3729_, 0, v___x_3723_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3695_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3696_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_l_3697_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v___x_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3747_; 
lean_del_object(v___x_3638_);
v_l_3747_ = lean_ctor_get(v_impl_3691_, 3);
lean_inc(v_l_3747_);
if (lean_obj_tag(v_l_3747_) == 0)
{
lean_object* v_r_3748_; lean_object* v_k_3749_; lean_object* v_v_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3759_; 
v_r_3748_ = lean_ctor_get(v_impl_3691_, 4);
v_k_3749_ = lean_ctor_get(v_impl_3691_, 1);
v_v_3750_ = lean_ctor_get(v_impl_3691_, 2);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_impl_3691_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3760_ = lean_ctor_get(v_impl_3691_, 3);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_impl_3691_, 0);
lean_dec(v_unused_3761_);
v___x_3752_ = v_impl_3691_;
v_isShared_3753_ = v_isSharedCheck_3759_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_r_3748_);
lean_inc(v_v_3750_);
lean_inc(v_k_3749_);
lean_dec(v_impl_3691_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3759_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3748_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 3, v_r_3748_);
lean_ctor_set(v___x_3752_, 2, v_v_3634_);
lean_ctor_set(v___x_3752_, 1, v_k_3633_);
lean_ctor_set(v___x_3752_, 0, v___x_3692_);
v___x_3756_ = v___x_3752_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_r_3748_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_r_3748_);
v___x_3756_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3754_);
lean_ctor_set(v___x_3757_, 1, v_k_3749_);
lean_ctor_set(v___x_3757_, 2, v_v_3750_);
lean_ctor_set(v___x_3757_, 3, v_l_3747_);
lean_ctor_set(v___x_3757_, 4, v___x_3756_);
return v___x_3757_;
}
}
}
else
{
lean_object* v_r_3762_; 
v_r_3762_ = lean_ctor_get(v_impl_3691_, 4);
lean_inc(v_r_3762_);
if (lean_obj_tag(v_r_3762_) == 0)
{
lean_object* v_k_3763_; lean_object* v_v_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3785_; 
v_k_3763_ = lean_ctor_get(v_impl_3691_, 1);
v_v_3764_ = lean_ctor_get(v_impl_3691_, 2);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_impl_3691_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; lean_object* v_unused_3787_; lean_object* v_unused_3788_; 
v_unused_3786_ = lean_ctor_get(v_impl_3691_, 4);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_impl_3691_, 3);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_impl_3691_, 0);
lean_dec(v_unused_3788_);
v___x_3766_ = v_impl_3691_;
v_isShared_3767_ = v_isSharedCheck_3785_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_v_3764_);
lean_inc(v_k_3763_);
lean_dec(v_impl_3691_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3785_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v_k_3768_; lean_object* v_v_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3781_; 
v_k_3768_ = lean_ctor_get(v_r_3762_, 1);
v_v_3769_ = lean_ctor_get(v_r_3762_, 2);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_r_3762_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; lean_object* v_unused_3784_; 
v_unused_3782_ = lean_ctor_get(v_r_3762_, 4);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_r_3762_, 3);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_r_3762_, 0);
lean_dec(v_unused_3784_);
v___x_3771_ = v_r_3762_;
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_v_3769_);
lean_inc(v_k_3768_);
lean_dec(v_r_3762_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3781_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3773_ = lean_unsigned_to_nat(3u);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 4, v_l_3747_);
lean_ctor_set(v___x_3771_, 3, v_l_3747_);
lean_ctor_set(v___x_3771_, 2, v_v_3764_);
lean_ctor_set(v___x_3771_, 1, v_k_3763_);
lean_ctor_set(v___x_3771_, 0, v___x_3692_);
v___x_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3763_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3764_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_l_3747_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_l_3747_);
v___x_3775_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 4, v_l_3747_);
lean_ctor_set(v___x_3766_, 2, v_v_3634_);
lean_ctor_set(v___x_3766_, 1, v_k_3633_);
lean_ctor_set(v___x_3766_, 0, v___x_3692_);
v___x_3777_ = v___x_3766_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v_l_3747_);
lean_ctor_set(v_reuseFailAlloc_3779_, 4, v_l_3747_);
v___x_3777_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3773_);
lean_ctor_set(v___x_3778_, 1, v_k_3768_);
lean_ctor_set(v___x_3778_, 2, v_v_3769_);
lean_ctor_set(v___x_3778_, 3, v___x_3775_);
lean_ctor_set(v___x_3778_, 4, v___x_3777_);
return v___x_3778_;
}
}
}
}
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_unsigned_to_nat(2u);
v___x_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v_k_3633_);
lean_ctor_set(v___x_3790_, 2, v_v_3634_);
lean_ctor_set(v___x_3790_, 3, v_impl_3691_);
lean_ctor_set(v___x_3790_, 4, v_r_3762_);
return v___x_3790_;
}
}
}
}
case 1:
{
lean_object* v___x_3791_; 
lean_del_object(v___x_3638_);
lean_dec(v_v_3634_);
lean_dec(v_k_3633_);
v___x_3791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3791_, 0, v_size_3632_);
lean_ctor_set(v___x_3791_, 1, v_k_3615_);
lean_ctor_set(v___x_3791_, 2, v_v_3616_);
lean_ctor_set(v___x_3791_, 3, v_l_3635_);
lean_ctor_set(v___x_3791_, 4, v_r_3636_);
return v___x_3791_;
}
default: 
{
lean_object* v_impl_3792_; lean_object* v___x_3793_; 
lean_del_object(v___x_3638_);
lean_dec(v_size_3632_);
v_impl_3792_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3615_, v_v_3616_, v_r_3636_);
v___x_3793_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3635_) == 0)
{
lean_object* v_size_3794_; lean_object* v_size_3795_; lean_object* v_k_3796_; lean_object* v_v_3797_; lean_object* v_l_3798_; lean_object* v_r_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_size_3794_ = lean_ctor_get(v_l_3635_, 0);
v_size_3795_ = lean_ctor_get(v_impl_3792_, 0);
lean_inc(v_size_3795_);
v_k_3796_ = lean_ctor_get(v_impl_3792_, 1);
lean_inc(v_k_3796_);
v_v_3797_ = lean_ctor_get(v_impl_3792_, 2);
lean_inc(v_v_3797_);
v_l_3798_ = lean_ctor_get(v_impl_3792_, 3);
lean_inc(v_l_3798_);
v_r_3799_ = lean_ctor_get(v_impl_3792_, 4);
lean_inc(v_r_3799_);
v___x_3800_ = lean_unsigned_to_nat(3u);
v___x_3801_ = lean_nat_mul(v___x_3800_, v_size_3794_);
v___x_3802_ = lean_nat_dec_lt(v___x_3801_, v_size_3795_);
lean_dec(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec(v_r_3799_);
lean_dec(v_l_3798_);
lean_dec(v_v_3797_);
lean_dec(v_k_3796_);
v___x_3803_ = lean_nat_add(v___x_3793_, v_size_3794_);
v___x_3804_ = lean_nat_add(v___x_3803_, v_size_3795_);
lean_dec(v_size_3795_);
lean_dec(v___x_3803_);
v___x_3805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
lean_ctor_set(v___x_3805_, 1, v_k_3633_);
lean_ctor_set(v___x_3805_, 2, v_v_3634_);
lean_ctor_set(v___x_3805_, 3, v_l_3635_);
lean_ctor_set(v___x_3805_, 4, v_impl_3792_);
return v___x_3805_;
}
else
{
lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3840_; 
v_isSharedCheck_3840_ = !lean_is_exclusive(v_impl_3792_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; lean_object* v_unused_3844_; lean_object* v_unused_3845_; 
v_unused_3841_ = lean_ctor_get(v_impl_3792_, 4);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_impl_3792_, 3);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_impl_3792_, 2);
lean_dec(v_unused_3843_);
v_unused_3844_ = lean_ctor_get(v_impl_3792_, 1);
lean_dec(v_unused_3844_);
v_unused_3845_ = lean_ctor_get(v_impl_3792_, 0);
lean_dec(v_unused_3845_);
v___x_3807_ = v_impl_3792_;
v_isShared_3808_ = v_isSharedCheck_3840_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v_impl_3792_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3840_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_size_3809_; lean_object* v_k_3810_; lean_object* v_v_3811_; lean_object* v_l_3812_; lean_object* v_r_3813_; lean_object* v_size_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_size_3809_ = lean_ctor_get(v_l_3798_, 0);
v_k_3810_ = lean_ctor_get(v_l_3798_, 1);
v_v_3811_ = lean_ctor_get(v_l_3798_, 2);
v_l_3812_ = lean_ctor_get(v_l_3798_, 3);
v_r_3813_ = lean_ctor_get(v_l_3798_, 4);
v_size_3814_ = lean_ctor_get(v_r_3799_, 0);
v___x_3815_ = lean_unsigned_to_nat(2u);
v___x_3816_ = lean_nat_mul(v___x_3815_, v_size_3814_);
v___x_3817_ = lean_nat_dec_lt(v_size_3809_, v___x_3816_);
lean_dec(v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_inc(v_size_3814_);
lean_inc(v_r_3813_);
lean_inc(v_l_3812_);
lean_inc(v_v_3811_);
lean_inc(v_k_3810_);
lean_del_object(v___x_3807_);
lean_dec(v_l_3798_);
v___x_3818_ = lean_nat_add(v___x_3793_, v_size_3794_);
v___x_3819_ = lean_nat_add(v___x_3818_, v_size_3795_);
lean_dec(v_size_3795_);
if (lean_obj_tag(v_l_3812_) == 0)
{
lean_object* v_size_3820_; 
v_size_3820_ = lean_ctor_get(v_l_3812_, 0);
lean_inc(v_size_3820_);
v___y_3672_ = v_l_3812_;
v___y_3673_ = v_size_3814_;
v___y_3674_ = v_v_3797_;
v___y_3675_ = v_r_3813_;
v___y_3676_ = v_k_3810_;
v___y_3677_ = v_k_3796_;
v___y_3678_ = v_v_3811_;
v___y_3679_ = v___x_3793_;
v___y_3680_ = v___x_3819_;
v___y_3681_ = v_r_3799_;
v___y_3682_ = v___x_3818_;
v___y_3683_ = v_size_3820_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_unsigned_to_nat(0u);
v___y_3672_ = v_l_3812_;
v___y_3673_ = v_size_3814_;
v___y_3674_ = v_v_3797_;
v___y_3675_ = v_r_3813_;
v___y_3676_ = v_k_3810_;
v___y_3677_ = v_k_3796_;
v___y_3678_ = v_v_3811_;
v___y_3679_ = v___x_3793_;
v___y_3680_ = v___x_3819_;
v___y_3681_ = v_r_3799_;
v___y_3682_ = v___x_3818_;
v___y_3683_ = v___x_3821_;
goto v___jp_3671_;
}
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3822_ = lean_nat_add(v___x_3793_, v_size_3794_);
v___x_3823_ = lean_nat_add(v___x_3822_, v_size_3795_);
lean_dec(v_size_3795_);
v___x_3824_ = lean_nat_add(v___x_3822_, v_size_3809_);
lean_dec(v___x_3822_);
lean_inc_ref(v_l_3635_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 4, v_l_3798_);
lean_ctor_set(v___x_3807_, 3, v_l_3635_);
lean_ctor_set(v___x_3807_, 2, v_v_3634_);
lean_ctor_set(v___x_3807_, 1, v_k_3633_);
lean_ctor_set(v___x_3807_, 0, v___x_3824_);
v___x_3826_ = v___x_3807_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3839_, 3, v_l_3635_);
lean_ctor_set(v_reuseFailAlloc_3839_, 4, v_l_3798_);
v___x_3826_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_isSharedCheck_3833_ = !lean_is_exclusive(v_l_3635_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3834_ = lean_ctor_get(v_l_3635_, 4);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_l_3635_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_l_3635_, 2);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_l_3635_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_l_3635_, 0);
lean_dec(v_unused_3838_);
v___x_3828_ = v_l_3635_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_dec(v_l_3635_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 4, v_r_3799_);
lean_ctor_set(v___x_3828_, 3, v___x_3826_);
lean_ctor_set(v___x_3828_, 2, v_v_3797_);
lean_ctor_set(v___x_3828_, 1, v_k_3796_);
lean_ctor_set(v___x_3828_, 0, v___x_3823_);
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3796_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3797_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_r_3799_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3846_; 
v_l_3846_ = lean_ctor_get(v_impl_3792_, 3);
lean_inc(v_l_3846_);
if (lean_obj_tag(v_l_3846_) == 0)
{
lean_object* v_r_3847_; lean_object* v_k_3848_; lean_object* v_v_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3870_; 
v_r_3847_ = lean_ctor_get(v_impl_3792_, 4);
v_k_3848_ = lean_ctor_get(v_impl_3792_, 1);
v_v_3849_ = lean_ctor_get(v_impl_3792_, 2);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_impl_3792_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3871_ = lean_ctor_get(v_impl_3792_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_impl_3792_, 0);
lean_dec(v_unused_3872_);
v___x_3851_ = v_impl_3792_;
v_isShared_3852_ = v_isSharedCheck_3870_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_r_3847_);
lean_inc(v_v_3849_);
lean_inc(v_k_3848_);
lean_dec(v_impl_3792_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3870_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_k_3853_; lean_object* v_v_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3866_; 
v_k_3853_ = lean_ctor_get(v_l_3846_, 1);
v_v_3854_ = lean_ctor_get(v_l_3846_, 2);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_l_3846_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; 
v_unused_3867_ = lean_ctor_get(v_l_3846_, 4);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_l_3846_, 3);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_l_3846_, 0);
lean_dec(v_unused_3869_);
v___x_3856_ = v_l_3846_;
v_isShared_3857_ = v_isSharedCheck_3866_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_v_3854_);
lean_inc(v_k_3853_);
lean_dec(v_l_3846_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3866_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3847_, 2);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 4, v_r_3847_);
lean_ctor_set(v___x_3856_, 3, v_r_3847_);
lean_ctor_set(v___x_3856_, 2, v_v_3634_);
lean_ctor_set(v___x_3856_, 1, v_k_3633_);
lean_ctor_set(v___x_3856_, 0, v___x_3793_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_r_3847_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_r_3847_);
v___x_3860_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3862_; 
lean_inc(v_r_3847_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 3, v_r_3847_);
lean_ctor_set(v___x_3851_, 0, v___x_3793_);
v___x_3862_ = v___x_3851_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3848_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3849_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_r_3847_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_r_3847_);
v___x_3862_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3858_);
lean_ctor_set(v___x_3863_, 1, v_k_3853_);
lean_ctor_set(v___x_3863_, 2, v_v_3854_);
lean_ctor_set(v___x_3863_, 3, v___x_3860_);
lean_ctor_set(v___x_3863_, 4, v___x_3862_);
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_r_3873_; 
v_r_3873_ = lean_ctor_get(v_impl_3792_, 4);
lean_inc(v_r_3873_);
if (lean_obj_tag(v_r_3873_) == 0)
{
lean_object* v_k_3874_; lean_object* v_v_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3884_; 
v_k_3874_ = lean_ctor_get(v_impl_3792_, 1);
v_v_3875_ = lean_ctor_get(v_impl_3792_, 2);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_impl_3792_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; 
v_unused_3885_ = lean_ctor_get(v_impl_3792_, 4);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_impl_3792_, 3);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_impl_3792_, 0);
lean_dec(v_unused_3887_);
v___x_3877_ = v_impl_3792_;
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_v_3875_);
lean_inc(v_k_3874_);
lean_dec(v_impl_3792_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3879_ = lean_unsigned_to_nat(3u);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 4, v_l_3846_);
lean_ctor_set(v___x_3877_, 2, v_v_3634_);
lean_ctor_set(v___x_3877_, 1, v_k_3633_);
lean_ctor_set(v___x_3877_, 0, v___x_3793_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v_l_3846_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v_l_3846_);
v___x_3881_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3879_);
lean_ctor_set(v___x_3882_, 1, v_k_3874_);
lean_ctor_set(v___x_3882_, 2, v_v_3875_);
lean_ctor_set(v___x_3882_, 3, v___x_3881_);
lean_ctor_set(v___x_3882_, 4, v_r_3873_);
return v___x_3882_;
}
}
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_unsigned_to_nat(2u);
v___x_3889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v_k_3633_);
lean_ctor_set(v___x_3889_, 2, v_v_3634_);
lean_ctor_set(v___x_3889_, 3, v_r_3873_);
lean_ctor_set(v___x_3889_, 4, v_impl_3792_);
return v___x_3889_;
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
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v_k_3615_);
lean_ctor_set(v___x_3898_, 2, v_v_3616_);
lean_ctor_set(v___x_3898_, 3, v_t_3617_);
lean_ctor_set(v___x_3898_, 4, v_t_3617_);
return v___x_3898_;
}
v___jp_3618_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_nat_add(v___y_3626_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
v___x_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
lean_ctor_set(v___x_3630_, 1, v___y_3624_);
lean_ctor_set(v___x_3630_, 2, v___y_3619_);
lean_ctor_set(v___x_3630_, 3, v___y_3621_);
lean_ctor_set(v___x_3630_, 4, v___y_3627_);
v___x_3631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3631_, 0, v___y_3625_);
lean_ctor_set(v___x_3631_, 1, v___y_3620_);
lean_ctor_set(v___x_3631_, 2, v___y_3623_);
lean_ctor_set(v___x_3631_, 3, v___y_3622_);
lean_ctor_set(v___x_3631_, 4, v___x_3630_);
return v___x_3631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_3899_, lean_object* v_k_3900_, lean_object* v_fallback_3901_){
_start:
{
if (lean_obj_tag(v_t_3899_) == 0)
{
lean_object* v_k_3902_; lean_object* v_v_3903_; lean_object* v_l_3904_; lean_object* v_r_3905_; uint8_t v___y_3907_; lean_object* v_fst_3910_; lean_object* v_snd_3911_; lean_object* v_fst_3912_; lean_object* v_snd_3913_; uint8_t v___x_3914_; 
v_k_3902_ = lean_ctor_get(v_t_3899_, 1);
v_v_3903_ = lean_ctor_get(v_t_3899_, 2);
v_l_3904_ = lean_ctor_get(v_t_3899_, 3);
v_r_3905_ = lean_ctor_get(v_t_3899_, 4);
v_fst_3910_ = lean_ctor_get(v_k_3900_, 0);
v_snd_3911_ = lean_ctor_get(v_k_3900_, 1);
v_fst_3912_ = lean_ctor_get(v_k_3902_, 0);
v_snd_3913_ = lean_ctor_get(v_k_3902_, 1);
v___x_3914_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3910_, v_fst_3912_);
if (v___x_3914_ == 1)
{
uint8_t v___x_3915_; 
v___x_3915_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3911_, v_snd_3913_);
v___y_3907_ = v___x_3915_;
goto v___jp_3906_;
}
else
{
v___y_3907_ = v___x_3914_;
goto v___jp_3906_;
}
v___jp_3906_:
{
switch(v___y_3907_)
{
case 0:
{
v_t_3899_ = v_l_3904_;
goto _start;
}
case 1:
{
lean_inc(v_v_3903_);
return v_v_3903_;
}
default: 
{
v_t_3899_ = v_r_3905_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_3901_);
return v_fallback_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_3916_, lean_object* v_k_3917_, lean_object* v_fallback_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_3916_, v_k_3917_, v_fallback_3918_);
lean_dec(v_fallback_3918_);
lean_dec_ref(v_k_3917_);
lean_dec(v_t_3916_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_3920_, lean_object* v_as_3921_, size_t v_sz_3922_, size_t v_i_3923_, lean_object* v_b_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_usize_dec_lt(v_i_3923_, v_sz_3922_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec(v___x_3920_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_b_3924_);
return v___x_3929_;
}
else
{
lean_object* v_a_3930_; lean_object* v_fst_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3959_; 
v_a_3930_ = lean_array_uget(v_as_3921_, v_i_3923_);
v_fst_3931_ = lean_ctor_get(v_a_3930_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v_a_3930_, 1);
lean_dec(v_unused_3960_);
v___x_3933_ = v_a_3930_;
v_isShared_3934_ = v_isSharedCheck_3959_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_fst_3931_);
lean_dec(v_a_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3959_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; 
lean_inc(v_fst_3931_);
v___x_3935_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3931_, v___y_3925_, v___y_3926_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; lean_object* v___y_3939_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_3936_) == 0)
{
lean_inc(v___x_3920_);
v___y_3939_ = v___x_3920_;
goto v___jp_3938_;
}
else
{
lean_object* v_val_3950_; 
v_val_3950_ = lean_ctor_get(v_a_3936_, 0);
lean_inc(v_val_3950_);
lean_dec_ref_known(v_a_3936_, 1);
v___y_3939_ = v_val_3950_;
goto v___jp_3938_;
}
v___jp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_fst_3931_);
lean_ctor_set(v___x_3933_, 0, v___y_3939_);
v___x_3941_ = v___x_3933_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___y_3939_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_fst_3931_);
v___x_3941_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; 
v___x_3942_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_3924_, v___x_3941_, v___x_3937_);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_add(v___x_3942_, v___x_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_3941_, v___x_3944_, v_b_3924_);
v___x_3946_ = ((size_t)1ULL);
v___x_3947_ = lean_usize_add(v_i_3923_, v___x_3946_);
v_i_3923_ = v___x_3947_;
v_b_3924_ = v___x_3945_;
goto _start;
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_del_object(v___x_3933_);
lean_dec(v_fst_3931_);
lean_dec(v_b_3924_);
lean_dec(v___x_3920_);
v_a_3951_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3935_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3935_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_3961_, lean_object* v_as_3962_, lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_b_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
size_t v_sz_boxed_3969_; size_t v_i_boxed_3970_; lean_object* v_res_3971_; 
v_sz_boxed_3969_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3970_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_3961_, v_as_3962_, v_sz_boxed_3969_, v_i_boxed_3970_, v_b_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec_ref(v_as_3962_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_3972_, lean_object* v_init_3973_, lean_object* v_x_3974_){
_start:
{
if (lean_obj_tag(v_x_3974_) == 0)
{
lean_object* v_k_3976_; lean_object* v_v_3977_; lean_object* v_l_3978_; lean_object* v_r_3979_; lean_object* v___x_3980_; lean_object* v_a_3981_; lean_object* v_a_3982_; lean_object* v_fst_3983_; lean_object* v_snd_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3999_; 
v_k_3976_ = lean_ctor_get(v_x_3974_, 1);
lean_inc(v_k_3976_);
v_v_3977_ = lean_ctor_get(v_x_3974_, 2);
lean_inc(v_v_3977_);
v_l_3978_ = lean_ctor_get(v_x_3974_, 3);
lean_inc(v_l_3978_);
v_r_3979_ = lean_ctor_get(v_x_3974_, 4);
lean_inc(v_r_3979_);
lean_dec_ref_known(v_x_3974_, 5);
lean_inc_ref(v_fst_3972_);
v___x_3980_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_3972_, v_init_3973_, v_l_3978_);
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
v_a_3982_ = lean_ctor_get(v_a_3981_, 0);
lean_inc(v_a_3982_);
lean_dec(v_a_3981_);
v_fst_3983_ = lean_ctor_get(v_k_3976_, 0);
v_snd_3984_ = lean_ctor_get(v_k_3976_, 1);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_k_3976_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3986_ = v_k_3976_;
v_isShared_3987_ = v_isSharedCheck_3999_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_snd_3984_);
lean_inc(v_fst_3983_);
lean_dec(v_k_3976_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3999_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_optName_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
v_optName_3988_ = lean_ctor_get(v_fst_3972_, 1);
v___x_3989_ = 1;
lean_inc(v_optName_3988_);
v___x_3990_ = l_Lean_Name_toString(v_optName_3988_, v___x_3989_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 1);
v___x_3992_ = v___x_3986_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_fst_3983_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_snd_3984_);
v___x_3992_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
double v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3993_ = lean_float_of_nat(v_v_3977_);
v___x_3994_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_3994_, 0, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3990_);
lean_ctor_set(v___x_3995_, 1, v___x_3992_);
lean_ctor_set(v___x_3995_, 2, v___x_3994_);
v___x_3996_ = lean_array_push(v_a_3982_, v___x_3995_);
v_init_3973_ = v___x_3996_;
v_x_3974_ = v_r_3979_;
goto _start;
}
}
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v_fst_3972_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_init_3973_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4002_, lean_object* v_init_4003_, lean_object* v_x_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4002_, v_init_4003_, v_x_4004_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4007_, lean_object* v_as_4008_, size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_b_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_a_4016_; uint8_t v___x_4020_; 
v___x_4020_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; 
lean_dec(v___x_4007_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v_b_4011_);
return v___x_4021_;
}
else
{
lean_object* v_a_4022_; lean_object* v_snd_4023_; lean_object* v_fst_4024_; lean_object* v_size_4025_; lean_object* v_buckets_4026_; lean_object* v___x_4027_; lean_object* v___y_4029_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_a_4022_ = lean_array_uget_borrowed(v_as_4008_, v_i_4010_);
v_snd_4023_ = lean_ctor_get(v_a_4022_, 1);
v_fst_4024_ = lean_ctor_get(v_a_4022_, 0);
v_size_4025_ = lean_ctor_get(v_snd_4023_, 0);
v_buckets_4026_ = lean_ctor_get(v_snd_4023_, 1);
v___x_4027_ = lean_box(1);
v___x_4063_ = lean_mk_empty_array_with_capacity(v_size_4025_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = lean_array_get_size(v_buckets_4026_);
v___x_4066_ = lean_nat_dec_lt(v___x_4064_, v___x_4065_);
if (v___x_4066_ == 0)
{
v___y_4029_ = v___x_4063_;
goto v___jp_4028_;
}
else
{
size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((size_t)0ULL);
v___x_4068_ = lean_usize_of_nat(v___x_4065_);
v___x_4069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4026_, v___x_4067_, v___x_4068_, v___x_4063_);
v___y_4029_ = v___x_4069_;
goto v___jp_4028_;
}
v___jp_4028_:
{
size_t v_sz_4030_; size_t v___x_4031_; lean_object* v___x_4032_; 
v_sz_4030_ = lean_array_size(v___y_4029_);
v___x_4031_ = ((size_t)0ULL);
lean_inc(v___x_4007_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4007_, v___y_4029_, v_sz_4030_, v___x_4031_, v___x_4027_, v___y_4012_, v___y_4013_);
lean_dec_ref(v___y_4029_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
lean_inc(v_fst_4024_);
v___x_4034_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4024_, v_b_4011_, v_a_4033_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v_a_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v_a_4036_ = lean_ctor_get(v_a_4035_, 0);
lean_inc(v_a_4036_);
lean_dec(v_a_4035_);
v_a_4016_ = v_a_4036_;
goto v___jp_4015_;
}
else
{
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4046_; 
v_a_4037_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4039_ = v___x_4034_;
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4034_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_a_4037_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; 
lean_dec(v___x_4007_);
v_a_4041_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v_a_4037_, 1);
if (v_isShared_4040_ == 0)
{
lean_ctor_set_tag(v___x_4039_, 0);
lean_ctor_set(v___x_4039_, 0, v_a_4041_);
v___x_4043_ = v___x_4039_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
else
{
lean_object* v_a_4045_; 
lean_del_object(v___x_4039_);
v_a_4045_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v_a_4037_, 1);
v_a_4016_ = v_a_4045_;
goto v___jp_4015_;
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v___x_4007_);
v_a_4047_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4034_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4034_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_b_4011_);
lean_dec(v___x_4007_);
v_a_4055_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4032_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4032_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
v___jp_4015_:
{
size_t v___x_4017_; size_t v___x_4018_; 
v___x_4017_ = ((size_t)1ULL);
v___x_4018_ = lean_usize_add(v_i_4010_, v___x_4017_);
v_i_4010_ = v___x_4018_;
v_b_4011_ = v_a_4016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4070_, lean_object* v_as_4071_, lean_object* v_sz_4072_, lean_object* v_i_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
size_t v_sz_boxed_4078_; size_t v_i_boxed_4079_; lean_object* v_res_4080_; 
v_sz_boxed_4078_ = lean_unbox_usize(v_sz_4072_);
lean_dec(v_sz_4072_);
v_i_boxed_4079_ = lean_unbox_usize(v_i_4073_);
lean_dec(v_i_4073_);
v_res_4080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4070_, v_as_4071_, v_sz_boxed_4078_, v_i_boxed_4079_, v_b_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec_ref(v_as_4071_);
return v_res_4080_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = l_Lean_maxRecDepth;
v___x_4088_ = l_Lean_Options_empty;
v___x_4089_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4088_, v___x_4087_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4090_, lean_object* v_linterOpts_4091_, lean_object* v_sp_4092_, lean_object* v_env_4093_, lean_object* v_mod_4094_){
_start:
{
lean_object* v_msg_4097_; lean_object* v_a_4102_; lean_object* v_a_4106_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v_a_4137_; lean_object* v___y_4141_; lean_object* v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4221_; lean_object* v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_env_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; lean_object* v_fileName_4279_; lean_object* v_fileMap_4280_; lean_object* v_currRecDepth_4281_; lean_object* v_ref_4282_; lean_object* v_currNamespace_4283_; lean_object* v_openDecls_4284_; lean_object* v_initHeartbeats_4285_; lean_object* v_maxHeartbeats_4286_; lean_object* v_quotContext_4287_; lean_object* v_currMacroScope_4288_; lean_object* v_cancelTk_x3f_4289_; uint8_t v_suppressElabErrors_4290_; lean_object* v_inheritedTraceOptions_4291_; lean_object* v___y_4292_; uint8_t v___y_4308_; uint8_t v___x_4328_; 
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4122_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4123_ = lean_io_get_num_heartbeats();
v___x_4124_ = l_Lean_firstFrontendMacroScope;
v___x_4125_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4126_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4127_ = lean_box(0);
v___x_4128_ = lean_box(0);
v___x_4129_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4130_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4131_ = 1;
v___x_4132_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4133_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4134_, 0, v_env_4093_);
lean_ctor_set(v___x_4134_, 1, v___x_4125_);
lean_ctor_set(v___x_4134_, 2, v___x_4126_);
lean_ctor_set(v___x_4134_, 3, v___x_4129_);
lean_ctor_set(v___x_4134_, 4, v___x_4130_);
lean_ctor_set(v___x_4134_, 5, v___x_4121_);
lean_ctor_set(v___x_4134_, 6, v___x_4122_);
lean_ctor_set(v___x_4134_, 7, v___x_4132_);
lean_ctor_set(v___x_4134_, 8, v___x_4133_);
v___x_4135_ = lean_st_mk_ref(v___x_4134_);
v___x_4235_ = l_Lean_inheritedTraceOptions;
v___x_4236_ = lean_st_ref_get(v___x_4235_);
v___x_4237_ = lean_st_ref_get(v___x_4135_);
v_env_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc_ref(v_env_4238_);
lean_dec(v___x_4237_);
v___x_4239_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4240_ = l_Lean_instInhabitedFileMap_default;
v___x_4241_ = l_Lean_Options_empty;
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4244_ = 0;
v___x_4275_ = lean_box(0);
v___x_4276_ = l_Lean_Name_getRoot(v_mod_4094_);
v___x_4277_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4328_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4238_);
lean_dec_ref(v_env_4238_);
if (v___x_4277_ == 0)
{
if (v___x_4328_ == 0)
{
lean_inc(v___x_4135_);
v_fileName_4279_ = v___x_4239_;
v_fileMap_4280_ = v___x_4240_;
v_currRecDepth_4281_ = v___x_4120_;
v_ref_4282_ = v___x_4242_;
v_currNamespace_4283_ = v___x_4127_;
v_openDecls_4284_ = v___x_4128_;
v_initHeartbeats_4285_ = v___x_4123_;
v_maxHeartbeats_4286_ = v___x_4243_;
v_quotContext_4287_ = v___x_4127_;
v_currMacroScope_4288_ = v___x_4124_;
v_cancelTk_x3f_4289_ = v___x_4275_;
v_suppressElabErrors_4290_ = v___x_4244_;
v_inheritedTraceOptions_4291_ = v___x_4236_;
v___y_4292_ = v___x_4135_;
goto v___jp_4278_;
}
else
{
v___y_4308_ = v___x_4277_;
goto v___jp_4307_;
}
}
else
{
v___y_4308_ = v___x_4328_;
goto v___jp_4307_;
}
v___jp_4096_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = l_Lean_MessageData_toString(v_msg_4097_);
v___x_4099_ = lean_mk_io_user_error(v___x_4098_);
v___x_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
v___jp_4101_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_mk_io_user_error(v_a_4102_);
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
v___jp_4105_:
{
if (lean_obj_tag(v_a_4106_) == 0)
{
lean_object* v_msg_4107_; 
v_msg_4107_ = lean_ctor_get(v_a_4106_, 1);
lean_inc_ref(v_msg_4107_);
lean_dec_ref_known(v_a_4106_, 2);
v_msg_4097_ = v_msg_4107_;
goto v___jp_4096_;
}
else
{
lean_object* v_id_4108_; lean_object* v___x_4109_; 
v_id_4108_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_id_4108_);
lean_dec_ref_known(v_a_4106_, 2);
v___x_4109_ = l_Lean_InternalExceptionId_getName(v_id_4108_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec(v_id_4108_);
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4111_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4112_ = 1;
v___x_4113_ = l_Lean_Name_toString(v_a_4110_, v___x_4112_);
v___x_4114_ = lean_string_append(v___x_4111_, v___x_4113_);
lean_dec_ref(v___x_4113_);
v_a_4102_ = v___x_4114_;
goto v___jp_4101_;
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec_ref_known(v___x_4109_, 1);
v___x_4115_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4116_ = l_Nat_reprFast(v_id_4108_);
v___x_4117_ = lean_string_append(v___x_4115_, v___x_4116_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4119_ = lean_string_append(v___x_4117_, v___x_4118_);
v_a_4102_ = v___x_4119_;
goto v___jp_4101_;
}
}
}
v___jp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_st_ref_get(v___x_4135_);
lean_dec(v___x_4135_);
lean_dec(v___x_4138_);
v___x_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4139_, 0, v_a_4137_);
return v___x_4139_;
}
v___jp_4140_:
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___y_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___y_4141_);
v_a_4137_ = v_a_4142_;
goto v___jp_4136_;
}
v___jp_4143_:
{
switch(v___y_4146_)
{
case 0:
{
lean_dec(v_sp_4092_);
if (v___y_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec_ref(v___y_4144_);
v___x_4152_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4094_, v___x_4131_);
v___x_4154_ = lean_string_append(v___x_4152_, v___x_4153_);
lean_dec_ref(v___x_4153_);
v___x_4155_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4156_ = lean_string_append(v___x_4154_, v___x_4155_);
v___x_4157_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4151_, v_a_4158_, v___y_4150_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4150_);
v___y_4141_ = v___x_4159_;
goto v___jp_4140_;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4145_);
lean_dec(v___x_4135_);
v_a_4160_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4162_ = v___x_4157_;
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4157_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4169_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4164_ = lean_io_error_to_string(v_a_4160_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set_tag(v___x_4162_, 3);
lean_ctor_set(v___x_4162_, 0, v___x_4164_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Lean_MessageData_ofFormat(v___x_4166_);
v_msg_4097_ = v___x_4167_;
goto v___jp_4096_;
}
}
}
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4170_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4094_, v___y_4151_);
v___x_4172_ = lean_string_append(v___x_4170_, v___x_4171_);
lean_dec_ref(v___x_4171_);
v___x_4173_ = lean_array_get_size(v___y_4149_);
lean_dec_ref(v___y_4149_);
v___x_4174_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4148_, v___y_4144_, v___x_4131_, v___x_4172_, v___x_4173_, v___x_4131_, v___y_4150_, v___y_4145_);
lean_dec_ref(v___y_4144_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = l_Lean_MessageData_toString(v_a_4175_);
v___x_4177_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v___x_4179_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4151_, v_a_4178_, v___y_4150_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4150_);
v___y_4141_ = v___x_4179_;
goto v___jp_4140_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4145_);
lean_dec(v___x_4135_);
v_a_4180_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4182_ = v___x_4177_;
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4177_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___x_4184_ = lean_io_error_to_string(v_a_4180_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set_tag(v___x_4182_, 3);
lean_ctor_set(v___x_4182_, 0, v___x_4184_);
v___x_4186_ = v___x_4182_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_MessageData_ofFormat(v___x_4186_);
v_msg_4097_ = v___x_4187_;
goto v___jp_4096_;
}
}
}
}
else
{
lean_object* v_a_4190_; 
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4145_);
lean_dec(v___x_4135_);
v_a_4190_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4174_, 1);
v_a_4106_ = v_a_4190_;
goto v___jp_4105_;
}
}
}
case 1:
{
lean_object* v___x_4191_; lean_object* v_env_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; size_t v_sz_4196_; size_t v___x_4197_; lean_object* v___x_4198_; 
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4144_);
lean_dec(v_mod_4094_);
v___x_4191_ = lean_st_ref_get(v___y_4145_);
v_env_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc_ref(v_env_4192_);
lean_dec(v___x_4191_);
v___x_4193_ = l_Lean_Environment_mainModule(v_env_4192_);
lean_dec_ref(v_env_4192_);
v___x_4194_ = lean_box(v___y_4147_);
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4133_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v_sz_4196_ = lean_array_size(v___y_4148_);
v___x_4197_ = ((size_t)0ULL);
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4092_, v___x_4193_, v___y_4148_, v_sz_4196_, v___x_4197_, v___x_4195_, v___y_4150_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v___y_4148_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v_fst_4200_; lean_object* v_snd_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v_fst_4200_ = lean_ctor_get(v_a_4199_, 0);
lean_inc(v_fst_4200_);
v_snd_4201_ = lean_ctor_get(v_a_4199_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_a_4199_);
v___x_4202_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4202_, 0, v_fst_4200_);
v___x_4203_ = lean_unbox(v_snd_4201_);
lean_dec(v_snd_4201_);
lean_ctor_set_uint8(v___x_4202_, sizeof(void*)*1, v___x_4203_);
v_a_4137_ = v___x_4202_;
goto v___jp_4136_;
}
else
{
lean_object* v_a_4204_; 
lean_dec(v___x_4135_);
v_a_4204_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4198_, 1);
v_a_4106_ = v_a_4204_;
goto v___jp_4105_;
}
}
default: 
{
lean_object* v___x_4205_; lean_object* v_env_4206_; lean_object* v___x_4207_; size_t v_sz_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4144_);
lean_dec(v_mod_4094_);
lean_dec(v_sp_4092_);
v___x_4205_ = lean_st_ref_get(v___y_4145_);
v_env_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc_ref(v_env_4206_);
lean_dec(v___x_4205_);
v___x_4207_ = l_Lean_Environment_mainModule(v_env_4206_);
lean_dec_ref(v_env_4206_);
v_sz_4208_ = lean_array_size(v___y_4148_);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4207_, v___y_4148_, v_sz_4208_, v___x_4209_, v___x_4133_, v___y_4150_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v___y_4148_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
lean_ctor_set_tag(v___x_4213_, 2);
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
v_a_4137_ = v___x_4216_;
goto v___jp_4136_;
}
}
}
else
{
lean_object* v_a_4219_; 
lean_dec(v___x_4135_);
v_a_4219_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4219_);
lean_dec_ref_known(v___x_4210_, 1);
v_a_4106_ = v_a_4219_;
goto v___jp_4105_;
}
}
}
}
v___jp_4220_:
{
lean_object* v___x_4227_; 
lean_inc_ref(v___y_4224_);
v___x_4227_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4221_, v___y_4224_, v___y_4225_, v___y_4222_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = lean_array_get_size(v_a_4228_);
v___x_4230_ = lean_nat_dec_lt(v___x_4120_, v___x_4229_);
if (v___x_4230_ == 0)
{
v___y_4144_ = v___y_4221_;
v___y_4145_ = v___y_4222_;
v___y_4146_ = v___y_4223_;
v___y_4147_ = v___y_4226_;
v___y_4148_ = v_a_4228_;
v___y_4149_ = v___y_4224_;
v___y_4150_ = v___y_4225_;
v___y_4151_ = v___x_4230_;
goto v___jp_4143_;
}
else
{
if (v___x_4230_ == 0)
{
v___y_4144_ = v___y_4221_;
v___y_4145_ = v___y_4222_;
v___y_4146_ = v___y_4223_;
v___y_4147_ = v___y_4226_;
v___y_4148_ = v_a_4228_;
v___y_4149_ = v___y_4224_;
v___y_4150_ = v___y_4225_;
v___y_4151_ = v___x_4230_;
goto v___jp_4143_;
}
else
{
size_t v___x_4231_; size_t v___x_4232_; uint8_t v___x_4233_; 
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = lean_usize_of_nat(v___x_4229_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4226_, v_a_4228_, v___x_4231_, v___x_4232_);
v___y_4144_ = v___y_4221_;
v___y_4145_ = v___y_4222_;
v___y_4146_ = v___y_4223_;
v___y_4147_ = v___y_4226_;
v___y_4148_ = v_a_4228_;
v___y_4149_ = v___y_4224_;
v___y_4150_ = v___y_4225_;
v___y_4151_ = v___x_4233_;
goto v___jp_4143_;
}
}
}
else
{
lean_object* v_a_4234_; 
lean_dec_ref(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___x_4135_);
lean_dec(v_mod_4094_);
lean_dec(v_sp_4092_);
v_a_4234_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4227_, 1);
v_a_4106_ = v_a_4234_;
goto v___jp_4105_;
}
}
v___jp_4245_:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4250_, v___y_4249_, v___y_4247_);
lean_dec(v___y_4250_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
v___x_4253_ = lean_array_get_size(v_a_4252_);
v___x_4254_ = lean_nat_dec_eq(v___x_4253_, v___x_4120_);
if (v___x_4254_ == 0)
{
v___y_4221_ = v___y_4246_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v_a_4252_;
v___y_4225_ = v___y_4249_;
v___y_4226_ = v___x_4254_;
goto v___jp_4220_;
}
else
{
uint8_t v___x_4255_; uint8_t v___x_4256_; 
v___x_4255_ = 0;
v___x_4256_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4248_, v___x_4255_);
if (v___x_4256_ == 0)
{
v___y_4221_ = v___y_4246_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v_a_4252_;
v___y_4225_ = v___y_4249_;
v___y_4226_ = v___x_4256_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_dec(v_a_4252_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v_sp_4092_);
v___x_4257_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4094_, v___x_4256_);
v___x_4259_ = lean_string_append(v___x_4257_, v___x_4258_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4261_ = lean_string_append(v___x_4259_, v___x_4260_);
v___x_4262_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4261_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v___x_4263_; 
lean_dec_ref_known(v___x_4262_, 1);
v___x_4263_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4137_ = v___x_4263_;
goto v___jp_4136_;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v___x_4135_);
v_a_4264_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4266_ = v___x_4262_;
v_isShared_4267_ = v_isSharedCheck_4273_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4262_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4273_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_io_error_to_string(v_a_4264_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 3);
lean_ctor_set(v___x_4266_, 0, v___x_4268_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_MessageData_ofFormat(v___x_4270_);
v_msg_4097_ = v___x_4271_;
goto v___jp_4096_;
}
}
}
}
}
}
else
{
lean_object* v_a_4274_; 
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___x_4135_);
lean_dec(v_mod_4094_);
lean_dec(v_sp_4092_);
v_a_4274_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4251_, 1);
v_a_4106_ = v_a_4274_;
goto v___jp_4105_;
}
}
v___jp_4278_:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4276_, v___y_4292_);
lean_dec(v___x_4276_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4305_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4296_ = v___x_4293_;
v_isShared_4297_ = v_isSharedCheck_4305_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4305_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
uint8_t v_lintOnly_4298_; uint8_t v_mode_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_lintOnly_4298_ = lean_ctor_get_uint8(v_args_4090_, sizeof(void*)*4);
v_mode_4299_ = lean_ctor_get_uint8(v_args_4090_, sizeof(void*)*4 + 1);
v___x_4300_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4288_);
lean_inc(v_quotContext_4287_);
lean_inc(v_maxHeartbeats_4286_);
lean_inc(v_openDecls_4284_);
lean_inc(v_currNamespace_4283_);
lean_inc(v_ref_4282_);
lean_inc_ref(v_fileMap_4280_);
lean_inc_ref(v_fileName_4279_);
v___x_4301_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4301_, 0, v_fileName_4279_);
lean_ctor_set(v___x_4301_, 1, v_fileMap_4280_);
lean_ctor_set(v___x_4301_, 2, v___x_4241_);
lean_ctor_set(v___x_4301_, 3, v_currRecDepth_4281_);
lean_ctor_set(v___x_4301_, 4, v___x_4300_);
lean_ctor_set(v___x_4301_, 5, v_ref_4282_);
lean_ctor_set(v___x_4301_, 6, v_currNamespace_4283_);
lean_ctor_set(v___x_4301_, 7, v_openDecls_4284_);
lean_ctor_set(v___x_4301_, 8, v_initHeartbeats_4285_);
lean_ctor_set(v___x_4301_, 9, v_maxHeartbeats_4286_);
lean_ctor_set(v___x_4301_, 10, v_quotContext_4287_);
lean_ctor_set(v___x_4301_, 11, v_currMacroScope_4288_);
lean_ctor_set(v___x_4301_, 12, v_cancelTk_x3f_4289_);
lean_ctor_set(v___x_4301_, 13, v_inheritedTraceOptions_4291_);
lean_ctor_set_uint8(v___x_4301_, sizeof(void*)*14, v___x_4277_);
lean_ctor_set_uint8(v___x_4301_, sizeof(void*)*14 + 1, v_suppressElabErrors_4290_);
if (v_lintOnly_4298_ == 0)
{
lean_del_object(v___x_4296_);
lean_dec_ref(v_linterOpts_4091_);
v___y_4246_ = v_a_4294_;
v___y_4247_ = v___y_4292_;
v___y_4248_ = v_mode_4299_;
v___y_4249_ = v___x_4301_;
v___y_4250_ = v___x_4275_;
goto v___jp_4245_;
}
else
{
lean_object* v___x_4303_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 1);
lean_ctor_set(v___x_4296_, 0, v_linterOpts_4091_);
v___x_4303_ = v___x_4296_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_linterOpts_4091_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v___y_4246_ = v_a_4294_;
v___y_4247_ = v___y_4292_;
v___y_4248_ = v_mode_4299_;
v___y_4249_ = v___x_4301_;
v___y_4250_ = v___x_4303_;
goto v___jp_4245_;
}
}
}
}
else
{
lean_object* v_a_4306_; 
lean_dec(v___y_4292_);
lean_dec_ref(v_inheritedTraceOptions_4291_);
lean_dec(v_cancelTk_x3f_4289_);
lean_dec(v_initHeartbeats_4285_);
lean_dec(v_currRecDepth_4281_);
lean_dec(v___x_4135_);
lean_dec(v_mod_4094_);
lean_dec(v_sp_4092_);
lean_dec_ref(v_linterOpts_4091_);
v_a_4306_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4293_, 1);
v_a_4106_ = v_a_4306_;
goto v___jp_4105_;
}
}
v___jp_4307_:
{
if (v___y_4308_ == 0)
{
lean_object* v___x_4309_; lean_object* v_env_4310_; lean_object* v_nextMacroScope_4311_; lean_object* v_ngen_4312_; lean_object* v_auxDeclNGen_4313_; lean_object* v_traceState_4314_; lean_object* v_messages_4315_; lean_object* v_infoState_4316_; lean_object* v_snapshotTasks_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4326_; 
v___x_4309_ = lean_st_ref_take(v___x_4135_);
v_env_4310_ = lean_ctor_get(v___x_4309_, 0);
v_nextMacroScope_4311_ = lean_ctor_get(v___x_4309_, 1);
v_ngen_4312_ = lean_ctor_get(v___x_4309_, 2);
v_auxDeclNGen_4313_ = lean_ctor_get(v___x_4309_, 3);
v_traceState_4314_ = lean_ctor_get(v___x_4309_, 4);
v_messages_4315_ = lean_ctor_get(v___x_4309_, 6);
v_infoState_4316_ = lean_ctor_get(v___x_4309_, 7);
v_snapshotTasks_4317_ = lean_ctor_get(v___x_4309_, 8);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v___x_4309_, 5);
lean_dec(v_unused_4327_);
v___x_4319_ = v___x_4309_;
v_isShared_4320_ = v_isSharedCheck_4326_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_snapshotTasks_4317_);
lean_inc(v_infoState_4316_);
lean_inc(v_messages_4315_);
lean_inc(v_traceState_4314_);
lean_inc(v_auxDeclNGen_4313_);
lean_inc(v_ngen_4312_);
lean_inc(v_nextMacroScope_4311_);
lean_inc(v_env_4310_);
lean_dec(v___x_4309_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4326_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4321_ = l_Lean_Kernel_enableDiag(v_env_4310_, v___x_4277_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 5, v___x_4121_);
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4323_ = v___x_4319_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_nextMacroScope_4311_);
lean_ctor_set(v_reuseFailAlloc_4325_, 2, v_ngen_4312_);
lean_ctor_set(v_reuseFailAlloc_4325_, 3, v_auxDeclNGen_4313_);
lean_ctor_set(v_reuseFailAlloc_4325_, 4, v_traceState_4314_);
lean_ctor_set(v_reuseFailAlloc_4325_, 5, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4325_, 6, v_messages_4315_);
lean_ctor_set(v_reuseFailAlloc_4325_, 7, v_infoState_4316_);
lean_ctor_set(v_reuseFailAlloc_4325_, 8, v_snapshotTasks_4317_);
v___x_4323_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; 
v___x_4324_ = lean_st_ref_put(v___x_4135_, v___x_4323_);
lean_inc(v___x_4135_);
v_fileName_4279_ = v___x_4239_;
v_fileMap_4280_ = v___x_4240_;
v_currRecDepth_4281_ = v___x_4120_;
v_ref_4282_ = v___x_4242_;
v_currNamespace_4283_ = v___x_4127_;
v_openDecls_4284_ = v___x_4128_;
v_initHeartbeats_4285_ = v___x_4123_;
v_maxHeartbeats_4286_ = v___x_4243_;
v_quotContext_4287_ = v___x_4127_;
v_currMacroScope_4288_ = v___x_4124_;
v_cancelTk_x3f_4289_ = v___x_4275_;
v_suppressElabErrors_4290_ = v___x_4244_;
v_inheritedTraceOptions_4291_ = v___x_4236_;
v___y_4292_ = v___x_4135_;
goto v___jp_4278_;
}
}
}
else
{
lean_inc(v___x_4135_);
v_fileName_4279_ = v___x_4239_;
v_fileMap_4280_ = v___x_4240_;
v_currRecDepth_4281_ = v___x_4120_;
v_ref_4282_ = v___x_4242_;
v_currNamespace_4283_ = v___x_4127_;
v_openDecls_4284_ = v___x_4128_;
v_initHeartbeats_4285_ = v___x_4123_;
v_maxHeartbeats_4286_ = v___x_4243_;
v_quotContext_4287_ = v___x_4127_;
v_currMacroScope_4288_ = v___x_4124_;
v_cancelTk_x3f_4289_ = v___x_4275_;
v_suppressElabErrors_4290_ = v___x_4244_;
v_inheritedTraceOptions_4291_ = v___x_4236_;
v___y_4292_ = v___x_4135_;
goto v___jp_4278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4329_, lean_object* v_linterOpts_4330_, lean_object* v_sp_4331_, lean_object* v_env_4332_, lean_object* v_mod_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4329_, v_linterOpts_4330_, v_sp_4331_, v_env_4332_, v_mod_4333_);
lean_dec_ref(v_args_4329_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4336_, lean_object* v_t_4337_, lean_object* v_k_4338_, lean_object* v_fallback_4339_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4337_, v_k_4338_, v_fallback_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4341_, lean_object* v_t_4342_, lean_object* v_k_4343_, lean_object* v_fallback_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4341_, v_t_4342_, v_k_4343_, v_fallback_4344_);
lean_dec(v_fallback_4344_);
lean_dec_ref(v_k_4343_);
lean_dec(v_t_4342_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4346_, lean_object* v_k_4347_, lean_object* v_v_4348_, lean_object* v_t_4349_, lean_object* v_hl_4350_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4347_, v_v_4348_, v_t_4349_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4352_, lean_object* v_init_4353_, lean_object* v_x_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4352_, v_init_4353_, v_x_4354_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4359_, lean_object* v_init_4360_, lean_object* v_x_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4359_, v_init_4360_, v_x_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4366_, lean_object* v_constName_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4367_, v___y_4368_, v___y_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4372_, lean_object* v_constName_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4372_, v_constName_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4378_, lean_object* v_ref_4379_, lean_object* v_constName_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4379_, v_constName_4380_, v___y_4381_, v___y_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4385_, lean_object* v_ref_4386_, lean_object* v_constName_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4385_, v_ref_4386_, v_constName_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v_ref_4386_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4392_, lean_object* v_ref_4393_, lean_object* v_msg_4394_, lean_object* v_declHint_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4393_, v_msg_4394_, v_declHint_4395_, v___y_4396_, v___y_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4400_, lean_object* v_ref_4401_, lean_object* v_msg_4402_, lean_object* v_declHint_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4400_, v_ref_4401_, v_msg_4402_, v_declHint_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v_ref_4401_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4408_, lean_object* v_declHint_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4408_, v_declHint_4409_, v___y_4411_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4414_, lean_object* v_declHint_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4414_, v_declHint_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4420_, lean_object* v_ref_4421_, lean_object* v_msg_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4421_, v_msg_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_ref_4428_, lean_object* v_msg_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4427_, v_ref_4428_, v_msg_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v_ref_4428_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4434_, lean_object* v_msg_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4435_, v___y_4436_, v___y_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_msg_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4440_, v_msg_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; uint32_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4448_ = l_Std_Format_defWidth;
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = l_Std_Format_pretty(v_s_4446_, v___x_4448_, v___x_4449_, v___x_4449_);
v___x_4451_ = 10;
v___x_4452_ = lean_string_push(v___x_4450_, v___x_4451_);
v___x_4453_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4457_, size_t v_sz_4458_, size_t v_i_4459_, lean_object* v_b_4460_, lean_object* v___y_4461_){
_start:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_usize_dec_lt(v_i_4459_, v_sz_4458_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v_b_4460_);
return v___x_4464_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v_a_4465_ = lean_array_uget_borrowed(v_as_4457_, v_i_4459_);
v___x_4466_ = lean_box(0);
lean_inc(v_a_4465_);
v___x_4467_ = l_Lean_MessageData_format(v_a_4465_, v___x_4466_);
v___x_4468_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4467_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v___x_4469_; size_t v___x_4470_; size_t v___x_4471_; 
lean_dec_ref_known(v___x_4468_, 1);
v___x_4469_ = lean_box(0);
v___x_4470_ = ((size_t)1ULL);
v___x_4471_ = lean_usize_add(v_i_4459_, v___x_4470_);
v_i_4459_ = v___x_4471_;
v_b_4460_ = v___x_4469_;
goto _start;
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4485_; 
v_a_4473_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4475_ = v___x_4468_;
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4468_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_ref_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v_ref_4477_ = lean_ctor_get(v___y_4461_, 5);
v___x_4478_ = lean_io_error_to_string(v_a_4473_);
v___x_4479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
v___x_4480_ = l_Lean_MessageData_ofFormat(v___x_4479_);
lean_inc(v_ref_4477_);
v___x_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4481_, 0, v_ref_4477_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v___x_4481_);
v___x_4483_ = v___x_4475_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4486_, lean_object* v_sz_4487_, lean_object* v_i_4488_, lean_object* v_b_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
size_t v_sz_boxed_4492_; size_t v_i_boxed_4493_; lean_object* v_res_4494_; 
v_sz_boxed_4492_ = lean_unbox_usize(v_sz_4487_);
lean_dec(v_sz_4487_);
v_i_boxed_4493_ = lean_unbox_usize(v_i_4488_);
lean_dec(v_i_4488_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4486_, v_sz_boxed_4492_, v_i_boxed_4493_, v_b_4489_, v___y_4490_);
lean_dec_ref(v___y_4490_);
lean_dec_ref(v_as_4486_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4495_, lean_object* v_entries_4496_, lean_object* v_____r_4497_, uint8_t v_anyFailed_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; size_t v_sz_4503_; size_t v___x_4504_; lean_object* v___x_4505_; 
v___x_4502_ = lean_box(0);
v_sz_4503_ = lean_array_size(v_errors_4495_);
v___x_4504_ = ((size_t)0ULL);
v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4495_, v_sz_4503_, v___x_4504_, v___x_4502_, v___y_4499_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4514_; 
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v___x_4505_, 0);
lean_dec(v_unused_4515_);
v___x_4507_ = v___x_4505_;
v_isShared_4508_ = v_isSharedCheck_4514_;
goto v_resetjp_4506_;
}
else
{
lean_dec(v___x_4505_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4514_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4509_ = lean_box(v_anyFailed_4498_);
v___x_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4510_, 0, v_entries_4496_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 0, v___x_4510_);
v___x_4512_ = v___x_4507_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec_ref(v_entries_4496_);
v_a_4516_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4505_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4505_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4524_, lean_object* v_entries_4525_, lean_object* v_____r_4526_, lean_object* v_anyFailed_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
uint8_t v_anyFailed_boxed_4531_; lean_object* v_res_4532_; 
v_anyFailed_boxed_4531_ = lean_unbox(v_anyFailed_4527_);
v_res_4532_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4524_, v_entries_4525_, v_____r_4526_, v_anyFailed_boxed_4531_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v_errors_4524_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4533_, lean_object* v_env_4534_, lean_object* v_mod_4535_){
_start:
{
lean_object* v_a_4538_; lean_object* v_a_4542_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___y_4578_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v_env_4596_; uint8_t v_anyFailed_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; lean_object* v_fileName_4606_; lean_object* v_fileMap_4607_; lean_object* v_currRecDepth_4608_; lean_object* v_ref_4609_; lean_object* v_currNamespace_4610_; lean_object* v_openDecls_4611_; lean_object* v_initHeartbeats_4612_; lean_object* v_maxHeartbeats_4613_; lean_object* v_quotContext_4614_; lean_object* v_currMacroScope_4615_; lean_object* v_cancelTk_x3f_4616_; uint8_t v_suppressElabErrors_4617_; lean_object* v_inheritedTraceOptions_4618_; lean_object* v___y_4619_; uint8_t v___y_4638_; uint8_t v___x_4658_; 
v___x_4559_ = lean_unsigned_to_nat(0u);
v___x_4560_ = lean_unsigned_to_nat(32u);
v___x_4561_ = lean_mk_empty_array_with_capacity(v___x_4560_);
lean_dec_ref(v___x_4561_);
v___x_4562_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4563_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4564_ = lean_io_get_num_heartbeats();
v___x_4565_ = l_Lean_firstFrontendMacroScope;
v___x_4566_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4567_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4568_ = lean_box(0);
v___x_4569_ = lean_box(0);
v___x_4570_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4571_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4572_ = 1;
v___x_4573_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4574_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4575_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4575_, 0, v_env_4534_);
lean_ctor_set(v___x_4575_, 1, v___x_4566_);
lean_ctor_set(v___x_4575_, 2, v___x_4567_);
lean_ctor_set(v___x_4575_, 3, v___x_4570_);
lean_ctor_set(v___x_4575_, 4, v___x_4571_);
lean_ctor_set(v___x_4575_, 5, v___x_4562_);
lean_ctor_set(v___x_4575_, 6, v___x_4563_);
lean_ctor_set(v___x_4575_, 7, v___x_4573_);
lean_ctor_set(v___x_4575_, 8, v___x_4574_);
v___x_4576_ = lean_st_mk_ref(v___x_4575_);
v___x_4593_ = l_Lean_inheritedTraceOptions;
v___x_4594_ = lean_st_ref_get(v___x_4593_);
v___x_4595_ = lean_st_ref_get(v___x_4576_);
v_env_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc_ref(v_env_4596_);
lean_dec(v___x_4595_);
v_anyFailed_4597_ = 0;
v___x_4598_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4599_ = l_Lean_instInhabitedFileMap_default;
v___x_4600_ = l_Lean_Options_empty;
v___x_4601_ = lean_box(0);
v___x_4602_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4603_ = lean_box(0);
v___x_4604_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4658_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4596_);
lean_dec_ref(v_env_4596_);
if (v___x_4604_ == 0)
{
if (v___x_4658_ == 0)
{
lean_inc(v___x_4576_);
v_fileName_4606_ = v___x_4598_;
v_fileMap_4607_ = v___x_4599_;
v_currRecDepth_4608_ = v___x_4559_;
v_ref_4609_ = v___x_4601_;
v_currNamespace_4610_ = v___x_4568_;
v_openDecls_4611_ = v___x_4569_;
v_initHeartbeats_4612_ = v___x_4564_;
v_maxHeartbeats_4613_ = v___x_4602_;
v_quotContext_4614_ = v___x_4568_;
v_currMacroScope_4615_ = v___x_4565_;
v_cancelTk_x3f_4616_ = v___x_4603_;
v_suppressElabErrors_4617_ = v_anyFailed_4597_;
v_inheritedTraceOptions_4618_ = v___x_4594_;
v___y_4619_ = v___x_4576_;
goto v___jp_4605_;
}
else
{
v___y_4638_ = v___x_4604_;
goto v___jp_4637_;
}
}
else
{
v___y_4638_ = v___x_4658_;
goto v___jp_4637_;
}
v___jp_4537_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = lean_mk_io_user_error(v_a_4538_);
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
return v___x_4540_;
}
v___jp_4541_:
{
if (lean_obj_tag(v_a_4542_) == 0)
{
lean_object* v_msg_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v_msg_4543_ = lean_ctor_get(v_a_4542_, 1);
lean_inc_ref(v_msg_4543_);
lean_dec_ref_known(v_a_4542_, 2);
v___x_4544_ = l_Lean_MessageData_toString(v_msg_4543_);
v___x_4545_ = lean_mk_io_user_error(v___x_4544_);
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
else
{
lean_object* v_id_4547_; lean_object* v___x_4548_; 
v_id_4547_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_id_4547_);
lean_dec_ref_known(v_a_4542_, 2);
v___x_4548_ = l_Lean_InternalExceptionId_getName(v_id_4547_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v_id_4547_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v___x_4548_, 1);
v___x_4550_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4551_ = 1;
v___x_4552_ = l_Lean_Name_toString(v_a_4549_, v___x_4551_);
v___x_4553_ = lean_string_append(v___x_4550_, v___x_4552_);
lean_dec_ref(v___x_4552_);
v_a_4538_ = v___x_4553_;
goto v___jp_4537_;
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_dec_ref_known(v___x_4548_, 1);
v___x_4554_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4555_ = l_Nat_reprFast(v_id_4547_);
v___x_4556_ = lean_string_append(v___x_4554_, v___x_4555_);
lean_dec_ref(v___x_4555_);
v___x_4557_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4558_ = lean_string_append(v___x_4556_, v___x_4557_);
v_a_4538_ = v___x_4558_;
goto v___jp_4537_;
}
}
}
v___jp_4577_:
{
if (lean_obj_tag(v___y_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4591_; 
v_a_4579_ = lean_ctor_get(v___y_4578_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___y_4578_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4581_ = v___y_4578_;
v_isShared_4582_ = v_isSharedCheck_4591_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___y_4578_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4591_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v_fst_4584_; lean_object* v_snd_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; lean_object* v___x_4589_; 
v___x_4583_ = lean_st_ref_get(v___x_4576_);
lean_dec(v___x_4576_);
lean_dec(v___x_4583_);
v_fst_4584_ = lean_ctor_get(v_a_4579_, 0);
lean_inc(v_fst_4584_);
v_snd_4585_ = lean_ctor_get(v_a_4579_, 1);
lean_inc(v_snd_4585_);
lean_dec(v_a_4579_);
v___x_4586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4586_, 0, v_fst_4584_);
v___x_4587_ = lean_unbox(v_snd_4585_);
lean_dec(v_snd_4585_);
lean_ctor_set_uint8(v___x_4586_, sizeof(void*)*1, v___x_4587_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4586_);
v___x_4589_ = v___x_4581_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4586_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
else
{
lean_object* v_a_4592_; 
lean_dec(v___x_4576_);
v_a_4592_ = lean_ctor_get(v___y_4578_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___y_4578_, 1);
v_a_4542_ = v_a_4592_;
goto v___jp_4541_;
}
}
v___jp_4605_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4616_);
lean_inc(v_currMacroScope_4615_);
lean_inc(v_quotContext_4614_);
lean_inc(v_maxHeartbeats_4613_);
lean_inc(v_openDecls_4611_);
lean_inc(v_currNamespace_4610_);
lean_inc(v_ref_4609_);
lean_inc_ref(v_fileMap_4607_);
lean_inc_ref(v_fileName_4606_);
v___x_4621_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4621_, 0, v_fileName_4606_);
lean_ctor_set(v___x_4621_, 1, v_fileMap_4607_);
lean_ctor_set(v___x_4621_, 2, v___x_4600_);
lean_ctor_set(v___x_4621_, 3, v_currRecDepth_4608_);
lean_ctor_set(v___x_4621_, 4, v___x_4620_);
lean_ctor_set(v___x_4621_, 5, v_ref_4609_);
lean_ctor_set(v___x_4621_, 6, v_currNamespace_4610_);
lean_ctor_set(v___x_4621_, 7, v_openDecls_4611_);
lean_ctor_set(v___x_4621_, 8, v_initHeartbeats_4612_);
lean_ctor_set(v___x_4621_, 9, v_maxHeartbeats_4613_);
lean_ctor_set(v___x_4621_, 10, v_quotContext_4614_);
lean_ctor_set(v___x_4621_, 11, v_currMacroScope_4615_);
lean_ctor_set(v___x_4621_, 12, v_cancelTk_x3f_4616_);
lean_ctor_set(v___x_4621_, 13, v_inheritedTraceOptions_4618_);
lean_ctor_set_uint8(v___x_4621_, sizeof(void*)*14, v___x_4604_);
lean_ctor_set_uint8(v___x_4621_, sizeof(void*)*14 + 1, v_suppressElabErrors_4617_);
v___x_4622_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4621_, v___y_4619_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref_known(v___x_4622_, 1);
v___x_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4624_, 0, v_sp_4533_);
lean_ctor_set(v___x_4624_, 1, v_mod_4535_);
v___x_4625_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4623_, v___x_4624_, v___x_4621_, v___y_4619_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v_entries_4627_; lean_object* v_errors_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref_known(v___x_4625_, 1);
v_entries_4627_ = lean_ctor_get(v_a_4626_, 0);
lean_inc_ref(v_entries_4627_);
v_errors_4628_ = lean_ctor_get(v_a_4626_, 1);
lean_inc_ref(v_errors_4628_);
lean_dec(v_a_4626_);
v___x_4629_ = lean_array_get_size(v_errors_4628_);
v___x_4630_ = lean_nat_dec_eq(v___x_4629_, v___x_4559_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = lean_box(0);
v___x_4632_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4628_, v_entries_4627_, v___x_4631_, v___x_4572_, v___x_4621_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref_known(v___x_4621_, 14);
lean_dec_ref(v_errors_4628_);
v___y_4578_ = v___x_4632_;
goto v___jp_4577_;
}
else
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = lean_box(0);
v___x_4634_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4628_, v_entries_4627_, v___x_4633_, v_anyFailed_4597_, v___x_4621_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref_known(v___x_4621_, 14);
lean_dec_ref(v_errors_4628_);
v___y_4578_ = v___x_4634_;
goto v___jp_4577_;
}
}
else
{
lean_object* v_a_4635_; 
lean_dec_ref_known(v___x_4621_, 14);
lean_dec(v___y_4619_);
lean_dec(v___x_4576_);
v_a_4635_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4625_, 1);
v_a_4542_ = v_a_4635_;
goto v___jp_4541_;
}
}
else
{
lean_object* v_a_4636_; 
lean_dec_ref_known(v___x_4621_, 14);
lean_dec(v___y_4619_);
lean_dec(v___x_4576_);
lean_dec(v_mod_4535_);
lean_dec(v_sp_4533_);
v_a_4636_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4622_, 1);
v_a_4542_ = v_a_4636_;
goto v___jp_4541_;
}
}
v___jp_4637_:
{
if (v___y_4638_ == 0)
{
lean_object* v___x_4639_; lean_object* v_env_4640_; lean_object* v_nextMacroScope_4641_; lean_object* v_ngen_4642_; lean_object* v_auxDeclNGen_4643_; lean_object* v_traceState_4644_; lean_object* v_messages_4645_; lean_object* v_infoState_4646_; lean_object* v_snapshotTasks_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4656_; 
v___x_4639_ = lean_st_ref_take(v___x_4576_);
v_env_4640_ = lean_ctor_get(v___x_4639_, 0);
v_nextMacroScope_4641_ = lean_ctor_get(v___x_4639_, 1);
v_ngen_4642_ = lean_ctor_get(v___x_4639_, 2);
v_auxDeclNGen_4643_ = lean_ctor_get(v___x_4639_, 3);
v_traceState_4644_ = lean_ctor_get(v___x_4639_, 4);
v_messages_4645_ = lean_ctor_get(v___x_4639_, 6);
v_infoState_4646_ = lean_ctor_get(v___x_4639_, 7);
v_snapshotTasks_4647_ = lean_ctor_get(v___x_4639_, 8);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4656_ == 0)
{
lean_object* v_unused_4657_; 
v_unused_4657_ = lean_ctor_get(v___x_4639_, 5);
lean_dec(v_unused_4657_);
v___x_4649_ = v___x_4639_;
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_snapshotTasks_4647_);
lean_inc(v_infoState_4646_);
lean_inc(v_messages_4645_);
lean_inc(v_traceState_4644_);
lean_inc(v_auxDeclNGen_4643_);
lean_inc(v_ngen_4642_);
lean_inc(v_nextMacroScope_4641_);
lean_inc(v_env_4640_);
lean_dec(v___x_4639_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4653_; 
v___x_4651_ = l_Lean_Kernel_enableDiag(v_env_4640_, v___x_4604_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 5, v___x_4562_);
lean_ctor_set(v___x_4649_, 0, v___x_4651_);
v___x_4653_ = v___x_4649_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_nextMacroScope_4641_);
lean_ctor_set(v_reuseFailAlloc_4655_, 2, v_ngen_4642_);
lean_ctor_set(v_reuseFailAlloc_4655_, 3, v_auxDeclNGen_4643_);
lean_ctor_set(v_reuseFailAlloc_4655_, 4, v_traceState_4644_);
lean_ctor_set(v_reuseFailAlloc_4655_, 5, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4655_, 6, v_messages_4645_);
lean_ctor_set(v_reuseFailAlloc_4655_, 7, v_infoState_4646_);
lean_ctor_set(v_reuseFailAlloc_4655_, 8, v_snapshotTasks_4647_);
v___x_4653_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; 
v___x_4654_ = lean_st_ref_put(v___x_4576_, v___x_4653_);
lean_inc(v___x_4576_);
v_fileName_4606_ = v___x_4598_;
v_fileMap_4607_ = v___x_4599_;
v_currRecDepth_4608_ = v___x_4559_;
v_ref_4609_ = v___x_4601_;
v_currNamespace_4610_ = v___x_4568_;
v_openDecls_4611_ = v___x_4569_;
v_initHeartbeats_4612_ = v___x_4564_;
v_maxHeartbeats_4613_ = v___x_4602_;
v_quotContext_4614_ = v___x_4568_;
v_currMacroScope_4615_ = v___x_4565_;
v_cancelTk_x3f_4616_ = v___x_4603_;
v_suppressElabErrors_4617_ = v_anyFailed_4597_;
v_inheritedTraceOptions_4618_ = v___x_4594_;
v___y_4619_ = v___x_4576_;
goto v___jp_4605_;
}
}
}
else
{
lean_inc(v___x_4576_);
v_fileName_4606_ = v___x_4598_;
v_fileMap_4607_ = v___x_4599_;
v_currRecDepth_4608_ = v___x_4559_;
v_ref_4609_ = v___x_4601_;
v_currNamespace_4610_ = v___x_4568_;
v_openDecls_4611_ = v___x_4569_;
v_initHeartbeats_4612_ = v___x_4564_;
v_maxHeartbeats_4613_ = v___x_4602_;
v_quotContext_4614_ = v___x_4568_;
v_currMacroScope_4615_ = v___x_4565_;
v_cancelTk_x3f_4616_ = v___x_4603_;
v_suppressElabErrors_4617_ = v_anyFailed_4597_;
v_inheritedTraceOptions_4618_ = v___x_4594_;
v___y_4619_ = v___x_4576_;
goto v___jp_4605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4659_, lean_object* v_env_4660_, lean_object* v_mod_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4659_, v_env_4660_, v_mod_4661_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4664_, size_t v_sz_4665_, size_t v_i_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4664_, v_sz_4665_, v_i_4666_, v_b_4667_, v___y_4668_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4672_, lean_object* v_sz_4673_, lean_object* v_i_4674_, lean_object* v_b_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
size_t v_sz_boxed_4679_; size_t v_i_boxed_4680_; lean_object* v_res_4681_; 
v_sz_boxed_4679_ = lean_unbox_usize(v_sz_4673_);
lean_dec(v_sz_4673_);
v_i_boxed_4680_ = lean_unbox_usize(v_i_4674_);
lean_dec(v_i_4674_);
v_res_4681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4672_, v_sz_boxed_4679_, v_i_boxed_4680_, v_b_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v_as_4672_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_enable_initializer_execution();
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_compacted_region_free(v_region_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4689_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4695_, lean_object* v_k_4696_, uint8_t v_v_4697_){
_start:
{
lean_object* v_map_4698_; uint8_t v_hasTrace_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4713_; 
v_map_4698_ = lean_ctor_get(v_o_4695_, 0);
v_hasTrace_4699_ = lean_ctor_get_uint8(v_o_4695_, sizeof(void*)*1);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_o_4695_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4701_ = v_o_4695_;
v_isShared_4702_ = v_isSharedCheck_4713_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_map_4698_);
lean_dec(v_o_4695_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4713_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4703_, 0, v_v_4697_);
lean_inc(v_k_4696_);
v___x_4704_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4696_, v___x_4703_, v_map_4698_);
if (v_hasTrace_4699_ == 0)
{
lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4708_; 
v___x_4705_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4706_ = l_Lean_Name_isPrefixOf(v___x_4705_, v_k_4696_);
lean_dec(v_k_4696_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4704_);
v___x_4708_ = v___x_4701_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v___x_4704_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_ctor_set_uint8(v___x_4708_, sizeof(void*)*1, v___x_4706_);
return v___x_4708_;
}
}
else
{
lean_object* v___x_4711_; 
lean_dec(v_k_4696_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4704_);
v___x_4711_ = v___x_4701_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4704_);
lean_ctor_set_uint8(v_reuseFailAlloc_4712_, sizeof(void*)*1, v_hasTrace_4699_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4714_, lean_object* v_k_4715_, lean_object* v_v_4716_){
_start:
{
uint8_t v_v_boxed_4717_; lean_object* v_res_4718_; 
v_v_boxed_4717_ = lean_unbox(v_v_4716_);
v_res_4718_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4714_, v_k_4715_, v_v_boxed_4717_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4719_){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; uint32_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4721_ = lean_unsigned_to_nat(80u);
v___x_4722_ = l_Lean_Json_pretty(v_s_4719_, v___x_4721_);
v___x_4723_ = 10;
v___x_4724_ = lean_string_push(v___x_4722_, v___x_4723_);
v___x_4725_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4726_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4729_, size_t v_sz_4730_, size_t v_i_4731_, lean_object* v_b_4732_){
_start:
{
uint8_t v___x_4734_; 
v___x_4734_ = lean_usize_dec_lt(v_i_4731_, v_sz_4730_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; 
v___x_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4735_, 0, v_b_4732_);
return v___x_4735_;
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v_a_4736_ = lean_array_uget_borrowed(v_as_4729_, v_i_4731_);
lean_inc(v_a_4736_);
v___x_4737_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4736_);
v___x_4738_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4737_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v___x_4739_; size_t v___x_4740_; size_t v___x_4741_; 
lean_dec_ref_known(v___x_4738_, 1);
v___x_4739_ = lean_box(0);
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4731_, v___x_4740_);
v_i_4731_ = v___x_4741_;
v_b_4732_ = v___x_4739_;
goto _start;
}
else
{
return v___x_4738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4743_, lean_object* v_sz_4744_, lean_object* v_i_4745_, lean_object* v_b_4746_, lean_object* v___y_4747_){
_start:
{
size_t v_sz_boxed_4748_; size_t v_i_boxed_4749_; lean_object* v_res_4750_; 
v_sz_boxed_4748_ = lean_unbox_usize(v_sz_4744_);
lean_dec(v_sz_4744_);
v_i_boxed_4749_ = lean_unbox_usize(v_i_4745_);
lean_dec(v_i_4745_);
v_res_4750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4743_, v_sz_boxed_4748_, v_i_boxed_4749_, v_b_4746_);
lean_dec_ref(v_as_4743_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4751_, size_t v_sz_4752_, size_t v_i_4753_, lean_object* v_bs_4754_){
_start:
{
uint8_t v_anyUnlocated_4755_; 
v_anyUnlocated_4755_ = lean_usize_dec_lt(v_i_4753_, v_sz_4752_);
if (v_anyUnlocated_4755_ == 0)
{
return v_bs_4754_;
}
else
{
lean_object* v___x_4756_; uint8_t v_anyFailed_4757_; lean_object* v_v_4758_; lean_object* v_bs_x27_4759_; lean_object* v___x_4760_; size_t v___x_4761_; size_t v___x_4762_; lean_object* v___x_4763_; 
v___x_4756_ = lean_unsigned_to_nat(0u);
v_anyFailed_4757_ = lean_nat_dec_eq(v___x_4751_, v___x_4756_);
v_v_4758_ = lean_array_uget(v_bs_4754_, v_i_4753_);
v_bs_x27_4759_ = lean_array_uset(v_bs_4754_, v_i_4753_, v___x_4756_);
v___x_4760_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4760_, 0, v_v_4758_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*1, v_anyFailed_4757_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*1 + 1, v_anyUnlocated_4755_);
lean_ctor_set_uint8(v___x_4760_, sizeof(void*)*1 + 2, v_anyFailed_4757_);
v___x_4761_ = ((size_t)1ULL);
v___x_4762_ = lean_usize_add(v_i_4753_, v___x_4761_);
v___x_4763_ = lean_array_uset(v_bs_x27_4759_, v_i_4753_, v___x_4760_);
v_i_4753_ = v___x_4762_;
v_bs_4754_ = v___x_4763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4765_, lean_object* v_sz_4766_, lean_object* v_i_4767_, lean_object* v_bs_4768_){
_start:
{
size_t v_sz_boxed_4769_; size_t v_i_boxed_4770_; lean_object* v_res_4771_; 
v_sz_boxed_4769_ = lean_unbox_usize(v_sz_4766_);
lean_dec(v_sz_4766_);
v_i_boxed_4770_ = lean_unbox_usize(v_i_4767_);
lean_dec(v_i_4767_);
v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4765_, v_sz_boxed_4769_, v_i_boxed_4770_, v_bs_4768_);
lean_dec(v___x_4765_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4772_, size_t v_i_4773_, size_t v_stop_4774_, lean_object* v_b_4775_){
_start:
{
uint8_t v___x_4776_; 
v___x_4776_ = lean_usize_dec_eq(v_i_4773_, v_stop_4774_);
if (v___x_4776_ == 0)
{
lean_object* v___x_4777_; lean_object* v_fst_4778_; lean_object* v_snd_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; size_t v___x_4782_; size_t v___x_4783_; 
v___x_4777_ = lean_array_uget_borrowed(v_as_4772_, v_i_4773_);
v_fst_4778_ = lean_ctor_get(v___x_4777_, 0);
v_snd_4779_ = lean_ctor_get(v___x_4777_, 1);
v___x_4780_ = lean_unbox(v_snd_4779_);
lean_inc(v_fst_4778_);
v___x_4781_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4775_, v_fst_4778_, v___x_4780_);
v___x_4782_ = ((size_t)1ULL);
v___x_4783_ = lean_usize_add(v_i_4773_, v___x_4782_);
v_i_4773_ = v___x_4783_;
v_b_4775_ = v___x_4781_;
goto _start;
}
else
{
return v_b_4775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4785_, lean_object* v_i_4786_, lean_object* v_stop_4787_, lean_object* v_b_4788_){
_start:
{
size_t v_i_boxed_4789_; size_t v_stop_boxed_4790_; lean_object* v_res_4791_; 
v_i_boxed_4789_ = lean_unbox_usize(v_i_4786_);
lean_dec(v_i_4786_);
v_stop_boxed_4790_ = lean_unbox_usize(v_stop_4787_);
lean_dec(v_stop_4787_);
v_res_4791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4785_, v_i_boxed_4789_, v_stop_boxed_4790_, v_b_4788_);
lean_dec_ref(v_as_4785_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4801_, lean_object* v_checkImports_4802_, lean_object* v_args_4803_, lean_object* v___x_4804_, lean_object* v_as_4805_, size_t v_sz_4806_, size_t v_i_4807_, lean_object* v_b_4808_){
_start:
{
lean_object* v_a_4811_; lean_object* v___x_4815_; uint8_t v_anyFailed_4816_; uint8_t v_anyUnlocated_4817_; lean_object* v___x_4818_; lean_object* v_envLinterModule_4819_; uint8_t v___x_4820_; 
v___x_4815_ = lean_unsigned_to_nat(0u);
v_anyFailed_4816_ = lean_nat_dec_eq(v___x_4801_, v___x_4815_);
v_anyUnlocated_4817_ = 1;
v___x_4818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4819_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4819_, 0, v___x_4818_);
lean_ctor_set_uint8(v_envLinterModule_4819_, sizeof(void*)*1, v_anyFailed_4816_);
lean_ctor_set_uint8(v_envLinterModule_4819_, sizeof(void*)*1 + 1, v_anyUnlocated_4817_);
lean_ctor_set_uint8(v_envLinterModule_4819_, sizeof(void*)*1 + 2, v_anyFailed_4816_);
v___x_4820_ = lean_usize_dec_lt(v_i_4807_, v_sz_4806_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; 
lean_dec_ref_known(v_envLinterModule_4819_, 1);
lean_dec(v___x_4804_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v_b_4808_);
return v___x_4821_;
}
else
{
lean_object* v___x_4822_; lean_object* v_a_4823_; lean_object* v___x_4824_; 
v___x_4822_ = lean_enable_initializer_execution();
v_a_4823_ = lean_array_uget_borrowed(v_as_4805_, v_i_4807_);
lean_inc(v_a_4823_);
v___x_4824_ = l_Lean_findOLean(v_a_4823_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4826_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v___x_4826_ = l_Lean_readModuleData(v_a_4825_);
lean_dec(v_a_4825_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v_fst_4828_; lean_object* v_snd_4829_; uint8_t v___x_4830_; lean_object* v_snd_4831_; lean_object* v_snd_4832_; lean_object* v_snd_4833_; lean_object* v_fst_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_5090_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v_fst_4828_ = lean_ctor_get(v_a_4827_, 0);
lean_inc(v_fst_4828_);
v_snd_4829_ = lean_ctor_get(v_a_4827_, 1);
lean_inc(v_snd_4829_);
lean_dec(v_a_4827_);
v___x_4830_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4828_);
lean_dec(v_fst_4828_);
v_snd_4831_ = lean_ctor_get(v_b_4808_, 1);
lean_inc(v_snd_4831_);
v_snd_4832_ = lean_ctor_get(v_snd_4831_, 1);
lean_inc(v_snd_4832_);
v_snd_4833_ = lean_ctor_get(v_snd_4832_, 1);
lean_inc(v_snd_4833_);
v_fst_4834_ = lean_ctor_get(v_b_4808_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_b_4808_);
if (v_isSharedCheck_5090_ == 0)
{
lean_object* v_unused_5091_; 
v_unused_5091_ = lean_ctor_get(v_b_4808_, 1);
lean_dec(v_unused_5091_);
v___x_4836_ = v_b_4808_;
v_isShared_4837_ = v_isSharedCheck_5090_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_fst_4834_);
lean_dec(v_b_4808_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_5090_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v_fst_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_5088_; 
v_fst_4838_ = lean_ctor_get(v_snd_4831_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_snd_4831_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v_snd_4831_, 1);
lean_dec(v_unused_5089_);
v___x_4840_ = v_snd_4831_;
v_isShared_4841_ = v_isSharedCheck_5088_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_fst_4838_);
lean_dec(v_snd_4831_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_5088_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v_fst_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_5086_; 
v_fst_4842_ = lean_ctor_get(v_snd_4832_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_snd_4832_);
if (v_isSharedCheck_5086_ == 0)
{
lean_object* v_unused_5087_; 
v_unused_5087_ = lean_ctor_get(v_snd_4832_, 1);
lean_dec(v_unused_5087_);
v___x_4844_ = v_snd_4832_;
v_isShared_4845_ = v_isSharedCheck_5086_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_fst_4842_);
lean_dec(v_snd_4832_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_5086_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v_fst_4846_; lean_object* v_snd_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_5085_; 
v_fst_4846_ = lean_ctor_get(v_snd_4833_, 0);
v_snd_4847_ = lean_ctor_get(v_snd_4833_, 1);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_snd_4833_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_4849_ = v_snd_4833_;
v_isShared_4850_ = v_isSharedCheck_5085_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_snd_4847_);
lean_inc(v_fst_4846_);
lean_dec(v_snd_4833_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_5085_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___y_4852_; lean_object* v___y_4853_; uint8_t v_anyFailed_4854_; uint8_t v_anyUnlocated_4855_; lean_object* v_records_4856_; lean_object* v_codeQualityEntries_4857_; lean_object* v___y_4978_; lean_object* v___y_4979_; uint8_t v_anyFailed_4980_; uint8_t v_anyUnlocated_4981_; lean_object* v_records_4982_; lean_object* v_codeQualityEntries_4983_; lean_object* v___x_5000_; lean_object* v___y_5002_; lean_object* v___y_5003_; uint8_t v___y_5043_; 
v___x_5000_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
if (v___x_4830_ == 0)
{
uint8_t v___x_5083_; 
v___x_5083_ = 2;
v___y_5043_ = v___x_5083_;
goto v___jp_5042_;
}
else
{
uint8_t v___x_5084_; 
v___x_5084_ = 1;
v___y_5043_ = v___x_5084_;
goto v___jp_5042_;
}
v___jp_4851_:
{
uint8_t v_mode_4858_; uint8_t v___x_4859_; uint8_t v___x_4860_; 
v_mode_4858_ = lean_ctor_get_uint8(v_args_4803_, sizeof(void*)*4 + 1);
v___x_4859_ = 2;
v___x_4860_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4861_ = l_Lean_Name_getRoot(v_a_4823_);
lean_inc(v___x_4804_);
v___x_4862_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4803_, v___y_4852_, v___x_4804_, v___y_4853_, v___x_4861_, v_snd_4847_);
lean_dec_ref(v___y_4852_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v_outcome_4864_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v_outcome_4864_ = lean_ctor_get(v_a_4863_, 0);
if (lean_obj_tag(v_outcome_4864_) == 0)
{
uint8_t v_failed_4865_; 
v_failed_4865_ = lean_ctor_get_uint8(v_outcome_4864_, 0);
if (v_failed_4865_ == 0)
{
lean_object* v_checkedModules_4866_; lean_object* v___x_4868_; 
v_checkedModules_4866_ = lean_ctor_get(v_a_4863_, 1);
lean_inc(v_checkedModules_4866_);
lean_dec(v_a_4863_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_checkedModules_4866_);
lean_ctor_set(v___x_4849_, 0, v_codeQualityEntries_4857_);
v___x_4868_ = v___x_4849_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_codeQualityEntries_4857_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_checkedModules_4866_);
v___x_4868_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4870_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4868_);
lean_ctor_set(v___x_4844_, 0, v_records_4856_);
v___x_4870_ = v___x_4844_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_records_4856_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v___x_4868_);
v___x_4870_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4871_ = lean_box(v_anyUnlocated_4855_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4870_);
lean_ctor_set(v___x_4840_, 0, v___x_4871_);
v___x_4873_ = v___x_4840_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4871_);
lean_ctor_set(v_reuseFailAlloc_4878_, 1, v___x_4870_);
v___x_4873_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4874_ = lean_box(v_anyFailed_4854_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4873_);
lean_ctor_set(v___x_4836_, 0, v___x_4874_);
v___x_4876_ = v___x_4836_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v___x_4873_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
v_a_4811_ = v___x_4876_;
goto v___jp_4810_;
}
}
}
}
}
else
{
lean_object* v_checkedModules_4881_; lean_object* v___x_4883_; 
v_checkedModules_4881_ = lean_ctor_get(v_a_4863_, 1);
lean_inc(v_checkedModules_4881_);
lean_dec(v_a_4863_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_checkedModules_4881_);
lean_ctor_set(v___x_4849_, 0, v_codeQualityEntries_4857_);
v___x_4883_ = v___x_4849_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_codeQualityEntries_4857_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_checkedModules_4881_);
v___x_4883_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4885_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4883_);
lean_ctor_set(v___x_4844_, 0, v_records_4856_);
v___x_4885_ = v___x_4844_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_records_4856_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4886_ = lean_box(v_anyUnlocated_4855_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4885_);
lean_ctor_set(v___x_4840_, 0, v___x_4886_);
v___x_4888_ = v___x_4840_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4886_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4885_);
v___x_4888_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_box(v_anyUnlocated_4817_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4888_);
lean_ctor_set(v___x_4836_, 0, v___x_4889_);
v___x_4891_ = v___x_4836_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v___x_4888_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
v_a_4811_ = v___x_4891_;
goto v___jp_4810_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4896_; lean_object* v_records_4897_; uint8_t v_unlocated_4898_; lean_object* v___x_4899_; 
lean_inc_ref(v_outcome_4864_);
v_checkedModules_4896_ = lean_ctor_get(v_a_4863_, 1);
lean_inc(v_checkedModules_4896_);
lean_dec(v_a_4863_);
v_records_4897_ = lean_ctor_get(v_outcome_4864_, 0);
lean_inc_ref(v_records_4897_);
v_unlocated_4898_ = lean_ctor_get_uint8(v_outcome_4864_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4864_, 1);
v___x_4899_ = l_Array_append___redArg(v_records_4856_, v_records_4897_);
lean_dec_ref(v_records_4897_);
if (v_unlocated_4898_ == 0)
{
lean_object* v___x_4901_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_checkedModules_4896_);
lean_ctor_set(v___x_4849_, 0, v_codeQualityEntries_4857_);
v___x_4901_ = v___x_4849_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_codeQualityEntries_4857_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_checkedModules_4896_);
v___x_4901_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
lean_object* v___x_4903_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4901_);
lean_ctor_set(v___x_4844_, 0, v___x_4899_);
v___x_4903_ = v___x_4844_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v___x_4901_);
v___x_4903_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4904_ = lean_box(v_anyUnlocated_4855_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4903_);
lean_ctor_set(v___x_4840_, 0, v___x_4904_);
v___x_4906_ = v___x_4840_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v___x_4903_);
v___x_4906_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4909_; 
v___x_4907_ = lean_box(v_anyFailed_4854_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4906_);
lean_ctor_set(v___x_4836_, 0, v___x_4907_);
v___x_4909_ = v___x_4836_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v___x_4906_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
v_a_4811_ = v___x_4909_;
goto v___jp_4810_;
}
}
}
}
}
else
{
lean_object* v___x_4915_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v_checkedModules_4896_);
lean_ctor_set(v___x_4849_, 0, v_codeQualityEntries_4857_);
v___x_4915_ = v___x_4849_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_codeQualityEntries_4857_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_checkedModules_4896_);
v___x_4915_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4917_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4915_);
lean_ctor_set(v___x_4844_, 0, v___x_4899_);
v___x_4917_ = v___x_4844_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4899_);
lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4918_ = lean_box(v_anyUnlocated_4817_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4917_);
lean_ctor_set(v___x_4840_, 0, v___x_4918_);
v___x_4920_ = v___x_4840_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4918_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v___x_4917_);
v___x_4920_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4921_ = lean_box(v_anyFailed_4854_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4920_);
lean_ctor_set(v___x_4836_, 0, v___x_4921_);
v___x_4923_ = v___x_4836_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v___x_4920_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
v_a_4811_ = v___x_4923_;
goto v___jp_4810_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec_ref(v_codeQualityEntries_4857_);
lean_dec_ref(v_records_4856_);
lean_del_object(v___x_4849_);
lean_del_object(v___x_4844_);
lean_del_object(v___x_4840_);
lean_del_object(v___x_4836_);
lean_dec(v___x_4804_);
v_a_4928_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4862_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4862_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
else
{
lean_object* v___x_4936_; 
lean_dec_ref(v___y_4852_);
lean_inc(v_a_4823_);
lean_inc(v___x_4804_);
v___x_4936_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4804_, v___y_4853_, v_a_4823_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v_entries_4938_; uint8_t v_failed_4939_; lean_object* v___x_4940_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v_entries_4938_ = lean_ctor_get(v_a_4937_, 0);
lean_inc_ref(v_entries_4938_);
v_failed_4939_ = lean_ctor_get_uint8(v_a_4937_, sizeof(void*)*1);
lean_dec(v_a_4937_);
v___x_4940_ = l_Array_append___redArg(v_codeQualityEntries_4857_, v_entries_4938_);
lean_dec_ref(v_entries_4938_);
if (v_failed_4939_ == 0)
{
lean_object* v___x_4942_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4940_);
v___x_4942_ = v___x_4849_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v_snd_4847_);
v___x_4942_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4944_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4942_);
lean_ctor_set(v___x_4844_, 0, v_records_4856_);
v___x_4944_ = v___x_4844_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_records_4856_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v___x_4942_);
v___x_4944_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
v___x_4945_ = lean_box(v_anyUnlocated_4855_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4944_);
lean_ctor_set(v___x_4840_, 0, v___x_4945_);
v___x_4947_ = v___x_4840_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4952_, 1, v___x_4944_);
v___x_4947_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4948_; lean_object* v___x_4950_; 
v___x_4948_ = lean_box(v_anyFailed_4854_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4947_);
lean_ctor_set(v___x_4836_, 0, v___x_4948_);
v___x_4950_ = v___x_4836_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v___x_4947_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
v_a_4811_ = v___x_4950_;
goto v___jp_4810_;
}
}
}
}
}
else
{
lean_object* v___x_4956_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4940_);
v___x_4956_ = v___x_4849_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v_snd_4847_);
v___x_4956_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
lean_object* v___x_4958_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4956_);
lean_ctor_set(v___x_4844_, 0, v_records_4856_);
v___x_4958_ = v___x_4844_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_records_4856_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
lean_object* v___x_4959_; lean_object* v___x_4961_; 
v___x_4959_ = lean_box(v_anyUnlocated_4855_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v___x_4958_);
lean_ctor_set(v___x_4840_, 0, v___x_4959_);
v___x_4961_ = v___x_4840_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4966_, 1, v___x_4958_);
v___x_4961_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
lean_object* v___x_4962_; lean_object* v___x_4964_; 
v___x_4962_ = lean_box(v_anyUnlocated_4817_);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 1, v___x_4961_);
lean_ctor_set(v___x_4836_, 0, v___x_4962_);
v___x_4964_ = v___x_4836_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4965_, 1, v___x_4961_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
v_a_4811_ = v___x_4964_;
goto v___jp_4810_;
}
}
}
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec_ref(v_codeQualityEntries_4857_);
lean_dec_ref(v_records_4856_);
lean_del_object(v___x_4849_);
lean_dec(v_snd_4847_);
lean_del_object(v___x_4844_);
lean_del_object(v___x_4840_);
lean_del_object(v___x_4836_);
lean_dec(v___x_4804_);
v_a_4969_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4936_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4936_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
}
v___jp_4977_:
{
lean_object* v___x_4984_; 
lean_inc(v_a_4823_);
lean_inc_ref(v___y_4979_);
lean_inc(v___x_4804_);
lean_inc_ref(v___y_4978_);
v___x_4984_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4803_, v___y_4978_, v___x_4804_, v___y_4979_, v_a_4823_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
switch(lean_obj_tag(v_a_4985_))
{
case 0:
{
uint8_t v_failed_4986_; 
v_failed_4986_ = lean_ctor_get_uint8(v_a_4985_, 0);
lean_dec_ref_known(v_a_4985_, 0);
if (v_failed_4986_ == 0)
{
v___y_4852_ = v___y_4978_;
v___y_4853_ = v___y_4979_;
v_anyFailed_4854_ = v_anyFailed_4980_;
v_anyUnlocated_4855_ = v_anyUnlocated_4981_;
v_records_4856_ = v_records_4982_;
v_codeQualityEntries_4857_ = v_codeQualityEntries_4983_;
goto v___jp_4851_;
}
else
{
v___y_4852_ = v___y_4978_;
v___y_4853_ = v___y_4979_;
v_anyFailed_4854_ = v_anyUnlocated_4817_;
v_anyUnlocated_4855_ = v_anyUnlocated_4981_;
v_records_4856_ = v_records_4982_;
v_codeQualityEntries_4857_ = v_codeQualityEntries_4983_;
goto v___jp_4851_;
}
}
case 1:
{
lean_object* v_records_4987_; uint8_t v_unlocated_4988_; lean_object* v___x_4989_; 
v_records_4987_ = lean_ctor_get(v_a_4985_, 0);
lean_inc_ref(v_records_4987_);
v_unlocated_4988_ = lean_ctor_get_uint8(v_a_4985_, sizeof(void*)*1);
lean_dec_ref_known(v_a_4985_, 1);
v___x_4989_ = l_Array_append___redArg(v_records_4982_, v_records_4987_);
lean_dec_ref(v_records_4987_);
if (v_unlocated_4988_ == 0)
{
v___y_4852_ = v___y_4978_;
v___y_4853_ = v___y_4979_;
v_anyFailed_4854_ = v_anyFailed_4980_;
v_anyUnlocated_4855_ = v_anyUnlocated_4981_;
v_records_4856_ = v___x_4989_;
v_codeQualityEntries_4857_ = v_codeQualityEntries_4983_;
goto v___jp_4851_;
}
else
{
v___y_4852_ = v___y_4978_;
v___y_4853_ = v___y_4979_;
v_anyFailed_4854_ = v_anyFailed_4980_;
v_anyUnlocated_4855_ = v_anyUnlocated_4817_;
v_records_4856_ = v___x_4989_;
v_codeQualityEntries_4857_ = v_codeQualityEntries_4983_;
goto v___jp_4851_;
}
}
default: 
{
lean_object* v_entries_4990_; lean_object* v___x_4991_; 
v_entries_4990_ = lean_ctor_get(v_a_4985_, 0);
lean_inc_ref(v_entries_4990_);
lean_dec_ref_known(v_a_4985_, 1);
v___x_4991_ = l_Array_append___redArg(v_codeQualityEntries_4983_, v_entries_4990_);
lean_dec_ref(v_entries_4990_);
v___y_4852_ = v___y_4978_;
v___y_4853_ = v___y_4979_;
v_anyFailed_4854_ = v_anyFailed_4980_;
v_anyUnlocated_4855_ = v_anyUnlocated_4981_;
v_records_4856_ = v_records_4982_;
v_codeQualityEntries_4857_ = v___x_4991_;
goto v___jp_4851_;
}
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec_ref(v_codeQualityEntries_4983_);
lean_dec_ref(v_records_4982_);
lean_dec_ref(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_del_object(v___x_4849_);
lean_dec(v_snd_4847_);
lean_del_object(v___x_4844_);
lean_del_object(v___x_4840_);
lean_del_object(v___x_4836_);
lean_dec(v___x_4804_);
v_a_4992_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4984_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4984_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
v___jp_5001_:
{
lean_object* v___x_5004_; lean_object* v_toEnvExtension_5005_; lean_object* v_asyncMode_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v_merged_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5040_; 
v___x_5004_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5005_ = lean_ctor_get(v___x_5004_, 0);
v_asyncMode_5006_ = lean_ctor_get(v_toEnvExtension_5005_, 2);
v___x_5007_ = lean_box(0);
lean_inc_ref(v___y_5002_);
v___x_5008_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5000_, v___x_5004_, v___y_5002_, v_asyncMode_5006_, v___x_5007_);
v_merged_5009_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5040_ == 0)
{
lean_object* v_unused_5041_; 
v_unused_5041_ = lean_ctor_get(v___x_5008_, 1);
lean_dec(v_unused_5041_);
v___x_5011_ = v___x_5008_;
v_isShared_5012_ = v_isSharedCheck_5040_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_merged_5009_);
lean_dec(v___x_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5040_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 1, v_merged_5009_);
lean_ctor_set(v___x_5011_, 0, v___y_5003_);
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___y_5003_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v_merged_5009_);
v___x_5014_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5015_; 
v___x_5015_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4803_, v___x_5014_, v___y_5002_, v_a_4823_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
lean_dec_ref_known(v___x_5015_, 1);
switch(lean_obj_tag(v_a_5016_))
{
case 0:
{
uint8_t v___x_5017_; 
v___x_5017_ = lean_unbox(v_fst_4834_);
lean_dec(v_fst_4834_);
if (v___x_5017_ == 0)
{
uint8_t v_failed_5018_; uint8_t v___x_5019_; 
v_failed_5018_ = lean_ctor_get_uint8(v_a_5016_, 0);
lean_dec_ref_known(v_a_5016_, 0);
v___x_5019_ = lean_unbox(v_fst_4838_);
lean_dec(v_fst_4838_);
v___y_4978_ = v___x_5014_;
v___y_4979_ = v___y_5002_;
v_anyFailed_4980_ = v_failed_5018_;
v_anyUnlocated_4981_ = v___x_5019_;
v_records_4982_ = v_fst_4842_;
v_codeQualityEntries_4983_ = v_fst_4846_;
goto v___jp_4977_;
}
else
{
uint8_t v___x_5020_; 
lean_dec_ref_known(v_a_5016_, 0);
v___x_5020_ = lean_unbox(v_fst_4838_);
lean_dec(v_fst_4838_);
v___y_4978_ = v___x_5014_;
v___y_4979_ = v___y_5002_;
v_anyFailed_4980_ = v_anyUnlocated_4817_;
v_anyUnlocated_4981_ = v___x_5020_;
v_records_4982_ = v_fst_4842_;
v_codeQualityEntries_4983_ = v_fst_4846_;
goto v___jp_4977_;
}
}
case 1:
{
lean_object* v_records_5021_; uint8_t v_unlocated_5022_; lean_object* v___x_5023_; 
v_records_5021_ = lean_ctor_get(v_a_5016_, 0);
lean_inc_ref(v_records_5021_);
v_unlocated_5022_ = lean_ctor_get_uint8(v_a_5016_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5016_, 1);
v___x_5023_ = l_Array_append___redArg(v_fst_4842_, v_records_5021_);
lean_dec_ref(v_records_5021_);
if (v_unlocated_5022_ == 0)
{
uint8_t v___x_5024_; uint8_t v___x_5025_; 
v___x_5024_ = lean_unbox(v_fst_4834_);
lean_dec(v_fst_4834_);
v___x_5025_ = lean_unbox(v_fst_4838_);
lean_dec(v_fst_4838_);
v___y_4978_ = v___x_5014_;
v___y_4979_ = v___y_5002_;
v_anyFailed_4980_ = v___x_5024_;
v_anyUnlocated_4981_ = v___x_5025_;
v_records_4982_ = v___x_5023_;
v_codeQualityEntries_4983_ = v_fst_4846_;
goto v___jp_4977_;
}
else
{
uint8_t v___x_5026_; 
lean_dec(v_fst_4838_);
v___x_5026_ = lean_unbox(v_fst_4834_);
lean_dec(v_fst_4834_);
v___y_4978_ = v___x_5014_;
v___y_4979_ = v___y_5002_;
v_anyFailed_4980_ = v___x_5026_;
v_anyUnlocated_4981_ = v_anyUnlocated_4817_;
v_records_4982_ = v___x_5023_;
v_codeQualityEntries_4983_ = v_fst_4846_;
goto v___jp_4977_;
}
}
default: 
{
lean_object* v_entries_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; uint8_t v___x_5030_; 
v_entries_5027_ = lean_ctor_get(v_a_5016_, 0);
lean_inc_ref(v_entries_5027_);
lean_dec_ref_known(v_a_5016_, 1);
v___x_5028_ = l_Array_append___redArg(v_fst_4846_, v_entries_5027_);
lean_dec_ref(v_entries_5027_);
v___x_5029_ = lean_unbox(v_fst_4834_);
lean_dec(v_fst_4834_);
v___x_5030_ = lean_unbox(v_fst_4838_);
lean_dec(v_fst_4838_);
v___y_4978_ = v___x_5014_;
v___y_4979_ = v___y_5002_;
v_anyFailed_4980_ = v___x_5029_;
v_anyUnlocated_4981_ = v___x_5030_;
v_records_4982_ = v_fst_4842_;
v_codeQualityEntries_4983_ = v___x_5028_;
goto v___jp_4977_;
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_dec_ref(v___x_5014_);
lean_dec_ref(v___y_5002_);
lean_del_object(v___x_4849_);
lean_dec(v_snd_4847_);
lean_dec(v_fst_4846_);
lean_del_object(v___x_4844_);
lean_dec(v_fst_4842_);
lean_del_object(v___x_4840_);
lean_dec(v_fst_4838_);
lean_del_object(v___x_4836_);
lean_dec(v_fst_4834_);
lean_dec(v___x_4804_);
v_a_5031_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5015_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5015_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
}
v___jp_5042_:
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_compacted_region_free(v_snd_4829_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; uint32_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_dec_ref_known(v___x_5044_, 1);
lean_inc(v_a_4823_);
v___x_5045_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5045_, 0, v_a_4823_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*1, v_anyFailed_4816_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*1 + 1, v_anyUnlocated_4817_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*1 + 2, v_anyFailed_4816_);
v___x_5046_ = lean_unsigned_to_nat(2u);
v___x_5047_ = lean_mk_empty_array_with_capacity(v___x_5046_);
v___x_5048_ = lean_array_push(v___x_5047_, v___x_5045_);
v___x_5049_ = lean_array_push(v___x_5048_, v_envLinterModule_4819_);
v___x_5050_ = l_Array_append___redArg(v___x_5049_, v_checkImports_4802_);
v___x_5051_ = l_Lean_Options_empty;
v___x_5052_ = 1024;
v___x_5053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5054_ = lean_box(1);
v___x_5055_ = l_Lean_importModules(v___x_5050_, v___x_5051_, v___x_5052_, v___x_5053_, v_anyFailed_4816_, v_anyUnlocated_4817_, v___y_5043_, v___x_5054_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v_linterOverrides_5057_; lean_object* v___x_5058_; uint8_t v___x_5059_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v_linterOverrides_5057_ = lean_ctor_get(v_args_4803_, 0);
v___x_5058_ = lean_array_get_size(v_linterOverrides_5057_);
v___x_5059_ = lean_nat_dec_lt(v___x_4815_, v___x_5058_);
if (v___x_5059_ == 0)
{
v___y_5002_ = v_a_5056_;
v___y_5003_ = v___x_5051_;
goto v___jp_5001_;
}
else
{
uint8_t v___x_5060_; 
v___x_5060_ = lean_nat_dec_le(v___x_5058_, v___x_5058_);
if (v___x_5060_ == 0)
{
if (v___x_5059_ == 0)
{
v___y_5002_ = v_a_5056_;
v___y_5003_ = v___x_5051_;
goto v___jp_5001_;
}
else
{
size_t v___x_5061_; size_t v___x_5062_; lean_object* v___x_5063_; 
v___x_5061_ = ((size_t)0ULL);
v___x_5062_ = lean_usize_of_nat(v___x_5058_);
v___x_5063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5057_, v___x_5061_, v___x_5062_, v___x_5051_);
v___y_5002_ = v_a_5056_;
v___y_5003_ = v___x_5063_;
goto v___jp_5001_;
}
}
else
{
size_t v___x_5064_; size_t v___x_5065_; lean_object* v___x_5066_; 
v___x_5064_ = ((size_t)0ULL);
v___x_5065_ = lean_usize_of_nat(v___x_5058_);
v___x_5066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5057_, v___x_5064_, v___x_5065_, v___x_5051_);
v___y_5002_ = v_a_5056_;
v___y_5003_ = v___x_5066_;
goto v___jp_5001_;
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_del_object(v___x_4849_);
lean_dec(v_snd_4847_);
lean_dec(v_fst_4846_);
lean_del_object(v___x_4844_);
lean_dec(v_fst_4842_);
lean_del_object(v___x_4840_);
lean_dec(v_fst_4838_);
lean_del_object(v___x_4836_);
lean_dec(v_fst_4834_);
lean_dec(v___x_4804_);
v_a_5067_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_5055_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5055_);
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
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_del_object(v___x_4849_);
lean_dec(v_snd_4847_);
lean_dec(v_fst_4846_);
lean_del_object(v___x_4844_);
lean_dec(v_fst_4842_);
lean_del_object(v___x_4840_);
lean_dec(v_fst_4838_);
lean_del_object(v___x_4836_);
lean_dec(v_fst_4834_);
lean_dec_ref_known(v_envLinterModule_4819_, 1);
lean_dec(v___x_4804_);
v_a_5075_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5044_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5044_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
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
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec_ref_known(v_envLinterModule_4819_, 1);
lean_dec_ref(v_b_4808_);
lean_dec(v___x_4804_);
v_a_5092_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_4826_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_4826_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_dec_ref_known(v_envLinterModule_4819_, 1);
lean_dec_ref(v_b_4808_);
lean_dec(v___x_4804_);
v_a_5100_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_4824_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_4824_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
v___jp_4810_:
{
size_t v___x_4812_; size_t v___x_4813_; 
v___x_4812_ = ((size_t)1ULL);
v___x_4813_ = lean_usize_add(v_i_4807_, v___x_4812_);
v_i_4807_ = v___x_4813_;
v_b_4808_ = v_a_4811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5108_, lean_object* v_checkImports_5109_, lean_object* v_args_5110_, lean_object* v___x_5111_, lean_object* v_as_5112_, lean_object* v_sz_5113_, lean_object* v_i_5114_, lean_object* v_b_5115_, lean_object* v___y_5116_){
_start:
{
size_t v_sz_boxed_5117_; size_t v_i_boxed_5118_; lean_object* v_res_5119_; 
v_sz_boxed_5117_ = lean_unbox_usize(v_sz_5113_);
lean_dec(v_sz_5113_);
v_i_boxed_5118_ = lean_unbox_usize(v_i_5114_);
lean_dec(v_i_5114_);
v_res_5119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5108_, v_checkImports_5109_, v_args_5110_, v___x_5111_, v_as_5112_, v_sz_boxed_5117_, v_i_boxed_5118_, v_b_5115_);
lean_dec_ref(v_as_5112_);
lean_dec_ref(v_args_5110_);
lean_dec_ref(v_checkImports_5109_);
lean_dec(v___x_5108_);
return v_res_5119_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5120_ = l_Lean_NameSet_empty;
v___x_5121_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
lean_ctor_set(v___x_5122_, 1, v___x_5120_);
return v___x_5122_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5123_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5124_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5125_, 0, v___x_5124_);
lean_ctor_set(v___x_5125_, 1, v___x_5123_);
return v___x_5125_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = 0;
v___x_5128_ = lean_box_uint32(v___x_5127_);
return v___x_5128_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = 1;
v___x_5130_ = lean_box_uint32(v___x_5129_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5131_){
_start:
{
lean_object* v_mods_5133_; uint8_t v_mode_5134_; lean_object* v_checks_5135_; lean_object* v_srcSearchPath_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; uint8_t v_anyFailed_5139_; 
v_mods_5133_ = lean_ctor_get(v_args_5131_, 1);
lean_inc_ref(v_mods_5133_);
v_mode_5134_ = lean_ctor_get_uint8(v_args_5131_, sizeof(void*)*4 + 1);
v_checks_5135_ = lean_ctor_get(v_args_5131_, 2);
v_srcSearchPath_5136_ = lean_ctor_get(v_args_5131_, 3);
v___x_5137_ = lean_array_get_size(v_mods_5133_);
v___x_5138_ = lean_unsigned_to_nat(0u);
v_anyFailed_5139_ = lean_nat_dec_eq(v___x_5137_, v___x_5138_);
if (v_anyFailed_5139_ == 0)
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; size_t v_sz_5142_; size_t v___x_5143_; lean_object* v_checkImports_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; size_t v_sz_5151_; lean_object* v___x_5152_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5140_, 1);
v_sz_5142_ = lean_array_size(v_checks_5135_);
v___x_5143_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5135_);
v_checkImports_5144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5137_, v_sz_5142_, v___x_5143_, v_checks_5135_);
lean_inc(v_srcSearchPath_5136_);
v___x_5145_ = l_List_appendTR___redArg(v_srcSearchPath_5136_, v_a_5141_);
v___x_5146_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5147_ = lean_box(v_anyFailed_5139_);
v___x_5148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5148_, 0, v___x_5147_);
lean_ctor_set(v___x_5148_, 1, v___x_5146_);
v___x_5149_ = lean_box(v_anyFailed_5139_);
v___x_5150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5149_);
lean_ctor_set(v___x_5150_, 1, v___x_5148_);
v_sz_5151_ = lean_array_size(v_mods_5133_);
v___x_5152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5137_, v_checkImports_5144_, v_args_5131_, v___x_5145_, v_mods_5133_, v_sz_5151_, v___x_5143_, v___x_5150_);
lean_dec_ref(v_mods_5133_);
lean_dec_ref(v_args_5131_);
lean_dec_ref(v_checkImports_5144_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5224_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5155_ = v___x_5152_;
v_isShared_5156_ = v_isSharedCheck_5224_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5152_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5224_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
switch(v_mode_5134_)
{
case 0:
{
lean_object* v_fst_5157_; uint8_t v___x_5158_; 
v_fst_5157_ = lean_ctor_get(v_a_5153_, 0);
lean_inc(v_fst_5157_);
lean_dec(v_a_5153_);
v___x_5158_ = lean_unbox(v_fst_5157_);
lean_dec(v_fst_5157_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; lean_object* v___x_5161_; 
v___x_5159_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 0, v___x_5159_);
v___x_5161_ = v___x_5155_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
else
{
lean_object* v___x_5163_; lean_object* v___x_5165_; 
v___x_5163_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 0, v___x_5163_);
v___x_5165_ = v___x_5155_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
case 1:
{
lean_object* v_snd_5167_; lean_object* v_snd_5168_; lean_object* v_fst_5169_; lean_object* v_fst_5170_; lean_object* v___x_5171_; 
v_snd_5167_ = lean_ctor_get(v_a_5153_, 1);
lean_inc(v_snd_5167_);
lean_del_object(v___x_5155_);
lean_dec(v_a_5153_);
v_snd_5168_ = lean_ctor_get(v_snd_5167_, 1);
lean_inc(v_snd_5168_);
v_fst_5169_ = lean_ctor_get(v_snd_5167_, 0);
lean_inc(v_fst_5169_);
lean_dec(v_snd_5167_);
v_fst_5170_ = lean_ctor_get(v_snd_5168_, 0);
lean_inc(v_fst_5170_);
lean_dec(v_snd_5168_);
v___x_5171_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5170_);
lean_dec(v_fst_5170_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5184_; 
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5184_ == 0)
{
lean_object* v_unused_5185_; 
v_unused_5185_ = lean_ctor_get(v___x_5171_, 0);
lean_dec(v_unused_5185_);
v___x_5173_ = v___x_5171_;
v_isShared_5174_ = v_isSharedCheck_5184_;
goto v_resetjp_5172_;
}
else
{
lean_dec(v___x_5171_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5184_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
uint8_t v___x_5175_; 
v___x_5175_ = lean_unbox(v_fst_5169_);
lean_dec(v_fst_5169_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5178_; 
v___x_5176_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 0, v___x_5176_);
v___x_5178_ = v___x_5173_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
else
{
lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5180_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 0, v___x_5180_);
v___x_5182_ = v___x_5173_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5180_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
lean_dec(v_fst_5169_);
v_a_5186_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5171_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5171_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
default: 
{
lean_object* v_snd_5194_; lean_object* v_snd_5195_; lean_object* v_snd_5196_; lean_object* v_fst_5197_; lean_object* v_fst_5198_; lean_object* v___x_5199_; size_t v_sz_5200_; lean_object* v___x_5201_; 
v_snd_5194_ = lean_ctor_get(v_a_5153_, 1);
lean_del_object(v___x_5155_);
v_snd_5195_ = lean_ctor_get(v_snd_5194_, 1);
v_snd_5196_ = lean_ctor_get(v_snd_5195_, 1);
lean_inc(v_snd_5196_);
v_fst_5197_ = lean_ctor_get(v_a_5153_, 0);
lean_inc(v_fst_5197_);
lean_dec(v_a_5153_);
v_fst_5198_ = lean_ctor_get(v_snd_5196_, 0);
lean_inc(v_fst_5198_);
lean_dec(v_snd_5196_);
v___x_5199_ = lean_box(0);
v_sz_5200_ = lean_array_size(v_fst_5198_);
v___x_5201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5198_, v_sz_5200_, v___x_5143_, v___x_5199_);
lean_dec(v_fst_5198_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5214_; 
v_isSharedCheck_5214_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5214_ == 0)
{
lean_object* v_unused_5215_; 
v_unused_5215_ = lean_ctor_get(v___x_5201_, 0);
lean_dec(v_unused_5215_);
v___x_5203_ = v___x_5201_;
v_isShared_5204_ = v_isSharedCheck_5214_;
goto v_resetjp_5202_;
}
else
{
lean_dec(v___x_5201_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5214_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
uint8_t v___x_5205_; 
v___x_5205_ = lean_unbox(v_fst_5197_);
lean_dec(v_fst_5197_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; lean_object* v___x_5208_; 
v___x_5206_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 0, v___x_5206_);
v___x_5208_ = v___x_5203_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5206_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
else
{
lean_object* v___x_5210_; lean_object* v___x_5212_; 
v___x_5210_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 0, v___x_5210_);
v___x_5212_ = v___x_5203_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_dec(v_fst_5197_);
v_a_5216_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5201_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5201_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
v_a_5225_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5152_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5152_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_dec_ref(v_mods_5133_);
lean_dec_ref(v_args_5131_);
v_a_5233_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5140_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5140_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
else
{
lean_object* v___x_5241_; lean_object* v___x_5242_; 
lean_dec_ref(v_mods_5133_);
lean_dec_ref(v_args_5131_);
v___x_5241_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__2));
v___x_5242_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5241_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5250_; 
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5250_ == 0)
{
lean_object* v_unused_5251_; 
v_unused_5251_ = lean_ctor_get(v___x_5242_, 0);
lean_dec(v_unused_5251_);
v___x_5244_ = v___x_5242_;
v_isShared_5245_ = v_isSharedCheck_5250_;
goto v_resetjp_5243_;
}
else
{
lean_dec(v___x_5242_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5250_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5246_; lean_object* v___x_5248_; 
v___x_5246_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5245_ == 0)
{
lean_ctor_set(v___x_5244_, 0, v___x_5246_);
v___x_5248_ = v___x_5244_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
else
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
v_a_5252_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5242_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5242_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lake_BuiltinLint_run(v_args_5260_);
return v_res_5262_;
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
