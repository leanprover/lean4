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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
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
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
extern lean_object* l_Lean_declRangeExt;
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
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
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
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* lean_compacted_region_free(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0;
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3;
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
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_value;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18;
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_value;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object* v___dummy_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v_res_524_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_528_);
lean_dec_ref(v_s_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
return v_x_530_;
}
else
{
lean_object* v_key_532_; lean_object* v_value_533_; lean_object* v_tail_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_key_532_ = lean_ctor_get(v_x_531_, 0);
v_value_533_ = lean_ctor_get(v_x_531_, 1);
v_tail_534_ = lean_ctor_get(v_x_531_, 2);
lean_inc(v_value_533_);
lean_inc(v_key_532_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_key_532_);
lean_ctor_set(v___x_535_, 1, v_value_533_);
v___x_536_ = lean_array_push(v_x_530_, v___x_535_);
v_x_530_ = v___x_536_;
v_x_531_ = v_tail_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_538_, v_x_539_);
lean_dec(v_x_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, lean_object* v_b_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; 
v___x_546_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
v___x_547_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_544_, v___x_546_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_542_, v___x_548_);
v_i_542_ = v___x_549_;
v_b_544_ = v___x_547_;
goto _start;
}
else
{
return v_b_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_, lean_object* v_b_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_551_, v_i_boxed_555_, v_stop_boxed_556_, v_b_554_);
lean_dec_ref(v_as_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_558_){
_start:
{
lean_object* v___x_560_; lean_object* v_putStr_561_; lean_object* v___x_562_; 
v___x_560_ = lean_get_stderr();
v_putStr_561_ = lean_ctor_get(v___x_560_, 4);
lean_inc_ref(v_putStr_561_);
lean_dec_ref(v___x_560_);
v___x_562_ = lean_apply_2(v_putStr_561_, v_s_558_, lean_box(0));
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_566_){
_start:
{
uint32_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = 10;
v___x_569_ = lean_string_push(v_s_566_, v___x_568_);
v___x_570_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
return v_x_574_;
}
else
{
lean_object* v_key_576_; lean_object* v_value_577_; lean_object* v_tail_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_key_576_ = lean_ctor_get(v_x_575_, 0);
v_value_577_ = lean_ctor_get(v_x_575_, 1);
v_tail_578_ = lean_ctor_get(v_x_575_, 2);
lean_inc(v_value_577_);
lean_inc(v_key_576_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_key_576_);
lean_ctor_set(v___x_579_, 1, v_value_577_);
v___x_580_ = lean_array_push(v_x_574_, v___x_579_);
v_x_574_ = v___x_580_;
v_x_575_ = v_tail_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_582_, v_x_583_);
lean_dec(v_x_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_585_, size_t v_i_586_, size_t v_stop_587_, lean_object* v_b_588_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_eq(v_i_586_, v_stop_587_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; size_t v___x_592_; size_t v___x_593_; 
v___x_590_ = lean_array_uget_borrowed(v_as_585_, v_i_586_);
v___x_591_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_588_, v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_586_, v___x_592_);
v_i_586_ = v___x_593_;
v_b_588_ = v___x_591_;
goto _start;
}
else
{
return v_b_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_595_, lean_object* v_i_596_, lean_object* v_stop_597_, lean_object* v_b_598_){
_start:
{
size_t v_i_boxed_599_; size_t v_stop_boxed_600_; lean_object* v_res_601_; 
v_i_boxed_599_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_stop_boxed_600_ = lean_unbox_usize(v_stop_597_);
lean_dec(v_stop_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_595_, v_i_boxed_599_, v_stop_boxed_600_, v_b_598_);
lean_dec_ref(v_as_595_);
return v_res_601_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
lean_object* v_fst_604_; lean_object* v_fst_605_; uint8_t v___x_606_; 
v_fst_604_ = lean_ctor_get(v_b_603_, 0);
v_fst_605_ = lean_ctor_get(v_a_602_, 0);
v___x_606_ = lean_nat_dec_lt(v_fst_604_, v_fst_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_607_, v_b_608_);
lean_dec_ref(v_b_608_);
lean_dec_ref(v_a_607_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_611_, lean_object* v_pivot_612_, lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v_k_615_, v_hi_611_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v_k_615_);
v___x_617_ = lean_array_fswap(v_as_613_, v_i_614_, v_hi_611_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_i_614_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v_fst_619_; lean_object* v___x_620_; lean_object* v_fst_621_; uint8_t v___x_622_; 
v_fst_619_ = lean_ctor_get(v_pivot_612_, 0);
v___x_620_ = lean_array_fget_borrowed(v_as_613_, v_k_615_);
v_fst_621_ = lean_ctor_get(v___x_620_, 0);
v___x_622_ = lean_nat_dec_lt(v_fst_619_, v_fst_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_k_615_, v___x_623_);
lean_dec(v_k_615_);
v_k_615_ = v___x_624_;
goto _start;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_array_fswap(v_as_613_, v_i_614_, v_k_615_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_i_614_, v___x_627_);
lean_dec(v_i_614_);
v___x_629_ = lean_nat_add(v_k_615_, v___x_627_);
lean_dec(v_k_615_);
v_as_613_ = v___x_626_;
v_i_614_ = v___x_628_;
v_k_615_ = v___x_629_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_631_, lean_object* v_pivot_632_, lean_object* v_as_633_, lean_object* v_i_634_, lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_631_, v_pivot_632_, v_as_633_, v_i_634_, v_k_635_);
lean_dec_ref(v_pivot_632_);
lean_dec(v_hi_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_637_, lean_object* v_as_638_, lean_object* v_lo_639_, lean_object* v_hi_640_){
_start:
{
lean_object* v___y_642_; uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_lt(v_lo_639_, v_hi_640_);
if (v___x_652_ == 0)
{
lean_dec(v_lo_639_);
return v_as_638_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_mid_655_; lean_object* v___y_657_; lean_object* v___y_663_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_653_ = lean_nat_add(v_lo_639_, v_hi_640_);
v___x_654_ = lean_unsigned_to_nat(1u);
v_mid_655_ = lean_nat_shiftr(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
v___x_668_ = lean_array_fget_borrowed(v_as_638_, v_mid_655_);
v___x_669_ = lean_array_fget_borrowed(v_as_638_, v_lo_639_);
v___x_670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
v___y_663_ = v_as_638_;
goto v___jp_662_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_array_fswap(v_as_638_, v_lo_639_, v_mid_655_);
v___y_663_ = v___x_671_;
goto v___jp_662_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_fget_borrowed(v___y_657_, v_mid_655_);
v___x_659_ = lean_array_fget_borrowed(v___y_657_, v_hi_640_);
v___x_660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_dec(v_mid_655_);
v___y_642_ = v___y_657_;
goto v___jp_641_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_array_fswap(v___y_657_, v_mid_655_, v_hi_640_);
lean_dec(v_mid_655_);
v___y_642_ = v___x_661_;
goto v___jp_641_;
}
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_array_fget_borrowed(v___y_663_, v_hi_640_);
v___x_665_ = lean_array_fget_borrowed(v___y_663_, v_lo_639_);
v___x_666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
v___y_657_ = v___y_663_;
goto v___jp_656_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_array_fswap(v___y_663_, v_lo_639_, v_hi_640_);
v___y_657_ = v___x_667_;
goto v___jp_656_;
}
}
}
v___jp_641_:
{
lean_object* v_pivot_643_; lean_object* v___x_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; uint8_t v___x_647_; 
v_pivot_643_ = lean_array_fget(v___y_642_, v_hi_640_);
lean_inc_n(v_lo_639_, 2);
v___x_644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_640_, v_pivot_643_, v___y_642_, v_lo_639_, v_lo_639_);
lean_dec(v_pivot_643_);
v_fst_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_fst_645_);
v_snd_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_snd_646_);
lean_dec_ref(v___x_644_);
v___x_647_ = lean_nat_dec_le(v_hi_640_, v_fst_645_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_637_, v_snd_646_, v_lo_639_, v_fst_645_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_fst_645_, v___x_649_);
lean_dec(v_fst_645_);
v_as_638_ = v___x_648_;
v_lo_639_ = v___x_650_;
goto _start;
}
else
{
lean_dec(v_fst_645_);
lean_dec(v_lo_639_);
return v_snd_646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_672_, lean_object* v_as_673_, lean_object* v_lo_674_, lean_object* v_hi_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_672_, v_as_673_, v_lo_674_, v_hi_675_);
lean_dec(v_hi_675_);
lean_dec(v_n_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_677_, lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v_a_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_it_683_; lean_object* v_startInclusive_684_; lean_object* v_endExclusive_685_; 
if (lean_obj_tag(v_a_680_) == 0)
{
lean_object* v_currPos_689_; lean_object* v_searcher_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_713_; 
v_currPos_689_ = lean_ctor_get(v_a_680_, 0);
v_searcher_690_ = lean_ctor_get(v_a_680_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_713_ == 0)
{
v___x_692_ = v_a_680_;
v_isShared_693_ = v_isSharedCheck_713_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_searcher_690_);
lean_inc(v_currPos_689_);
lean_dec(v_a_680_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_713_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v_decide_694_; 
v_decide_694_ = lean_nat_dec_eq(v_searcher_690_, v___x_679_);
if (v_decide_694_ == 0)
{
uint32_t v___x_695_; uint32_t v___x_696_; uint8_t v___x_697_; 
v___x_695_ = 10;
v___x_696_ = lean_string_utf8_get_fast(v_a_677_, v_searcher_690_);
v___x_697_ = lean_uint32_dec_eq(v___x_696_, v___x_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_string_utf8_next_fast(v_a_677_, v_searcher_690_);
lean_dec(v_searcher_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_698_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_currPos_689_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_702_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v_a_680_ = v___x_700_;
goto _start;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_slice_706_; lean_object* v_nextIt_708_; 
v___x_703_ = lean_string_utf8_next_fast(v_a_677_, v_searcher_690_);
v___x_704_ = lean_nat_sub(v___x_703_, v_searcher_690_);
v___x_705_ = lean_nat_add(v_searcher_690_, v___x_704_);
lean_dec(v___x_704_);
v_slice_706_ = l_String_Slice_subslice_x21(v___x_678_, v_currPos_689_, v_searcher_690_);
lean_inc(v___x_705_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_705_);
lean_ctor_set(v___x_692_, 0, v___x_705_);
v_nextIt_708_ = v___x_692_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_705_);
v_nextIt_708_ = v_reuseFailAlloc_711_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v_startInclusive_709_; lean_object* v_endExclusive_710_; 
v_startInclusive_709_ = lean_ctor_get(v_slice_706_, 0);
lean_inc(v_startInclusive_709_);
v_endExclusive_710_ = lean_ctor_get(v_slice_706_, 1);
lean_inc(v_endExclusive_710_);
lean_dec_ref(v_slice_706_);
v_it_683_ = v_nextIt_708_;
v_startInclusive_684_ = v_startInclusive_709_;
v_endExclusive_685_ = v_endExclusive_710_;
goto v___jp_682_;
}
}
}
else
{
lean_object* v___x_712_; 
lean_del_object(v___x_692_);
lean_dec(v_searcher_690_);
v___x_712_ = lean_box(1);
lean_inc(v___x_679_);
v_it_683_ = v___x_712_;
v_startInclusive_684_ = v_currPos_689_;
v_endExclusive_685_ = v___x_679_;
goto v___jp_682_;
}
}
}
else
{
lean_dec(v___x_679_);
lean_dec_ref(v_a_677_);
return v_b_681_;
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref(v_a_677_);
v___x_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_686_, 0, v_a_677_);
lean_ctor_set(v___x_686_, 1, v_startInclusive_684_);
lean_ctor_set(v___x_686_, 2, v_endExclusive_685_);
v___x_687_ = lean_array_push(v_b_681_, v___x_686_);
v_a_680_ = v_it_683_;
v_b_681_ = v___x_687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v_a_717_, lean_object* v_b_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_714_, v___x_715_, v___x_716_, v_a_717_, v_b_718_);
lean_dec_ref(v___x_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_723_ == 0)
{
return v_bs_722_;
}
else
{
lean_object* v_v_724_; lean_object* v___x_725_; lean_object* v_bs_x27_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v_v_724_ = lean_array_uget(v_bs_722_, v_i_721_);
v___x_725_ = lean_unsigned_to_nat(0u);
v_bs_x27_726_ = lean_array_uset(v_bs_722_, v_i_721_, v___x_725_);
v___x_727_ = l_String_Slice_toString(v_v_724_);
lean_dec(v_v_724_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_721_, v___x_728_);
v___x_730_ = lean_array_uset(v_bs_x27_726_, v_i_721_, v___x_727_);
v_i_721_ = v___x_729_;
v_bs_722_ = v___x_730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_732_, lean_object* v_i_733_, lean_object* v_bs_734_){
_start:
{
size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_sz_boxed_735_ = lean_unbox_usize(v_sz_732_);
lean_dec(v_sz_732_);
v_i_boxed_736_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_735_, v_i_boxed_736_, v_bs_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
return v_x_738_;
}
else
{
lean_object* v_key_740_; lean_object* v_value_741_; lean_object* v_tail_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_765_; 
v_key_740_ = lean_ctor_get(v_x_739_, 0);
v_value_741_ = lean_ctor_get(v_x_739_, 1);
v_tail_742_ = lean_ctor_get(v_x_739_, 2);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_765_ == 0)
{
v___x_744_ = v_x_739_;
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_tail_742_);
lean_inc(v_value_741_);
lean_inc(v_key_740_);
lean_dec(v_x_739_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; uint64_t v_fold_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_746_ = lean_array_get_size(v_x_738_);
v___x_747_ = lean_uint64_of_nat(v_key_740_);
v___x_748_ = 32ULL;
v___x_749_ = lean_uint64_shift_right(v___x_747_, v___x_748_);
v_fold_750_ = lean_uint64_xor(v___x_747_, v___x_749_);
v___x_751_ = 16ULL;
v___x_752_ = lean_uint64_shift_right(v_fold_750_, v___x_751_);
v___x_753_ = lean_uint64_xor(v_fold_750_, v___x_752_);
v___x_754_ = lean_uint64_to_usize(v___x_753_);
v___x_755_ = lean_usize_of_nat(v___x_746_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_sub(v___x_755_, v___x_756_);
v___x_758_ = lean_usize_land(v___x_754_, v___x_757_);
v___x_759_ = lean_array_uget_borrowed(v_x_738_, v___x_758_);
lean_inc(v___x_759_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 2, v___x_759_);
v___x_761_ = v___x_744_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_key_740_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_value_741_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v___x_759_);
v___x_761_ = v_reuseFailAlloc_764_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = lean_array_uset(v_x_738_, v___x_758_, v___x_761_);
v_x_738_ = v___x_762_;
v_x_739_ = v_tail_742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_766_, lean_object* v_source_767_, lean_object* v_target_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_source_767_);
v___x_770_ = lean_nat_dec_lt(v_i_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec_ref(v_source_767_);
lean_dec(v_i_766_);
return v_target_768_;
}
else
{
lean_object* v_es_771_; lean_object* v___x_772_; lean_object* v_source_773_; lean_object* v_target_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_es_771_ = lean_array_fget(v_source_767_, v_i_766_);
v___x_772_ = lean_box(0);
v_source_773_ = lean_array_fset(v_source_767_, v_i_766_, v___x_772_);
v_target_774_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_768_, v_es_771_);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_add(v_i_766_, v___x_775_);
lean_dec(v_i_766_);
v_i_766_ = v___x_776_;
v_source_767_ = v_source_773_;
v_target_768_ = v_target_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_nbuckets_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_779_ = lean_array_get_size(v_data_778_);
v___x_780_ = lean_unsigned_to_nat(2u);
v_nbuckets_781_ = lean_nat_mul(v___x_779_, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_box(0);
v___x_784_ = lean_mk_array(v_nbuckets_781_, v___x_783_);
v___x_785_ = lean_array_propagate_mark(v_data_778_, v___x_784_);
v___x_786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_782_, v_data_778_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
else
{
lean_object* v_key_790_; lean_object* v_tail_791_; uint8_t v___x_792_; 
v_key_790_ = lean_ctor_get(v_x_788_, 0);
v_tail_791_ = lean_ctor_get(v_x_788_, 2);
v___x_792_ = lean_nat_dec_eq(v_key_790_, v_a_787_);
if (v___x_792_ == 0)
{
v_x_788_ = v_tail_791_;
goto _start;
}
else
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_794_, lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_794_, v_x_795_);
lean_dec(v_x_795_);
lean_dec(v_a_794_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_dec(v_b_799_);
lean_dec(v_a_798_);
return v_x_800_;
}
else
{
lean_object* v_key_801_; lean_object* v_value_802_; lean_object* v_tail_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_key_801_ = lean_ctor_get(v_x_800_, 0);
v_value_802_ = lean_ctor_get(v_x_800_, 1);
v_tail_803_ = lean_ctor_get(v_x_800_, 2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_815_ == 0)
{
v___x_805_ = v_x_800_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_tail_803_);
lean_inc(v_value_802_);
lean_inc(v_key_801_);
lean_dec(v_x_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_eq(v_key_801_, v_a_798_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_798_, v_b_799_, v_tail_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 2, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_key_801_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_value_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_813_; 
lean_dec(v_value_802_);
lean_dec(v_key_801_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_b_799_);
lean_ctor_set(v___x_805_, 0, v_a_798_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_798_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_b_799_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_tail_803_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v_size_819_; lean_object* v_buckets_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_863_; 
v_size_819_ = lean_ctor_get(v_m_816_, 0);
v_buckets_820_ = lean_ctor_get(v_m_816_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_m_816_);
if (v_isSharedCheck_863_ == 0)
{
v___x_822_ = v_m_816_;
v_isShared_823_ = v_isSharedCheck_863_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_buckets_820_);
lean_inc(v_size_819_);
lean_dec(v_m_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_863_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_bkt_837_; uint8_t v___x_838_; 
v___x_824_ = lean_array_get_size(v_buckets_820_);
v___x_825_ = lean_uint64_of_nat(v_a_817_);
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___x_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___x_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_824_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v_bkt_837_ = lean_array_uget_borrowed(v_buckets_820_, v___x_836_);
v___x_838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_817_, v_bkt_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v_size_x27_840_; lean_object* v___x_841_; lean_object* v_buckets_x27_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_839_ = lean_unsigned_to_nat(1u);
v_size_x27_840_ = lean_nat_add(v_size_819_, v___x_839_);
lean_dec(v_size_819_);
lean_inc(v_bkt_837_);
v___x_841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_841_, 0, v_a_817_);
lean_ctor_set(v___x_841_, 1, v_b_818_);
lean_ctor_set(v___x_841_, 2, v_bkt_837_);
v_buckets_x27_842_ = lean_array_uset(v_buckets_820_, v___x_836_, v___x_841_);
v___x_843_ = lean_unsigned_to_nat(4u);
v___x_844_ = lean_nat_mul(v_size_x27_840_, v___x_843_);
v___x_845_ = lean_unsigned_to_nat(3u);
v___x_846_ = lean_nat_div(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_array_get_size(v_buckets_x27_842_);
v___x_848_ = lean_nat_dec_le(v___x_846_, v___x_847_);
lean_dec(v___x_846_);
if (v___x_848_ == 0)
{
lean_object* v_val_849_; lean_object* v___x_851_; 
v_val_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_842_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_val_849_);
lean_ctor_set(v___x_822_, 0, v_size_x27_840_);
v___x_851_ = v___x_822_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_size_x27_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_val_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v___x_854_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_buckets_x27_842_);
lean_ctor_set(v___x_822_, 0, v_size_x27_840_);
v___x_854_ = v___x_822_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_size_x27_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_buckets_x27_842_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v___x_856_; lean_object* v_buckets_x27_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_inc(v_bkt_837_);
v___x_856_ = lean_box(0);
v_buckets_x27_857_ = lean_array_uset(v_buckets_820_, v___x_836_, v___x_856_);
v___x_858_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_817_, v_b_818_, v_bkt_837_);
v___x_859_ = lean_array_uset(v_buckets_x27_857_, v___x_836_, v___x_858_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_859_);
v___x_861_ = v___x_822_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_size_819_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_864_, lean_object* v_as_865_, size_t v_i_866_, size_t v_stop_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_eq(v_i_866_, v_stop_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_array_uget_borrowed(v_as_865_, v_i_866_);
v___x_870_ = lean_name_eq(v_a_864_, v___x_869_);
if (v___x_870_ == 0)
{
size_t v___x_871_; size_t v___x_872_; 
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_866_, v___x_871_);
v_i_866_ = v___x_872_;
goto _start;
}
else
{
return v___x_870_;
}
}
else
{
uint8_t v___x_874_; 
v___x_874_ = 0;
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_875_, lean_object* v_as_876_, lean_object* v_i_877_, lean_object* v_stop_878_){
_start:
{
size_t v_i_boxed_879_; size_t v_stop_boxed_880_; uint8_t v_res_881_; lean_object* v_r_882_; 
v_i_boxed_879_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_stop_boxed_880_ = lean_unbox_usize(v_stop_878_);
lean_dec(v_stop_878_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_875_, v_as_876_, v_i_boxed_879_, v_stop_boxed_880_);
lean_dec_ref(v_as_876_);
lean_dec(v_a_875_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_array_get_size(v_as_883_);
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
return v___x_887_;
}
else
{
if (v___x_887_ == 0)
{
return v___x_887_;
}
else
{
size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v___x_888_ = ((size_t)0ULL);
v___x_889_ = lean_usize_of_nat(v___x_886_);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_884_, v_as_883_, v___x_888_, v___x_889_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_as_891_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_895_, lean_object* v_fallback_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_inc(v_fallback_896_);
return v_fallback_896_;
}
else
{
lean_object* v_key_898_; lean_object* v_value_899_; lean_object* v_tail_900_; uint8_t v___x_901_; 
v_key_898_ = lean_ctor_get(v_x_897_, 0);
v_value_899_ = lean_ctor_get(v_x_897_, 1);
v_tail_900_ = lean_ctor_get(v_x_897_, 2);
v___x_901_ = lean_nat_dec_eq(v_key_898_, v_a_895_);
if (v___x_901_ == 0)
{
v_x_897_ = v_tail_900_;
goto _start;
}
else
{
lean_inc(v_value_899_);
return v_value_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_903_, lean_object* v_fallback_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_903_, v_fallback_904_, v_x_905_);
lean_dec(v_x_905_);
lean_dec(v_fallback_904_);
lean_dec(v_a_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_907_, lean_object* v_a_908_, lean_object* v_fallback_909_){
_start:
{
lean_object* v_buckets_910_; lean_object* v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v_fold_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_buckets_910_ = lean_ctor_get(v_m_907_, 1);
v___x_911_ = lean_array_get_size(v_buckets_910_);
v___x_912_ = lean_uint64_of_nat(v_a_908_);
v___x_913_ = 32ULL;
v___x_914_ = lean_uint64_shift_right(v___x_912_, v___x_913_);
v_fold_915_ = lean_uint64_xor(v___x_912_, v___x_914_);
v___x_916_ = 16ULL;
v___x_917_ = lean_uint64_shift_right(v_fold_915_, v___x_916_);
v___x_918_ = lean_uint64_xor(v_fold_915_, v___x_917_);
v___x_919_ = lean_uint64_to_usize(v___x_918_);
v___x_920_ = lean_usize_of_nat(v___x_911_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_sub(v___x_920_, v___x_921_);
v___x_923_ = lean_usize_land(v___x_919_, v___x_922_);
v___x_924_ = lean_array_uget_borrowed(v_buckets_910_, v___x_923_);
v___x_925_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_908_, v_fallback_909_, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_926_, lean_object* v_a_927_, lean_object* v_fallback_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_926_, v_a_927_, v_fallback_928_);
lean_dec(v_fallback_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_m_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_935_);
return v___x_943_;
}
else
{
lean_object* v_a_944_; lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_a_944_ = lean_array_uget_borrowed(v_as_932_, v_i_934_);
v_fst_945_ = lean_ctor_get(v_a_944_, 0);
v_snd_946_ = lean_ctor_get(v_a_944_, 1);
v___x_947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_935_, v_fst_945_, v___x_947_);
v___x_949_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_948_, v_snd_946_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_inc(v_snd_946_);
v___x_950_ = lean_array_push(v___x_948_, v_snd_946_);
lean_inc(v_fst_945_);
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_935_, v_fst_945_, v___x_950_);
v_a_938_ = v___x_951_;
goto v___jp_937_;
}
else
{
lean_dec(v___x_948_);
v_a_938_ = v_b_935_;
goto v___jp_937_;
}
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_934_, v___x_939_);
v_i_934_ = v___x_940_;
v_b_935_ = v_a_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_952_, lean_object* v_sz_953_, lean_object* v_i_954_, lean_object* v_b_955_, lean_object* v___y_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_953_);
lean_dec(v_sz_953_);
v_i_boxed_958_ = lean_unbox_usize(v_i_954_);
lean_dec(v_i_954_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_952_, v_sz_boxed_957_, v_i_boxed_958_, v_b_955_);
lean_dec_ref(v_as_952_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_putStr_963_; lean_object* v___x_964_; 
v___x_962_ = lean_get_stdout();
v_putStr_963_ = lean_ctor_get(v___x_962_, 4);
lean_inc_ref(v_putStr_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = lean_apply_2(v_putStr_963_, v_s_960_, lean_box(0));
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_968_){
_start:
{
uint32_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = 10;
v___x_971_ = lean_string_push(v_s_968_, v___x_970_);
v___x_972_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_973_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_977_, v___x_976_);
v___x_980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_978_, v___x_976_);
v___x_981_ = lean_string_dec_lt(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
lean_dec_ref(v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_982_, lean_object* v_a_983_, lean_object* v_b_984_){
_start:
{
uint8_t v___x_11514__boxed_985_; uint8_t v_res_986_; lean_object* v_r_987_; 
v___x_11514__boxed_985_ = lean_unbox(v___x_982_);
v_res_986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11514__boxed_985_, v_a_983_, v_b_984_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v_hi_990_, lean_object* v_pivot_991_, lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_k_994_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = lean_nat_dec_lt(v_k_994_, v_hi_990_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_k_994_);
lean_dec(v_pivot_991_);
v___x_996_ = lean_array_fswap(v_as_992_, v_i_993_, v_hi_990_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_i_993_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
return v___x_997_;
}
else
{
uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_998_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
v___x_999_ = lean_array_fget_borrowed(v_as_992_, v_k_994_);
lean_inc(v___x_999_);
v___x_1000_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_999_, v___x_998_);
lean_inc(v_pivot_991_);
v___x_1001_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_991_, v___x_998_);
v___x_1002_ = lean_string_dec_lt(v___x_1000_, v___x_1001_);
lean_dec_ref(v___x_1001_);
lean_dec_ref(v___x_1000_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_k_994_, v___x_1003_);
lean_dec(v_k_994_);
v_k_994_ = v___x_1004_;
goto _start;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = lean_array_fswap(v_as_992_, v_i_993_, v_k_994_);
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_i_993_, v___x_1007_);
lean_dec(v_i_993_);
v___x_1009_ = lean_nat_add(v_k_994_, v___x_1007_);
lean_dec(v_k_994_);
v_as_992_ = v___x_1006_;
v_i_993_ = v___x_1008_;
v_k_994_ = v___x_1009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_hi_1013_, lean_object* v_pivot_1014_, lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1011_, v___x_1012_, v_hi_1013_, v_pivot_1014_, v_as_1015_, v_i_1016_, v_k_1017_);
lean_dec(v_hi_1013_);
lean_dec(v___x_1012_);
lean_dec(v___x_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v_n_1021_, lean_object* v_as_1022_, lean_object* v_lo_1023_, lean_object* v_hi_1024_){
_start:
{
lean_object* v___y_1026_; uint8_t v___x_1036_; 
v___x_1036_ = lean_nat_dec_lt(v_lo_1023_, v_hi_1024_);
if (v___x_1036_ == 0)
{
lean_dec(v_lo_1023_);
return v_as_1022_;
}
else
{
uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_mid_1040_; lean_object* v___y_1042_; lean_object* v___y_1048_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1037_ = lean_nat_dec_lt(v___x_1019_, v___x_1020_);
v___x_1038_ = lean_nat_add(v_lo_1023_, v_hi_1024_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v_mid_1040_ = lean_nat_shiftr(v___x_1038_, v___x_1039_);
lean_dec(v___x_1038_);
v___x_1053_ = lean_array_fget_borrowed(v_as_1022_, v_mid_1040_);
v___x_1054_ = lean_array_fget_borrowed(v_as_1022_, v_lo_1023_);
lean_inc(v___x_1054_);
lean_inc(v___x_1053_);
v___x_1055_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1037_, v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
v___y_1048_ = v_as_1022_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_array_fswap(v_as_1022_, v_lo_1023_, v_mid_1040_);
v___y_1048_ = v___x_1056_;
goto v___jp_1047_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = lean_array_fget_borrowed(v___y_1042_, v_mid_1040_);
v___x_1044_ = lean_array_fget_borrowed(v___y_1042_, v_hi_1024_);
lean_inc(v___x_1044_);
lean_inc(v___x_1043_);
v___x_1045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1037_, v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v_mid_1040_);
v___y_1026_ = v___y_1042_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_fswap(v___y_1042_, v_mid_1040_, v_hi_1024_);
lean_dec(v_mid_1040_);
v___y_1026_ = v___x_1046_;
goto v___jp_1025_;
}
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = lean_array_fget_borrowed(v___y_1048_, v_hi_1024_);
v___x_1050_ = lean_array_fget_borrowed(v___y_1048_, v_lo_1023_);
lean_inc(v___x_1050_);
lean_inc(v___x_1049_);
v___x_1051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1037_, v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
v___y_1042_ = v___y_1048_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_array_fswap(v___y_1048_, v_lo_1023_, v_hi_1024_);
v___y_1042_ = v___x_1052_;
goto v___jp_1041_;
}
}
}
v___jp_1025_:
{
lean_object* v_pivot_1027_; lean_object* v___x_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; uint8_t v___x_1031_; 
v_pivot_1027_ = lean_array_fget(v___y_1026_, v_hi_1024_);
lean_inc_n(v_lo_1023_, 2);
v___x_1028_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1019_, v___x_1020_, v_hi_1024_, v_pivot_1027_, v___y_1026_, v_lo_1023_, v_lo_1023_);
v_fst_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec_ref(v___x_1028_);
v___x_1031_ = lean_nat_dec_le(v_hi_1024_, v_fst_1029_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1019_, v___x_1020_, v_n_1021_, v_snd_1030_, v_lo_1023_, v_fst_1029_);
v___x_1033_ = lean_unsigned_to_nat(1u);
v___x_1034_ = lean_nat_add(v_fst_1029_, v___x_1033_);
lean_dec(v_fst_1029_);
v_as_1022_ = v___x_1032_;
v_lo_1023_ = v___x_1034_;
goto _start;
}
else
{
lean_dec(v_fst_1029_);
lean_dec(v_lo_1023_);
return v_snd_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_n_1059_, lean_object* v_as_1060_, lean_object* v_lo_1061_, lean_object* v_hi_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1057_, v___x_1058_, v_n_1059_, v_as_1060_, v_lo_1061_, v_hi_1062_);
lean_dec(v_hi_1062_);
lean_dec(v_n_1059_);
lean_dec(v___x_1058_);
lean_dec(v___x_1057_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v___x_1068_, size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_bs_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v___x_1066_);
return v_bs_1071_;
}
else
{
uint8_t v___x_1073_; lean_object* v_v_1074_; lean_object* v___x_1075_; lean_object* v_bs_x27_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1073_ = lean_nat_dec_lt(v___x_1067_, v___x_1068_);
v_v_1074_ = lean_array_uget(v_bs_1071_, v_i_1070_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v_bs_x27_1076_ = lean_array_uset(v_bs_1071_, v_i_1070_, v___x_1075_);
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1066_);
v___x_1078_ = lean_string_append(v___x_1066_, v___x_1077_);
v___x_1079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1074_, v___x_1073_);
v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1082_ = lean_string_append(v___x_1080_, v___x_1081_);
v___x_1083_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_add(v_i_1070_, v___x_1085_);
v___x_1087_ = lean_array_uset(v_bs_x27_1076_, v_i_1070_, v___x_1084_);
v_i_1070_ = v___x_1086_;
v_bs_1071_ = v___x_1087_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1089_, lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_bs_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1089_, v___x_1090_, v___x_1091_, v_sz_boxed_1095_, v_i_boxed_1096_, v_bs_1094_);
lean_dec(v___x_1091_);
lean_dec(v___x_1090_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1098_, size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_b_1101_){
_start:
{
lean_object* v_a_1104_; uint8_t v___x_1108_; 
v___x_1108_ = lean_usize_dec_lt(v_i_1100_, v_sz_1099_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_b_1101_);
return v___x_1109_;
}
else
{
lean_object* v_a_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1153_; 
v_a_1110_ = lean_array_uget_borrowed(v_as_1098_, v_i_1100_);
v_fst_1111_ = lean_ctor_get(v_a_1110_, 0);
v_snd_1112_ = lean_ctor_get(v_a_1110_, 1);
v_fst_1113_ = lean_ctor_get(v_b_1101_, 0);
v_snd_1114_ = lean_ctor_get(v_b_1101_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_b_1101_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1116_ = v_b_1101_;
v_isShared_1117_ = v_isSharedCheck_1153_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snd_1114_);
lean_inc(v_fst_1113_);
lean_dec(v_b_1101_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1153_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_sub(v_fst_1111_, v___x_1118_);
v___x_1120_ = lean_array_get_size(v_fst_1113_);
v___x_1121_ = lean_nat_dec_lt(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v___x_1119_);
if (v_isShared_1117_ == 0)
{
v___x_1123_ = v___x_1116_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_fst_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_snd_1114_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v_a_1104_ = v___x_1123_;
goto v___jp_1103_;
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___y_1129_; lean_object* v___x_1142_; lean_object* v___y_1144_; lean_object* v___y_1145_; uint8_t v___x_1147_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_fget_borrowed(v_fst_1113_, v___x_1119_);
v___x_1127_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1126_);
v___x_1142_ = lean_array_get_size(v_snd_1112_);
v___x_1147_ = lean_nat_dec_eq(v___x_1142_, v___x_1125_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___y_1150_; uint8_t v___x_1152_; 
v___x_1148_ = lean_nat_sub(v___x_1142_, v___x_1118_);
v___x_1152_ = lean_nat_dec_le(v___x_1125_, v___x_1148_);
if (v___x_1152_ == 0)
{
lean_inc(v___x_1148_);
v___y_1150_ = v___x_1148_;
goto v___jp_1149_;
}
else
{
v___y_1150_ = v___x_1125_;
goto v___jp_1149_;
}
v___jp_1149_:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_nat_dec_le(v___y_1150_, v___x_1148_);
if (v___x_1151_ == 0)
{
lean_dec(v___x_1148_);
lean_inc(v___y_1150_);
v___y_1144_ = v___y_1150_;
v___y_1145_ = v___y_1150_;
goto v___jp_1143_;
}
else
{
v___y_1144_ = v___y_1150_;
v___y_1145_ = v___x_1148_;
goto v___jp_1143_;
}
}
}
else
{
lean_inc(v_snd_1112_);
v___y_1129_ = v_snd_1112_;
goto v___jp_1128_;
}
v___jp_1128_:
{
size_t v_sz_1130_; size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v_sz_1130_ = lean_array_size(v___y_1129_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1127_, v___x_1119_, v___x_1120_, v_sz_1130_, v___x_1131_, v___y_1129_);
lean_inc(v___x_1119_);
v___x_1133_ = l_Array_extract___redArg(v_fst_1113_, v___x_1125_, v___x_1119_);
v___x_1134_ = l_Array_append___redArg(v___x_1133_, v___x_1132_);
v___x_1135_ = l_Array_extract___redArg(v_fst_1113_, v___x_1119_, v___x_1120_);
lean_dec(v_fst_1113_);
v___x_1136_ = l_Array_append___redArg(v___x_1134_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_array_get_size(v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1138_ = lean_nat_add(v_snd_1114_, v___x_1137_);
lean_dec(v_snd_1114_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v___x_1138_);
lean_ctor_set(v___x_1116_, 0, v___x_1136_);
v___x_1140_ = v___x_1116_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v_a_1104_ = v___x_1140_;
goto v___jp_1103_;
}
}
v___jp_1143_:
{
lean_object* v___x_1146_; 
lean_inc(v_snd_1112_);
v___x_1146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1119_, v___x_1120_, v___x_1142_, v_snd_1112_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
v___y_1129_ = v___x_1146_;
goto v___jp_1128_;
}
}
}
}
v___jp_1103_:
{
size_t v___x_1105_; size_t v___x_1106_; 
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_i_1100_, v___x_1105_);
v_i_1100_ = v___x_1106_;
v_b_1101_ = v_a_1104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1154_, v_sz_boxed_1159_, v_i_boxed_1160_, v_b_1157_);
lean_dec_ref(v_as_1154_);
return v_res_1161_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_unsigned_to_nat(16u);
v___x_1166_ = lean_mk_array(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1178_, size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_b_1181_){
_start:
{
lean_object* v_a_1184_; uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_b_1181_);
return v___x_1189_;
}
else
{
lean_object* v_a_1190_; lean_object* v_snd_1191_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1300_; 
v_a_1190_ = lean_array_uget_borrowed(v_as_1178_, v_i_1180_);
v_snd_1191_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_snd_1191_);
v_fst_1192_ = lean_ctor_get(v_snd_1191_, 0);
v_snd_1193_ = lean_ctor_get(v_snd_1191_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_snd_1191_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1195_ = v_snd_1191_;
v_isShared_1196_ = v_isSharedCheck_1300_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v_snd_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1300_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___x_1211_; lean_object* v___x_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1197_ = lean_box(0);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3);
v_sz_1213_ = lean_array_size(v_snd_1193_);
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1193_, v_sz_1213_, v___x_1214_, v___x_1212_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = l_IO_FS_readFile(v_fst_1192_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_size_1221_; lean_object* v_buckets_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; size_t v_sz_1226_; lean_object* v___x_1227_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1271_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
lean_dec(v_snd_1193_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_n(v_a_1218_, 2);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = lean_string_utf8_byte_size(v_a_1218_);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1211_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v_size_1221_ = lean_ctor_get(v_a_1216_, 0);
lean_inc(v_size_1221_);
v_buckets_1222_ = lean_ctor_get(v_a_1216_, 1);
lean_inc_ref(v_buckets_1222_);
lean_dec(v_a_1216_);
v___x_1223_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
v___x_1224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1225_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1218_, v___x_1220_, v___x_1219_, v___x_1223_, v___x_1224_);
lean_dec_ref_known(v___x_1220_, 3);
v_sz_1226_ = lean_array_size(v___x_1225_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1226_, v___x_1214_, v___x_1225_);
v___x_1277_ = lean_mk_empty_array_with_capacity(v_size_1221_);
lean_dec(v_size_1221_);
v___x_1278_ = lean_array_get_size(v_buckets_1222_);
v___x_1279_ = lean_nat_dec_lt(v___x_1211_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_buckets_1222_);
v___y_1271_ = v___x_1277_;
goto v___jp_1270_;
}
else
{
size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_usize_of_nat(v___x_1278_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1222_, v___x_1214_, v___x_1280_, v___x_1277_);
lean_dec_ref(v_buckets_1222_);
v___y_1271_ = v___x_1281_;
goto v___jp_1270_;
}
v___jp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___x_1211_);
lean_ctor_set(v___x_1195_, 0, v___x_1227_);
v___x_1232_ = v___x_1195_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1211_);
v___x_1232_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
size_t v_sz_1233_; lean_object* v___x_1234_; 
v_sz_1233_ = lean_array_size(v___y_1230_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1230_, v_sz_1233_, v___x_1214_, v___x_1232_);
lean_dec_ref(v___y_1230_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; uint8_t v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_fst_1236_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_fst_1236_);
v_snd_1237_ = lean_ctor_get(v_a_1235_, 1);
lean_inc(v_snd_1237_);
lean_dec(v_a_1235_);
v___x_1238_ = lean_nat_dec_lt(v___x_1211_, v_snd_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_snd_1237_);
lean_dec(v_fst_1236_);
lean_dec(v_fst_1192_);
v_a_1184_ = v___x_1197_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1237_);
v___x_1240_ = l_Nat_reprFast(v_snd_1237_);
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1243_ = lean_string_append(v___x_1241_, v___x_1242_);
v___x_1244_ = lean_nat_dec_eq(v_snd_1237_, v___y_1229_);
lean_dec(v_snd_1237_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1199_ = v___x_1243_;
v___y_1200_ = v_fst_1236_;
v___y_1201_ = v___x_1245_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1246_; 
v___x_1246_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1199_ = v___x_1243_;
v___y_1200_ = v_fst_1236_;
v___y_1201_ = v___x_1246_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_fst_1192_);
v_a_1247_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1234_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1234_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
v___jp_1256_:
{
lean_object* v___x_1262_; 
v___x_1262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1257_, v___y_1258_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec(v___y_1257_);
v___y_1229_ = v___y_1259_;
v___y_1230_ = v___x_1262_;
goto v___jp_1228_;
}
v___jp_1263_:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_le(v___y_1268_, v___y_1267_);
if (v___x_1269_ == 0)
{
lean_dec(v___y_1267_);
lean_inc(v___y_1268_);
v___y_1257_ = v___y_1264_;
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___y_1268_;
v___y_1261_ = v___y_1268_;
goto v___jp_1256_;
}
else
{
v___y_1257_ = v___y_1264_;
v___y_1258_ = v___y_1265_;
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___y_1268_;
v___y_1261_ = v___y_1267_;
goto v___jp_1256_;
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_array_get_size(v___y_1271_);
v___x_1274_ = lean_nat_dec_eq(v___x_1273_, v___x_1211_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_nat_sub(v___x_1273_, v___x_1272_);
v___x_1276_ = lean_nat_dec_le(v___x_1211_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_inc(v___x_1275_);
v___y_1264_ = v___x_1273_;
v___y_1265_ = v___y_1271_;
v___y_1266_ = v___x_1272_;
v___y_1267_ = v___x_1275_;
v___y_1268_ = v___x_1275_;
goto v___jp_1263_;
}
else
{
v___y_1264_ = v___x_1273_;
v___y_1265_ = v___y_1271_;
v___y_1266_ = v___x_1272_;
v___y_1267_ = v___x_1275_;
v___y_1268_ = v___x_1211_;
goto v___jp_1263_;
}
}
else
{
v___y_1229_ = v___x_1272_;
v___y_1230_ = v___y_1271_;
goto v___jp_1228_;
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec_ref_known(v___x_1217_, 1);
lean_dec(v_a_1216_);
lean_del_object(v___x_1195_);
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1283_ = lean_string_append(v___x_1282_, v_fst_1192_);
lean_dec(v_fst_1192_);
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1285_ = lean_string_append(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_array_get_size(v_snd_1193_);
lean_dec(v_snd_1193_);
v___x_1287_ = l_Nat_reprFast(v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1290_ = lean_string_append(v___x_1288_, v___x_1289_);
v___x_1291_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_dec_ref_known(v___x_1291_, 1);
v_a_1184_ = v___x_1197_;
goto v___jp_1183_;
}
else
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_del_object(v___x_1195_);
lean_dec(v_snd_1193_);
lean_dec(v_fst_1192_);
v_a_1292_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1215_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1215_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
v___jp_1198_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1202_ = lean_string_append(v___y_1199_, v___y_1201_);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0));
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_string_append(v___x_1204_, v_fst_1192_);
v___x_1206_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1));
v___x_1208_ = lean_array_to_list(v___y_1200_);
v___x_1209_ = l_String_intercalate(v___x_1207_, v___x_1208_);
v___x_1210_ = l_IO_FS_writeFile(v_fst_1192_, v___x_1209_);
lean_dec_ref(v___x_1209_);
lean_dec(v_fst_1192_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_dec_ref_known(v___x_1210_, 1);
v_a_1184_ = v___x_1197_;
goto v___jp_1183_;
}
else
{
return v___x_1210_;
}
}
else
{
lean_dec(v___y_1200_);
lean_dec(v_fst_1192_);
return v___x_1206_;
}
}
}
}
v___jp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1180_, v___x_1185_);
v_i_1180_ = v___x_1186_;
v_b_1181_ = v_a_1184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1301_, lean_object* v_sz_1302_, lean_object* v_i_1303_, lean_object* v_b_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1302_);
lean_dec(v_sz_1302_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1301_, v_sz_boxed_1306_, v_i_boxed_1307_, v_b_1304_);
lean_dec_ref(v_as_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = 0;
return v___x_1311_;
}
else
{
lean_object* v_key_1312_; lean_object* v_tail_1313_; uint8_t v___x_1314_; 
v_key_1312_ = lean_ctor_get(v_x_1310_, 0);
v_tail_1313_ = lean_ctor_get(v_x_1310_, 2);
v___x_1314_ = lean_string_dec_eq(v_key_1312_, v_a_1309_);
if (v___x_1314_ == 0)
{
v_x_1310_ = v_tail_1313_;
goto _start;
}
else
{
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1316_, lean_object* v_x_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1316_, v_x_1317_);
lean_dec(v_x_1317_);
lean_dec_ref(v_a_1316_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1320_, lean_object* v_b_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_dec(v_b_1321_);
lean_dec_ref(v_a_1320_);
return v_x_1322_;
}
else
{
lean_object* v_key_1323_; lean_object* v_value_1324_; lean_object* v_tail_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1337_; 
v_key_1323_ = lean_ctor_get(v_x_1322_, 0);
v_value_1324_ = lean_ctor_get(v_x_1322_, 1);
v_tail_1325_ = lean_ctor_get(v_x_1322_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1327_ = v_x_1322_;
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_tail_1325_);
lean_inc(v_value_1324_);
lean_inc(v_key_1323_);
lean_dec(v_x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_string_dec_eq(v_key_1323_, v_a_1320_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1320_, v_b_1321_, v_tail_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 2, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_key_1323_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_value_1324_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v___x_1335_; 
lean_dec(v_value_1324_);
lean_dec(v_key_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_b_1321_);
lean_ctor_set(v___x_1327_, 0, v_a_1320_);
v___x_1335_ = v___x_1327_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_b_1321_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_tail_1325_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 0)
{
return v_x_1338_;
}
else
{
lean_object* v_key_1340_; lean_object* v_value_1341_; lean_object* v_tail_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1365_; 
v_key_1340_ = lean_ctor_get(v_x_1339_, 0);
v_value_1341_ = lean_ctor_get(v_x_1339_, 1);
v_tail_1342_ = lean_ctor_get(v_x_1339_, 2);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_x_1339_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1344_ = v_x_1339_;
v_isShared_1345_ = v_isSharedCheck_1365_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_tail_1342_);
lean_inc(v_value_1341_);
lean_inc(v_key_1340_);
lean_dec(v_x_1339_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1365_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v_fold_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1346_ = lean_array_get_size(v_x_1338_);
v___x_1347_ = lean_string_hash(v_key_1340_);
v___x_1348_ = 32ULL;
v___x_1349_ = lean_uint64_shift_right(v___x_1347_, v___x_1348_);
v_fold_1350_ = lean_uint64_xor(v___x_1347_, v___x_1349_);
v___x_1351_ = 16ULL;
v___x_1352_ = lean_uint64_shift_right(v_fold_1350_, v___x_1351_);
v___x_1353_ = lean_uint64_xor(v_fold_1350_, v___x_1352_);
v___x_1354_ = lean_uint64_to_usize(v___x_1353_);
v___x_1355_ = lean_usize_of_nat(v___x_1346_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_sub(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_usize_land(v___x_1354_, v___x_1357_);
v___x_1359_ = lean_array_uget_borrowed(v_x_1338_, v___x_1358_);
lean_inc(v___x_1359_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 2, v___x_1359_);
v___x_1361_ = v___x_1344_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_key_1340_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_value_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_array_uset(v_x_1338_, v___x_1358_, v___x_1361_);
v_x_1338_ = v___x_1362_;
v_x_1339_ = v_tail_1342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1366_, lean_object* v_source_1367_, lean_object* v_target_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_source_1367_);
v___x_1370_ = lean_nat_dec_lt(v_i_1366_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v_source_1367_);
lean_dec(v_i_1366_);
return v_target_1368_;
}
else
{
lean_object* v_es_1371_; lean_object* v___x_1372_; lean_object* v_source_1373_; lean_object* v_target_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_es_1371_ = lean_array_fget(v_source_1367_, v_i_1366_);
v___x_1372_ = lean_box(0);
v_source_1373_ = lean_array_fset(v_source_1367_, v_i_1366_, v___x_1372_);
v_target_1374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1368_, v_es_1371_);
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_i_1366_, v___x_1375_);
lean_dec(v_i_1366_);
v_i_1366_ = v___x_1376_;
v_source_1367_ = v_source_1373_;
v_target_1368_ = v_target_1374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_nbuckets_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1379_ = lean_array_get_size(v_data_1378_);
v___x_1380_ = lean_unsigned_to_nat(2u);
v_nbuckets_1381_ = lean_nat_mul(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_mk_array(v_nbuckets_1381_, v___x_1383_);
v___x_1385_ = lean_array_propagate_mark(v_data_1378_, v___x_1384_);
v___x_1386_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1382_, v_data_1378_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1387_, lean_object* v_a_1388_, lean_object* v_b_1389_){
_start:
{
lean_object* v_size_1390_; lean_object* v_buckets_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1434_; 
v_size_1390_ = lean_ctor_get(v_m_1387_, 0);
v_buckets_1391_ = lean_ctor_get(v_m_1387_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_m_1387_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1393_ = v_m_1387_;
v_isShared_1394_ = v_isSharedCheck_1434_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_buckets_1391_);
lean_inc(v_size_1390_);
lean_dec(v_m_1387_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1434_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; uint64_t v___x_1396_; uint64_t v___x_1397_; uint64_t v___x_1398_; uint64_t v_fold_1399_; uint64_t v___x_1400_; uint64_t v___x_1401_; uint64_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; lean_object* v_bkt_1408_; uint8_t v___x_1409_; 
v___x_1395_ = lean_array_get_size(v_buckets_1391_);
v___x_1396_ = lean_string_hash(v_a_1388_);
v___x_1397_ = 32ULL;
v___x_1398_ = lean_uint64_shift_right(v___x_1396_, v___x_1397_);
v_fold_1399_ = lean_uint64_xor(v___x_1396_, v___x_1398_);
v___x_1400_ = 16ULL;
v___x_1401_ = lean_uint64_shift_right(v_fold_1399_, v___x_1400_);
v___x_1402_ = lean_uint64_xor(v_fold_1399_, v___x_1401_);
v___x_1403_ = lean_uint64_to_usize(v___x_1402_);
v___x_1404_ = lean_usize_of_nat(v___x_1395_);
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_sub(v___x_1404_, v___x_1405_);
v___x_1407_ = lean_usize_land(v___x_1403_, v___x_1406_);
v_bkt_1408_ = lean_array_uget_borrowed(v_buckets_1391_, v___x_1407_);
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1388_, v_bkt_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v_size_x27_1411_; lean_object* v___x_1412_; lean_object* v_buckets_x27_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
v_size_x27_1411_ = lean_nat_add(v_size_1390_, v___x_1410_);
lean_dec(v_size_1390_);
lean_inc(v_bkt_1408_);
v___x_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1412_, 0, v_a_1388_);
lean_ctor_set(v___x_1412_, 1, v_b_1389_);
lean_ctor_set(v___x_1412_, 2, v_bkt_1408_);
v_buckets_x27_1413_ = lean_array_uset(v_buckets_1391_, v___x_1407_, v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(4u);
v___x_1415_ = lean_nat_mul(v_size_x27_1411_, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(3u);
v___x_1417_ = lean_nat_div(v___x_1415_, v___x_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_array_get_size(v_buckets_x27_1413_);
v___x_1419_ = lean_nat_dec_le(v___x_1417_, v___x_1418_);
lean_dec(v___x_1417_);
if (v___x_1419_ == 0)
{
lean_object* v_val_1420_; lean_object* v___x_1422_; 
v_val_1420_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1413_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v_val_1420_);
lean_ctor_set(v___x_1393_, 0, v_size_x27_1411_);
v___x_1422_ = v___x_1393_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_size_x27_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_val_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
lean_object* v___x_1425_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v_buckets_x27_1413_);
lean_ctor_set(v___x_1393_, 0, v_size_x27_1411_);
v___x_1425_ = v___x_1393_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_size_x27_1411_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_buckets_x27_1413_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v_buckets_x27_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_inc(v_bkt_1408_);
v___x_1427_ = lean_box(0);
v_buckets_x27_1428_ = lean_array_uset(v_buckets_1391_, v___x_1407_, v___x_1427_);
v___x_1429_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1388_, v_b_1389_, v_bkt_1408_);
v___x_1430_ = lean_array_uset(v_buckets_x27_1428_, v___x_1407_, v___x_1429_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1430_);
v___x_1432_ = v___x_1393_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_size_1390_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1435_, lean_object* v_fallback_1436_, lean_object* v_x_1437_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_inc(v_fallback_1436_);
return v_fallback_1436_;
}
else
{
lean_object* v_key_1438_; lean_object* v_value_1439_; lean_object* v_tail_1440_; uint8_t v___x_1441_; 
v_key_1438_ = lean_ctor_get(v_x_1437_, 0);
v_value_1439_ = lean_ctor_get(v_x_1437_, 1);
v_tail_1440_ = lean_ctor_get(v_x_1437_, 2);
v___x_1441_ = lean_string_dec_eq(v_key_1438_, v_a_1435_);
if (v___x_1441_ == 0)
{
v_x_1437_ = v_tail_1440_;
goto _start;
}
else
{
lean_inc(v_value_1439_);
return v_value_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1443_, lean_object* v_fallback_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1443_, v_fallback_1444_, v_x_1445_);
lean_dec(v_x_1445_);
lean_dec(v_fallback_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1447_, lean_object* v_a_1448_, lean_object* v_fallback_1449_){
_start:
{
lean_object* v_buckets_1450_; lean_object* v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; uint64_t v_fold_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; uint64_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_buckets_1450_ = lean_ctor_get(v_m_1447_, 1);
v___x_1451_ = lean_array_get_size(v_buckets_1450_);
v___x_1452_ = lean_string_hash(v_a_1448_);
v___x_1453_ = 32ULL;
v___x_1454_ = lean_uint64_shift_right(v___x_1452_, v___x_1453_);
v_fold_1455_ = lean_uint64_xor(v___x_1452_, v___x_1454_);
v___x_1456_ = 16ULL;
v___x_1457_ = lean_uint64_shift_right(v_fold_1455_, v___x_1456_);
v___x_1458_ = lean_uint64_xor(v_fold_1455_, v___x_1457_);
v___x_1459_ = lean_uint64_to_usize(v___x_1458_);
v___x_1460_ = lean_usize_of_nat(v___x_1451_);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_sub(v___x_1460_, v___x_1461_);
v___x_1463_ = lean_usize_land(v___x_1459_, v___x_1462_);
v___x_1464_ = lean_array_uget_borrowed(v_buckets_1450_, v___x_1463_);
v___x_1465_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1448_, v_fallback_1449_, v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1466_, lean_object* v_a_1467_, lean_object* v_fallback_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1466_, v_a_1467_, v_fallback_1468_);
lean_dec(v_fallback_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_m_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1472_, size_t v_sz_1473_, size_t v_i_1474_, lean_object* v_b_1475_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_usize_dec_lt(v_i_1474_, v_sz_1473_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_b_1475_);
return v___x_1478_;
}
else
{
lean_object* v_a_1479_; lean_object* v_file_1480_; lean_object* v_pos_1481_; lean_object* v_option_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1508_; 
v_a_1479_ = lean_array_uget_borrowed(v_as_1472_, v_i_1474_);
v_file_1480_ = lean_ctor_get(v_a_1479_, 0);
v_pos_1481_ = lean_ctor_get(v_a_1479_, 1);
lean_inc_ref(v_pos_1481_);
v_option_1482_ = lean_ctor_get(v_a_1479_, 2);
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1480_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_file_1480_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1475_, v_file_1480_, v___x_1484_);
lean_dec_ref_known(v___x_1484_, 2);
v_fst_1486_ = lean_ctor_get(v___x_1485_, 0);
v_snd_1487_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1508_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_inc(v_fst_1486_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1508_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_line_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1506_; 
v_line_1491_ = lean_ctor_get(v_pos_1481_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_pos_1481_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_pos_1481_, 1);
lean_dec(v_unused_1507_);
v___x_1493_ = v_pos_1481_;
v_isShared_1494_ = v_isSharedCheck_1506_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_line_1491_);
lean_dec(v_pos_1481_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1506_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
lean_inc(v_option_1482_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_option_1482_);
lean_ctor_set(v___x_1489_, 0, v_line_1491_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_line_1491_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_option_1482_);
v___x_1496_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_array_push(v_snd_1487_, v___x_1496_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1497_);
lean_ctor_set(v___x_1493_, 0, v_fst_1486_);
v___x_1499_ = v___x_1493_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_fst_1486_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; 
lean_inc_ref(v_file_1480_);
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1475_, v_file_1480_, v___x_1499_);
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1474_, v___x_1501_);
v_i_1474_ = v___x_1502_;
v_b_1475_ = v___x_1500_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_){
_start:
{
size_t v_sz_boxed_1514_; size_t v_i_boxed_1515_; lean_object* v_res_1516_; 
v_sz_boxed_1514_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1515_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1509_, v_sz_boxed_1514_, v_i_boxed_1515_, v_b_1512_);
lean_dec_ref(v_as_1509_);
return v_res_1516_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_unsigned_to_nat(16u);
v___x_1519_ = lean_mk_array(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_byFile_1522_; 
v___x_1520_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1521_ = lean_unsigned_to_nat(0u);
v_byFile_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1522_, 0, v___x_1521_);
lean_ctor_set(v_byFile_1522_, 1, v___x_1520_);
return v_byFile_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v_byFile_1526_; size_t v_sz_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v_byFile_1526_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1527_ = lean_array_size(v_records_1523_);
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1523_, v_sz_1527_, v___x_1528_, v_byFile_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___y_1532_; lean_object* v_size_1544_; lean_object* v_buckets_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_size_1544_ = lean_ctor_get(v_a_1530_, 0);
lean_inc(v_size_1544_);
v_buckets_1545_ = lean_ctor_get(v_a_1530_, 1);
lean_inc_ref(v_buckets_1545_);
lean_dec(v_a_1530_);
v___x_1546_ = lean_mk_empty_array_with_capacity(v_size_1544_);
lean_dec(v_size_1544_);
v___x_1547_ = lean_array_get_size(v_buckets_1545_);
v___x_1548_ = lean_nat_dec_lt(v___x_1525_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v_buckets_1545_);
v___y_1532_ = v___x_1546_;
goto v___jp_1531_;
}
else
{
size_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_usize_of_nat(v___x_1547_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1545_, v___x_1528_, v___x_1549_, v___x_1546_);
lean_dec_ref(v_buckets_1545_);
v___y_1532_ = v___x_1550_;
goto v___jp_1531_;
}
v___jp_1531_:
{
lean_object* v___x_1533_; size_t v_sz_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(0);
v_sz_1534_ = lean_array_size(v___y_1532_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1532_, v_sz_1534_, v___x_1528_, v___x_1533_);
lean_dec_ref(v___y_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v___x_1535_, 0);
lean_dec(v_unused_1543_);
v___x_1537_ = v___x_1535_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v___x_1535_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1533_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1533_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
return v___x_1535_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1529_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1529_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1559_);
lean_dec_ref(v_records_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_m_1563_, lean_object* v_a_1564_, lean_object* v_fallback_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1563_, v_a_1564_, v_fallback_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_a_1569_, lean_object* v_fallback_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1567_, v_m_1568_, v_a_1569_, v_fallback_1570_);
lean_dec(v_fallback_1570_);
lean_dec_ref(v_a_1569_);
lean_dec_ref(v_m_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_a_1574_, lean_object* v_b_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1573_, v_a_1574_, v_b_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, lean_object* v_a_1579_, lean_object* v_fallback_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1578_, v_a_1579_, v_fallback_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1582_, lean_object* v_m_1583_, lean_object* v_a_1584_, lean_object* v_fallback_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1582_, v_m_1583_, v_a_1584_, v_fallback_1585_);
lean_dec(v_fallback_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_m_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1587_, lean_object* v_m_1588_, lean_object* v_a_1589_, lean_object* v_b_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1588_, v_a_1589_, v_b_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_inst_1595_, lean_object* v_R_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1592_, v___x_1593_, v___x_1594_, v_a_1597_, v_b_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_inst_1603_, lean_object* v_R_1604_, lean_object* v_a_1605_, lean_object* v_b_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1600_, v___x_1601_, v___x_1602_, v_inst_1603_, v_R_1604_, v_a_1605_, v_b_1606_);
lean_dec_ref(v___x_1601_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_n_1610_, lean_object* v_as_1611_, lean_object* v_lo_1612_, lean_object* v_hi_1613_, lean_object* v_w_1614_, lean_object* v_hlo_1615_, lean_object* v_hhi_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1608_, v___x_1609_, v_n_1610_, v_as_1611_, v_lo_1612_, v_hi_1613_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v_n_1620_, lean_object* v_as_1621_, lean_object* v_lo_1622_, lean_object* v_hi_1623_, lean_object* v_w_1624_, lean_object* v_hlo_1625_, lean_object* v_hhi_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1618_, v___x_1619_, v_n_1620_, v_as_1621_, v_lo_1622_, v_hi_1623_, v_w_1624_, v_hlo_1625_, v_hhi_1626_);
lean_dec(v_hi_1623_);
lean_dec(v_n_1620_);
lean_dec(v___x_1619_);
lean_dec(v___x_1618_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1628_, lean_object* v_as_1629_, lean_object* v_lo_1630_, lean_object* v_hi_1631_, lean_object* v_w_1632_, lean_object* v_hlo_1633_, lean_object* v_hhi_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1628_, v_as_1629_, v_lo_1630_, v_hi_1631_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1636_, lean_object* v_as_1637_, lean_object* v_lo_1638_, lean_object* v_hi_1639_, lean_object* v_w_1640_, lean_object* v_hlo_1641_, lean_object* v_hhi_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1636_, v_as_1637_, v_lo_1638_, v_hi_1639_, v_w_1640_, v_hlo_1641_, v_hhi_1642_);
lean_dec(v_hi_1639_);
lean_dec(v_n_1636_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_fallback_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1645_, v_fallback_1646_, v_x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1649_, lean_object* v_a_1650_, lean_object* v_fallback_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1649_, v_a_1650_, v_fallback_1651_, v_x_1652_);
lean_dec(v_x_1652_);
lean_dec(v_fallback_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1654_, lean_object* v_a_1655_, lean_object* v_x_1656_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1658_, lean_object* v_a_1659_, lean_object* v_x_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1658_, v_a_1659_, v_x_1660_);
lean_dec(v_x_1660_);
lean_dec_ref(v_a_1659_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1663_, lean_object* v_data_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1666_, lean_object* v_a_1667_, lean_object* v_b_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1667_, v_b_1668_, v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1671_, lean_object* v_a_1672_, lean_object* v_fallback_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1672_, v_fallback_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1676_, lean_object* v_a_1677_, lean_object* v_fallback_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1676_, v_a_1677_, v_fallback_1678_, v_x_1679_);
lean_dec(v_x_1679_);
lean_dec(v_fallback_1678_);
lean_dec(v_a_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1681_, lean_object* v_a_1682_, lean_object* v_x_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1685_, v_a_1686_, v_x_1687_);
lean_dec(v_x_1687_);
lean_dec(v_a_1686_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1690_, lean_object* v_data_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1693_, lean_object* v_a_1694_, lean_object* v_b_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1694_, v_b_1695_, v_x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v_n_1700_, lean_object* v_lo_1701_, lean_object* v_hi_1702_, lean_object* v_hhi_1703_, lean_object* v_pivot_1704_, lean_object* v_as_1705_, lean_object* v_i_1706_, lean_object* v_k_1707_, lean_object* v_ilo_1708_, lean_object* v_ik_1709_, lean_object* v_w_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1698_, v___x_1699_, v_hi_1702_, v_pivot_1704_, v_as_1705_, v_i_1706_, v_k_1707_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1712_, lean_object* v___x_1713_, lean_object* v_n_1714_, lean_object* v_lo_1715_, lean_object* v_hi_1716_, lean_object* v_hhi_1717_, lean_object* v_pivot_1718_, lean_object* v_as_1719_, lean_object* v_i_1720_, lean_object* v_k_1721_, lean_object* v_ilo_1722_, lean_object* v_ik_1723_, lean_object* v_w_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1712_, v___x_1713_, v_n_1714_, v_lo_1715_, v_hi_1716_, v_hhi_1717_, v_pivot_1718_, v_as_1719_, v_i_1720_, v_k_1721_, v_ilo_1722_, v_ik_1723_, v_w_1724_);
lean_dec(v_hi_1716_);
lean_dec(v_lo_1715_);
lean_dec(v_n_1714_);
lean_dec(v___x_1713_);
lean_dec(v___x_1712_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1726_, lean_object* v_lo_1727_, lean_object* v_hi_1728_, lean_object* v_hhi_1729_, lean_object* v_pivot_1730_, lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v_k_1733_, lean_object* v_ilo_1734_, lean_object* v_ik_1735_, lean_object* v_w_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1728_, v_pivot_1730_, v_as_1731_, v_i_1732_, v_k_1733_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1738_, lean_object* v_lo_1739_, lean_object* v_hi_1740_, lean_object* v_hhi_1741_, lean_object* v_pivot_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_k_1745_, lean_object* v_ilo_1746_, lean_object* v_ik_1747_, lean_object* v_w_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1738_, v_lo_1739_, v_hi_1740_, v_hhi_1741_, v_pivot_1742_, v_as_1743_, v_i_1744_, v_k_1745_, v_ilo_1746_, v_ik_1747_, v_w_1748_);
lean_dec_ref(v_pivot_1742_);
lean_dec(v_hi_1740_);
lean_dec(v_lo_1739_);
lean_dec(v_n_1738_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1750_, lean_object* v_i_1751_, lean_object* v_source_1752_, lean_object* v_target_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1751_, v_source_1752_, v_target_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1755_, lean_object* v_i_1756_, lean_object* v_source_1757_, lean_object* v_target_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1756_, v_source_1757_, v_target_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1761_, v_x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1765_, v_x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_env_1773_; lean_object* v___x_1774_; lean_object* v_env_1775_; lean_object* v___x_1776_; lean_object* v_toEnvExtension_1777_; lean_object* v_asyncMode_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1771_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1772_ = lean_st_ref_get(v___y_1769_);
v_env_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc_ref(v_env_1773_);
lean_dec(v___x_1772_);
v___x_1774_ = lean_st_ref_get(v___y_1769_);
v_env_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref(v_env_1775_);
lean_dec(v___x_1774_);
v___x_1776_ = l_Lean_declRangeExt;
v_toEnvExtension_1777_ = lean_ctor_get(v___x_1776_, 0);
v_asyncMode_1778_ = lean_ctor_get(v_toEnvExtension_1777_, 2);
v___x_1779_ = 0;
lean_inc(v_declName_1768_);
v___x_1780_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1771_, v___x_1776_, v_env_1773_, v_declName_1768_, v_asyncMode_1778_, v___x_1779_);
if (lean_obj_tag(v___x_1780_) == 0)
{
uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = 1;
v___x_1782_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1771_, v___x_1776_, v_env_1775_, v_declName_1768_, v_asyncMode_1778_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; 
lean_dec_ref(v_env_1775_);
lean_dec(v_declName_1768_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1780_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1785_, v___y_1786_);
lean_dec(v___y_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v_env_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = lean_st_ref_get(v___y_1790_);
v_env_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc_ref(v_env_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Lean_isRecCore(v_env_1793_, v_declName_1789_);
v___x_1795_ = lean_box(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1797_, v___y_1798_);
lean_dec(v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_ranges_1806_; lean_object* v___x_1812_; lean_object* v_env_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; uint8_t v___y_1821_; uint8_t v___x_1825_; 
v___x_1812_ = lean_st_ref_get(v___y_1803_);
v_env_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc_ref_n(v_env_1813_, 2);
lean_dec(v___x_1812_);
lean_inc_n(v_declName_1801_, 2);
v___x_1814_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1801_, v___y_1803_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
v___x_1825_ = l_Lean_isAuxRecursor(v_env_1813_, v_declName_1801_);
if (v___x_1825_ == 0)
{
uint8_t v___x_1826_; 
lean_inc(v_declName_1801_);
v___x_1826_ = l_Lean_isNoConfusion(v_env_1813_, v_declName_1801_);
v___y_1821_ = v___x_1826_;
goto v___jp_1820_;
}
else
{
lean_dec_ref(v_env_1813_);
v___y_1821_ = v___x_1825_;
goto v___jp_1820_;
}
v___jp_1805_:
{
if (lean_obj_tag(v_ranges_1806_) == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = l_Lean_builtinDeclRanges;
v___x_1808_ = lean_st_ref_get(v___x_1807_);
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1808_, v_declName_1801_);
lean_dec(v_declName_1801_);
lean_dec(v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; 
lean_dec(v_declName_1801_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_ranges_1806_);
return v___x_1811_;
}
}
v___jp_1816_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_a_1819_; 
v___x_1817_ = l_Lean_Name_getPrefix(v_declName_1801_);
v___x_1818_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1817_, v___y_1803_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v_ranges_1806_ = v_a_1819_;
goto v___jp_1805_;
}
v___jp_1820_:
{
if (v___y_1821_ == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_unbox(v_a_1815_);
lean_dec(v_a_1815_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v_a_1824_; 
lean_inc(v_declName_1801_);
v___x_1823_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1801_, v___y_1803_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v_ranges_1806_ = v_a_1824_;
goto v___jp_1805_;
}
else
{
goto v___jp_1816_;
}
}
else
{
lean_dec(v_a_1815_);
goto v___jp_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1832_, lean_object* v_site_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
if (lean_obj_tag(v_site_1833_) == 0)
{
lean_object* v_name_1837_; lean_object* v___x_1838_; 
v_name_1837_ = lean_ctor_get(v_site_1833_, 0);
lean_inc(v_name_1837_);
lean_dec_ref_known(v_site_1833_, 1);
v___x_1838_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1837_, v_a_1834_, v_a_1835_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1860_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1860_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1860_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
else
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1859_; 
v_val_1847_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1849_ = v_a_1839_;
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v_a_1839_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_range_1851_; lean_object* v_pos_1852_; lean_object* v___x_1854_; 
v_range_1851_ = lean_ctor_get(v_val_1847_, 0);
lean_inc_ref(v_range_1851_);
lean_dec(v_val_1847_);
v_pos_1852_ = lean_ctor_get(v_range_1851_, 0);
lean_inc_ref(v_pos_1852_);
lean_dec_ref(v_range_1851_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_pos_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_pos_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1854_);
v___x_1856_ = v___x_1841_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1838_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1838_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_n_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1900_; 
v_n_1869_ = lean_ctor_get(v_site_1833_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_site_1833_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1871_ = v_site_1833_;
v_isShared_1872_ = v_isSharedCheck_1900_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_n_1869_);
lean_dec(v_site_1833_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1900_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v_env_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_st_ref_get(v_a_1835_);
v_env_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc_ref(v_env_1874_);
lean_dec(v___x_1873_);
v___x_1875_ = l_Lean_getVersoModuleDoc_x3f(v_env_1874_, v_failMod_1832_);
lean_dec_ref(v_env_1874_);
if (lean_obj_tag(v___x_1875_) == 1)
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1895_; 
v_val_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1895_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1895_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_array_get_size(v_val_1876_);
v___x_1881_ = lean_nat_dec_lt(v_n_1869_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_del_object(v___x_1878_);
lean_dec(v_val_1876_);
lean_dec(v_n_1869_);
v___x_1882_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1882_);
v___x_1884_ = v___x_1871_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
else
{
lean_object* v___x_1886_; lean_object* v_declarationRange_1887_; lean_object* v_pos_1888_; lean_object* v___x_1890_; 
v___x_1886_ = lean_array_fget(v_val_1876_, v_n_1869_);
lean_dec(v_n_1869_);
lean_dec(v_val_1876_);
v_declarationRange_1887_ = lean_ctor_get(v___x_1886_, 2);
lean_inc_ref(v_declarationRange_1887_);
lean_dec(v___x_1886_);
v_pos_1888_ = lean_ctor_get(v_declarationRange_1887_, 0);
lean_inc_ref(v_pos_1888_);
lean_dec_ref(v_declarationRange_1887_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_pos_1888_);
v___x_1890_ = v___x_1878_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_pos_1888_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1890_);
v___x_1892_ = v___x_1871_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
lean_dec(v___x_1875_);
lean_dec(v_n_1869_);
v___x_1896_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1896_);
v___x_1898_ = v___x_1871_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1901_, lean_object* v_site_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1901_, v_site_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_failMod_1901_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1907_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1917_, v___y_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1930_){
_start:
{
if (lean_obj_tag(v_x_1930_) == 0)
{
lean_object* v_name_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_name_1931_ = lean_ctor_get(v_x_1930_, 0);
lean_inc(v_name_1931_);
lean_dec_ref_known(v_x_1930_, 1);
v___x_1932_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1933_ = 1;
v___x_1934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1931_, v___x_1933_);
v___x_1935_ = lean_string_append(v___x_1932_, v___x_1934_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
return v___x_1937_;
}
else
{
lean_object* v_n_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_n_1938_ = lean_ctor_get(v_x_1930_, 0);
lean_inc(v_n_1938_);
lean_dec_ref_known(v_x_1930_, 1);
v___x_1939_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_add(v_n_1938_, v___x_1940_);
lean_dec(v_n_1938_);
v___x_1942_ = l_Nat_reprFast(v___x_1941_);
v___x_1943_ = lean_string_append(v___x_1939_, v___x_1942_);
lean_dec_ref(v___x_1942_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_env_1949_; lean_object* v___x_1950_; lean_object* v_toEnvExtension_1951_; lean_object* v_asyncMode_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v_merged_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v___x_1947_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1948_ = lean_st_ref_get(v___y_1945_);
v_env_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_ref(v_env_1949_);
lean_dec(v___x_1948_);
v___x_1950_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1951_ = lean_ctor_get(v___x_1950_, 0);
v_asyncMode_1952_ = lean_ctor_get(v_toEnvExtension_1951_, 2);
v___x_1953_ = lean_box(0);
v___x_1954_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1947_, v___x_1950_, v_env_1949_, v_asyncMode_1952_, v___x_1953_);
v_merged_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1954_, 1);
lean_dec(v_unused_1964_);
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_merged_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_merged_1955_);
lean_ctor_set(v___x_1957_, 0, v_o_1944_);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_o_1944_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_merged_1955_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1965_, v___y_1966_);
lean_dec(v___y_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1969_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1979_, lean_object* v_opt_1980_){
_start:
{
lean_object* v_name_1981_; lean_object* v_defValue_1982_; lean_object* v_map_1983_; lean_object* v___x_1984_; 
v_name_1981_ = lean_ctor_get(v_opt_1980_, 0);
v_defValue_1982_ = lean_ctor_get(v_opt_1980_, 1);
v_map_1983_ = lean_ctor_get(v_opts_1979_, 0);
v___x_1984_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1983_, v_name_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_unbox(v_defValue_1982_);
return v___x_1985_;
}
else
{
lean_object* v_val_1986_; 
v_val_1986_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v___x_1984_, 1);
if (lean_obj_tag(v_val_1986_) == 1)
{
uint8_t v_v_1987_; 
v_v_1987_ = lean_ctor_get_uint8(v_val_1986_, 0);
lean_dec_ref_known(v_val_1986_, 0);
return v_v_1987_;
}
else
{
uint8_t v___x_1988_; 
lean_dec(v_val_1986_);
v___x_1988_ = lean_unbox(v_defValue_1982_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1989_, lean_object* v_opt_1990_){
_start:
{
uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_res_1991_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1989_, v_opt_1990_);
lean_dec_ref(v_opt_1990_);
lean_dec_ref(v_opts_1989_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1993_, lean_object* v_opt_1994_){
_start:
{
lean_object* v_name_1995_; lean_object* v_defValue_1996_; lean_object* v_map_1997_; lean_object* v___x_1998_; 
v_name_1995_ = lean_ctor_get(v_opt_1994_, 0);
v_defValue_1996_ = lean_ctor_get(v_opt_1994_, 1);
v_map_1997_ = lean_ctor_get(v_opts_1993_, 0);
v___x_1998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1997_, v_name_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_inc(v_defValue_1996_);
return v_defValue_1996_;
}
else
{
lean_object* v_val_1999_; 
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_1999_);
lean_dec_ref_known(v___x_1998_, 1);
if (lean_obj_tag(v_val_1999_) == 3)
{
lean_object* v_v_2000_; 
v_v_2000_ = lean_ctor_get(v_val_1999_, 0);
lean_inc(v_v_2000_);
lean_dec_ref_known(v_val_1999_, 1);
return v_v_2000_;
}
else
{
lean_dec(v_val_1999_);
lean_inc(v_defValue_1996_);
return v_defValue_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_2001_, lean_object* v_opt_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_2001_, v_opt_2002_);
lean_dec_ref(v_opt_2002_);
lean_dec_ref(v_opts_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_options_2008_; lean_object* v___x_2009_; lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_options_2008_ = lean_ctor_get(v_c_2004_, 6);
lean_inc_ref(v_options_2008_);
lean_dec_ref(v_c_2004_);
v___x_2009_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_2008_, v___y_2006_);
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2014_ = l_Lean_linter_doc_deferred;
v___x_2015_ = l_Lean_Linter_getLinterValue(v___x_2014_, v_a_2010_);
lean_dec(v_a_2010_);
v___x_2016_ = lean_box(v___x_2015_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2026_, lean_object* v_docCheckedModules_2027_, uint8_t v___y_2028_, lean_object* v_m_2029_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2026_, v_m_2029_);
if (v___x_2030_ == 0)
{
return v___x_2030_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_NameSet_contains(v_docCheckedModules_2027_, v_m_2029_);
if (v___x_2031_ == 0)
{
return v___y_2028_;
}
else
{
uint8_t v___x_2032_; 
v___x_2032_ = 0;
return v___x_2032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2033_, lean_object* v_docCheckedModules_2034_, lean_object* v___y_2035_, lean_object* v_m_2036_){
_start:
{
uint8_t v___y_7067__boxed_2037_; uint8_t v_res_2038_; lean_object* v_r_2039_; 
v___y_7067__boxed_2037_ = lean_unbox(v___y_2035_);
v_res_2038_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2033_, v_docCheckedModules_2034_, v___y_7067__boxed_2037_, v_m_2036_);
lean_dec(v_m_2036_);
lean_dec(v_docCheckedModules_2034_);
lean_dec(v_pkgRoot_2033_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_2047_, lean_object* v_sp_2048_, lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_a_2057_; uint8_t v_unlocated_2061_; 
v_unlocated_2061_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v_unlocated_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_sp_2048_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_b_2052_);
return v___x_2062_;
}
else
{
lean_object* v_a_2063_; lean_object* v_snd_2064_; lean_object* v_fst_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2187_; 
v_a_2063_ = lean_array_uget_borrowed(v_as_2049_, v_i_2051_);
v_snd_2064_ = lean_ctor_get(v_a_2063_, 1);
lean_inc(v_snd_2064_);
v_fst_2065_ = lean_ctor_get(v_snd_2064_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_snd_2064_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_snd_2064_, 1);
lean_dec(v_unused_2188_);
v___x_2067_ = v_snd_2064_;
v_isShared_2068_ = v_isSharedCheck_2187_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_fst_2065_);
lean_dec(v_snd_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2187_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_fst_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2186_; 
v_fst_2069_ = lean_ctor_get(v_a_2063_, 0);
v_fst_2070_ = lean_ctor_get(v_b_2052_, 0);
v_snd_2071_ = lean_ctor_get(v_b_2052_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_b_2052_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2073_ = v_b_2052_;
v_isShared_2074_ = v_isSharedCheck_2186_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snd_2071_);
lean_inc(v_fst_2070_);
lean_dec(v_b_2052_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2186_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_site_2075_; lean_object* v___x_2076_; 
v_site_2075_ = lean_ctor_get(v_fst_2065_, 0);
lean_inc_ref_n(v_site_2075_, 2);
lean_dec(v_fst_2065_);
v___x_2076_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2069_, v_site_2075_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
if (lean_obj_tag(v_a_2077_) == 0)
{
lean_object* v___x_2078_; lean_object* v_name_2079_; lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v_snd_2071_);
v___x_2078_ = l_Lean_linter_doc_deferred;
v_name_2079_ = lean_ctor_get(v___x_2078_, 0);
v_ref_2080_ = lean_ctor_get(v___y_2053_, 2);
lean_inc(v_fst_2069_);
v___x_2081_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2069_, v___x_2047_);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_2083_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2075_);
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_string_append(v___x_2086_, v___x_2081_);
lean_dec_ref(v___x_2081_);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_2089_ = lean_string_append(v___x_2087_, v___x_2088_);
lean_inc(v_name_2079_);
v___x_2090_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2079_, v___x_2047_);
v___x_2091_ = lean_string_append(v___x_2089_, v___x_2090_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
v___x_2094_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_dec_ref_known(v___x_2094_, 1);
lean_del_object(v___x_2067_);
v___x_2095_ = lean_box(v_unlocated_2061_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2095_);
v___x_2097_ = v___x_2073_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_fst_2070_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v_a_2057_ = v___x_2097_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2112_; 
lean_del_object(v___x_2073_);
lean_dec(v_fst_2070_);
lean_dec(v_sp_2048_);
v_a_2099_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2101_ = v___x_2094_;
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2112_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2103_ = lean_io_error_to_string(v_a_2099_);
v___x_2104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
v___x_2105_ = l_Lean_MessageData_ofFormat(v___x_2104_);
lean_inc(v_ref_2080_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2105_);
lean_ctor_set(v___x_2067_, 0, v_ref_2080_);
v___x_2107_ = v___x_2067_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_ref_2080_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2107_);
v___x_2109_ = v___x_2101_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
else
{
lean_object* v_val_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_site_2075_);
v_val_2113_ = lean_ctor_get(v_a_2077_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2115_ = v_a_2077_;
v_isShared_2116_ = v_isSharedCheck_2177_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_val_2113_);
lean_dec(v_a_2077_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2177_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_ref_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_ref_2117_ = lean_ctor_get(v___y_2053_, 2);
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2069_);
lean_inc(v_sp_2048_);
v___x_2119_ = l_Lean_SearchPath_findWithExt(v_sp_2048_, v___x_2118_, v_fst_2069_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
if (lean_obj_tag(v_a_2120_) == 0)
{
lean_object* v___x_2121_; lean_object* v_name_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_val_2113_);
lean_dec(v_snd_2071_);
v___x_2121_ = l_Lean_linter_doc_deferred;
v_name_2122_ = lean_ctor_get(v___x_2121_, 0);
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_2069_);
v___x_2124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2069_, v___x_2047_);
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
lean_inc(v_name_2122_);
v___x_2128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2122_, v___x_2047_);
v___x_2129_ = lean_string_append(v___x_2127_, v___x_2128_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2131_ = lean_string_append(v___x_2129_, v___x_2130_);
v___x_2132_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_dec_ref_known(v___x_2132_, 1);
lean_del_object(v___x_2115_);
lean_del_object(v___x_2067_);
v___x_2133_ = lean_box(v_unlocated_2061_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2133_);
v___x_2135_ = v___x_2073_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_fst_2070_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v_a_2057_ = v___x_2135_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_2073_);
lean_dec(v_fst_2070_);
lean_dec(v_sp_2048_);
v_a_2137_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2139_ = v___x_2132_;
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_io_error_to_string(v_a_2137_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 3);
lean_ctor_set(v___x_2115_, 0, v___x_2141_);
v___x_2143_ = v___x_2115_;
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
lean_inc(v_ref_2117_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2144_);
lean_ctor_set(v___x_2067_, 0, v_ref_2117_);
v___x_2146_ = v___x_2067_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_ref_2117_);
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
else
{
lean_object* v_val_2153_; lean_object* v___x_2154_; lean_object* v_name_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_del_object(v___x_2115_);
lean_del_object(v___x_2067_);
v_val_2153_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v_a_2120_, 1);
v___x_2154_ = l_Lean_linter_doc_deferred;
v_name_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_name_2155_);
v___x_2156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2156_, 0, v_val_2153_);
lean_ctor_set(v___x_2156_, 1, v_val_2113_);
lean_ctor_set(v___x_2156_, 2, v_name_2155_);
v___x_2157_ = lean_array_push(v_fst_2070_, v___x_2156_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2157_);
v___x_2159_ = v___x_2073_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_snd_2071_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v_a_2057_ = v___x_2159_;
goto v___jp_2056_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_val_2113_);
lean_del_object(v___x_2073_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_dec(v_sp_2048_);
v_a_2161_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2163_ = v___x_2119_;
v_isShared_2164_ = v_isSharedCheck_2176_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2119_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2176_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_io_error_to_string(v_a_2161_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 3);
lean_ctor_set(v___x_2115_, 0, v___x_2165_);
v___x_2167_ = v___x_2115_;
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
lean_inc(v_ref_2117_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2168_);
lean_ctor_set(v___x_2067_, 0, v_ref_2117_);
v___x_2170_ = v___x_2067_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_ref_2117_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2170_);
v___x_2172_ = v___x_2163_;
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
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_site_2075_);
lean_del_object(v___x_2073_);
lean_dec(v_snd_2071_);
lean_dec(v_fst_2070_);
lean_del_object(v___x_2067_);
lean_dec(v_sp_2048_);
v_a_2178_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2076_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2076_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
v___jp_2056_:
{
size_t v___x_2058_; size_t v___x_2059_; 
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2051_, v___x_2058_);
v_i_2051_ = v___x_2059_;
v_b_2052_ = v_a_2057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2189_, lean_object* v_sp_2190_, lean_object* v_as_2191_, lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_7091__boxed_2198_; size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v___x_7091__boxed_2198_ = lean_unbox(v___x_2189_);
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_7091__boxed_2198_, v_sp_2190_, v_as_2191_, v_sz_boxed_2199_, v_i_boxed_2200_, v_b_2194_, v___y_2195_, v___y_2196_);
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
lean_object* v_a_2223_; lean_object* v_snd_2224_; lean_object* v_fst_2225_; lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2320_; 
v_a_2223_ = lean_array_uget_borrowed(v_as_2210_, v_i_2212_);
v_snd_2224_ = lean_ctor_get(v_a_2223_, 1);
lean_inc(v_snd_2224_);
v_fst_2225_ = lean_ctor_get(v_snd_2224_, 0);
lean_inc(v_fst_2225_);
v_fst_2226_ = lean_ctor_get(v_a_2223_, 0);
v_snd_2227_ = lean_ctor_get(v_snd_2224_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_snd_2224_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v_snd_2224_, 0);
lean_dec(v_unused_2321_);
v___x_2229_ = v_snd_2224_;
v_isShared_2230_ = v_isSharedCheck_2320_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snd_2227_);
lean_dec(v_snd_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2320_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_site_2231_; lean_object* v_sourceString_2232_; lean_object* v___x_2233_; lean_object* v___y_2235_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_site_2231_ = lean_ctor_get(v_fst_2225_, 0);
lean_inc_ref(v_site_2231_);
v_sourceString_2232_ = lean_ctor_get(v_fst_2225_, 2);
lean_inc_ref(v_sourceString_2232_);
lean_dec(v_fst_2225_);
v___x_2233_ = lean_box(0);
v___x_2312_ = lean_string_utf8_byte_size(v_sourceString_2232_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_nat_dec_eq(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2316_ = lean_string_append(v___x_2315_, v_sourceString_2232_);
lean_dec_ref(v_sourceString_2232_);
v___x_2317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2318_ = lean_string_append(v___x_2316_, v___x_2317_);
v___y_2235_ = v___x_2318_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2319_; 
lean_dec_ref(v_sourceString_2232_);
v___x_2319_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2235_ = v___x_2319_;
goto v___jp_2234_;
}
v___jp_2234_:
{
lean_object* v_ref_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_ref_2236_ = lean_ctor_get(v___y_2214_, 2);
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2226_);
lean_inc(v_sp_2208_);
v___x_2238_ = l_Lean_SearchPath_findWithExt(v_sp_2208_, v___x_2237_, v_fst_2226_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2240_ = l_Lean_MessageData_toString(v_snd_2227_);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2226_);
v___x_2242_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2226_, v___y_2209_);
v___x_2243_ = lean_string_append(v___x_2241_, v___x_2242_);
lean_dec_ref(v___x_2242_);
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_2245_ = lean_string_append(v___x_2243_, v___x_2244_);
v___x_2246_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2231_);
v___x_2247_ = lean_string_append(v___x_2245_, v___x_2246_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_string_append(v___x_2247_, v___y_2235_);
lean_dec_ref(v___y_2235_);
v___x_2249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2250_ = lean_string_append(v___x_2248_, v___x_2249_);
v___x_2251_ = lean_string_append(v___x_2250_, v___x_2240_);
lean_dec_ref(v___x_2240_);
v___x_2252_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_dec_ref_known(v___x_2252_, 1);
lean_del_object(v___x_2229_);
v_a_2217_ = v___x_2233_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_sp_2208_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2266_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2266_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2257_ = lean_io_error_to_string(v_a_2253_);
v___x_2258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_ofFormat(v___x_2258_);
lean_inc(v_ref_2236_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2259_);
lean_ctor_set(v___x_2229_, 0, v_ref_2236_);
v___x_2261_ = v___x_2229_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_ref_2236_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2261_);
v___x_2263_ = v___x_2255_;
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
lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2297_; 
v_val_2267_ = lean_ctor_get(v_a_2239_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2269_ = v_a_2239_;
v_isShared_2270_ = v_isSharedCheck_2297_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_dec(v_a_2239_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2297_;
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
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_sp_2208_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2296_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2296_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_io_error_to_string(v_a_2281_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set_tag(v___x_2269_, 3);
lean_ctor_set(v___x_2269_, 0, v___x_2285_);
v___x_2287_ = v___x_2269_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = l_Lean_MessageData_ofFormat(v___x_2287_);
lean_inc(v_ref_2236_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2288_);
lean_ctor_set(v___x_2229_, 0, v_ref_2236_);
v___x_2290_ = v___x_2229_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_ref_2236_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2290_);
v___x_2292_ = v___x_2283_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_site_2231_);
lean_dec(v_snd_2227_);
lean_dec(v_sp_2208_);
v_a_2298_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2300_ = v___x_2238_;
v_isShared_2301_ = v_isSharedCheck_2311_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2238_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2311_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2302_ = lean_io_error_to_string(v_a_2298_);
v___x_2303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
v___x_2304_ = l_Lean_MessageData_ofFormat(v___x_2303_);
lean_inc(v_ref_2236_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2304_);
lean_ctor_set(v___x_2229_, 0, v_ref_2236_);
v___x_2306_ = v___x_2229_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_ref_2236_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2306_);
v___x_2308_ = v___x_2300_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2322_, lean_object* v___y_2323_, lean_object* v_as_2324_, lean_object* v_sz_2325_, lean_object* v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v___y_7373__boxed_2330_; size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v___y_7373__boxed_2330_ = lean_unbox(v___y_2323_);
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2325_);
lean_dec(v_sz_2325_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2322_, v___y_7373__boxed_2330_, v_as_2324_, v_sz_boxed_2331_, v_i_boxed_2332_, v_b_2327_, v___y_2328_);
lean_dec_ref(v___y_2328_);
lean_dec_ref(v_as_2324_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2334_, lean_object* v_as_2335_, size_t v_sz_2336_, size_t v_i_2337_, lean_object* v_b_2338_){
_start:
{
lean_object* v_a_2341_; uint8_t v___x_2345_; 
v___x_2345_ = lean_usize_dec_lt(v_i_2337_, v_sz_2336_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_b_2338_);
return v___x_2346_;
}
else
{
lean_object* v_a_2347_; uint8_t v___x_2348_; 
v_a_2347_ = lean_array_uget_borrowed(v_as_2335_, v_i_2337_);
v___x_2348_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2334_, v_a_2347_);
if (v___x_2348_ == 0)
{
v_a_2341_ = v_b_2338_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2349_; 
lean_inc(v_a_2347_);
v___x_2349_ = l_Lean_NameSet_insert(v_b_2338_, v_a_2347_);
v_a_2341_ = v___x_2349_;
goto v___jp_2340_;
}
}
v___jp_2340_:
{
size_t v___x_2342_; size_t v___x_2343_; 
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_add(v_i_2337_, v___x_2342_);
v_i_2337_ = v___x_2343_;
v_b_2338_ = v_a_2341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2350_, lean_object* v_as_2351_, lean_object* v_sz_2352_, lean_object* v_i_2353_, lean_object* v_b_2354_, lean_object* v___y_2355_){
_start:
{
size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2352_);
lean_dec(v_sz_2352_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2350_, v_as_2351_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2354_);
lean_dec_ref(v_as_2351_);
lean_dec(v_pkgRoot_2350_);
return v_res_2358_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = l_Lean_Options_empty;
v___x_2366_ = l_Lean_Core_getMaxHeartbeats(v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = l_Lean_firstFrontendMacroScope;
v___x_2369_ = lean_nat_add(v___x_2368_, v___x_2367_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_unsigned_to_nat(32u);
v___x_2381_ = lean_mk_empty_array_with_capacity(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
_start:
{
size_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = ((size_t)5ULL);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_unsigned_to_nat(32u);
v___x_2386_ = lean_mk_empty_array_with_capacity(v___x_2385_);
v___x_2387_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2388_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
lean_ctor_set(v___x_2388_, 2, v___x_2384_);
lean_ctor_set(v___x_2388_, 3, v___x_2384_);
lean_ctor_set_usize(v___x_2388_, 4, v___x_2383_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
lean_object* v___x_2389_; uint64_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2390_ = 0ULL;
v___x_2391_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set_uint64(v___x_2391_, sizeof(void*)*1, v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2392_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
return v___x_2396_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = l_Lean_NameSet_empty;
v___x_2398_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
lean_ctor_set(v___x_2399_, 2, v___x_2397_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v_unlocated_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2401_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v_unlocated_2402_ = 1;
v___x_2403_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
lean_ctor_set(v___x_2403_, 2, v___x_2400_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*3, v_unlocated_2402_);
return v___x_2403_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2406_ = l_Lean_diagnostics;
v___x_2407_ = l_Lean_Options_empty;
v___x_2408_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2407_, v___x_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2409_, lean_object* v_linterOpts_2410_, lean_object* v_sp_2411_, lean_object* v_env_2412_, lean_object* v_pkgRoot_2413_, lean_object* v_docCheckedModules_2414_){
_start:
{
lean_object* v___y_2417_; lean_object* v_a_2418_; lean_object* v___y_2443_; uint8_t v___y_2444_; lean_object* v_a_2447_; uint8_t v___y_2451_; lean_object* v_a_2452_; lean_object* v___y_2469_; uint8_t v_lintOnly_2472_; uint8_t v_mode_2473_; lean_object* v___f_2474_; lean_object* v___y_2476_; uint8_t v___y_2477_; uint8_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2482_; lean_object* v_fileName_2483_; lean_object* v_fileMap_2484_; lean_object* v_currNamespace_2485_; lean_object* v_openDecls_2486_; lean_object* v_initHeartbeats_2487_; lean_object* v_maxHeartbeats_2488_; lean_object* v_quotContext_2489_; lean_object* v_currMacroScope_2490_; lean_object* v_cancelTk_x3f_2491_; lean_object* v_inheritedTraceOptions_2492_; lean_object* v_currRecDepth_2493_; lean_object* v_ref_2494_; uint8_t v_suppressElabErrors_2495_; lean_object* v___y_2496_; lean_object* v___y_2526_; uint8_t v___y_2527_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2550_; uint8_t v___y_2551_; uint8_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; uint8_t v___y_2559_; uint8_t v___y_2580_; 
v_lintOnly_2472_ = lean_ctor_get_uint8(v_args_2409_, sizeof(void*)*4);
v_mode_2473_ = lean_ctor_get_uint8(v_args_2409_, sizeof(void*)*4 + 1);
v___f_2474_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2472_ == 0)
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = l_Lean_linter_doc_deferred;
v___x_2620_ = l_Lean_Linter_getLinterValue(v___x_2619_, v_linterOpts_2410_);
v___y_2580_ = v___x_2620_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2621_; lean_object* v_name_2622_; uint8_t v___x_2623_; 
v___x_2621_ = l_Lean_linter_doc_deferred;
v_name_2622_ = lean_ctor_get(v___x_2621_, 0);
v___x_2623_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2622_, v_linterOpts_2410_);
v___y_2580_ = v___x_2623_;
goto v___jp_2579_;
}
v___jp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; size_t v_sz_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2419_ = lean_st_ref_get(v___y_2417_);
lean_dec(v___y_2417_);
lean_dec(v___x_2419_);
v___x_2420_ = l_Lean_Environment_header(v_env_2412_);
lean_dec_ref(v_env_2412_);
v___x_2421_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2420_);
v_sz_2422_ = lean_array_size(v___x_2421_);
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2413_, v___x_2421_, v_sz_2422_, v___x_2423_, v_docCheckedModules_2414_);
lean_dec_ref(v___x_2421_);
lean_dec(v_pkgRoot_2413_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2433_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2433_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2418_);
lean_ctor_set(v___x_2429_, 1, v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_a_2418_);
v_a_2434_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2424_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2424_);
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
v___jp_2442_:
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2445_, 0, v___y_2444_);
v___y_2417_ = v___y_2443_;
v_a_2418_ = v___x_2445_;
goto v___jp_2416_;
}
v___jp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_mk_io_user_error(v_a_2447_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
v___jp_2450_:
{
if (lean_obj_tag(v_a_2452_) == 0)
{
lean_object* v_msg_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_msg_2453_ = lean_ctor_get(v_a_2452_, 1);
lean_inc_ref(v_msg_2453_);
lean_dec_ref_known(v_a_2452_, 2);
v___x_2454_ = l_Lean_MessageData_toString(v_msg_2453_);
v___x_2455_ = lean_mk_io_user_error(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
else
{
lean_object* v_id_2457_; lean_object* v___x_2458_; 
v_id_2457_ = lean_ctor_get(v_a_2452_, 0);
lean_inc(v_id_2457_);
lean_dec_ref_known(v_a_2452_, 2);
v___x_2458_ = l_Lean_InternalExceptionId_getName(v_id_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec(v_id_2457_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2461_ = l_Lean_Name_toString(v_a_2459_, v___y_2451_);
v___x_2462_ = lean_string_append(v___x_2460_, v___x_2461_);
lean_dec_ref(v___x_2461_);
v_a_2447_ = v___x_2462_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec_ref_known(v___x_2458_, 1);
v___x_2463_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2464_ = l_Nat_reprFast(v_id_2457_);
v___x_2465_ = lean_string_append(v___x_2463_, v___x_2464_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2467_ = lean_string_append(v___x_2465_, v___x_2466_);
v_a_2447_ = v___x_2467_;
goto v___jp_2446_;
}
}
}
v___jp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___y_2469_);
lean_ctor_set(v___x_2470_, 1, v_docCheckedModules_2414_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
v___jp_2475_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2497_ = l_Lean_maxRecDepth;
v___x_2498_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2479_, v___x_2497_);
lean_inc_ref(v___y_2479_);
v___x_2499_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2499_, 0, v_fileName_2483_);
lean_ctor_set(v___x_2499_, 1, v_fileMap_2484_);
lean_ctor_set(v___x_2499_, 2, v___y_2479_);
lean_ctor_set(v___x_2499_, 3, v___x_2498_);
lean_ctor_set(v___x_2499_, 4, v_currNamespace_2485_);
lean_ctor_set(v___x_2499_, 5, v_openDecls_2486_);
lean_ctor_set(v___x_2499_, 6, v_initHeartbeats_2487_);
lean_ctor_set(v___x_2499_, 7, v_maxHeartbeats_2488_);
lean_ctor_set(v___x_2499_, 8, v_quotContext_2489_);
lean_ctor_set(v___x_2499_, 9, v_currMacroScope_2490_);
lean_ctor_set(v___x_2499_, 10, v_cancelTk_x3f_2491_);
lean_ctor_set(v___x_2499_, 11, v_inheritedTraceOptions_2492_);
v___x_2500_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v_currRecDepth_2493_);
lean_ctor_set(v___x_2500_, 2, v_ref_2494_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*3, v___y_2482_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*3 + 1, v_suppressElabErrors_2495_);
v___x_2501_ = l_Lean_Doc_DeferredCheck_run(v___y_2481_, v___f_2474_, v___x_2500_, v___y_2496_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; uint8_t v___x_2503_; uint8_t v___x_2504_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = 1;
v___x_2504_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2473_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; size_t v_sz_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
lean_dec(v___y_2496_);
v___x_2505_ = lean_box(0);
v_sz_2506_ = lean_array_size(v_a_2502_);
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2411_, v___y_2478_, v_a_2502_, v_sz_2506_, v___x_2507_, v___x_2505_, v___x_2500_);
lean_dec_ref_known(v___x_2500_, 3);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; uint8_t v___x_2510_; 
lean_dec_ref_known(v___x_2508_, 1);
v___x_2509_ = lean_array_get_size(v_a_2502_);
lean_dec(v_a_2502_);
v___x_2510_ = lean_nat_dec_eq(v___x_2509_, v___y_2476_);
lean_dec(v___y_2476_);
if (v___x_2510_ == 0)
{
v___y_2443_ = v___y_2480_;
v___y_2444_ = v___y_2478_;
goto v___jp_2442_;
}
else
{
v___y_2443_ = v___y_2480_;
v___y_2444_ = v___x_2504_;
goto v___jp_2442_;
}
}
else
{
lean_object* v_a_2511_; 
lean_dec(v_a_2502_);
lean_dec(v___y_2480_);
lean_dec(v___y_2476_);
lean_dec(v_docCheckedModules_2414_);
lean_dec(v_pkgRoot_2413_);
lean_dec_ref(v_env_2412_);
v_a_2511_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2508_, 1);
v___y_2451_ = v___y_2478_;
v_a_2452_ = v_a_2511_;
goto v___jp_2450_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; size_t v_sz_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2512_ = lean_mk_empty_array_with_capacity(v___y_2476_);
lean_dec(v___y_2476_);
v___x_2513_ = lean_box(v___y_2477_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v_sz_2515_ = lean_array_size(v_a_2502_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2504_, v_sp_2411_, v_a_2502_, v_sz_2515_, v___x_2516_, v___x_2514_, v___x_2500_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref_known(v___x_2500_, 3);
lean_dec(v_a_2502_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v_fst_2519_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_fst_2519_);
v_snd_2520_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_snd_2520_);
lean_dec(v_a_2518_);
v___x_2521_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2521_, 0, v_fst_2519_);
v___x_2522_ = lean_unbox(v_snd_2520_);
lean_dec(v_snd_2520_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*1, v___x_2522_);
v___y_2417_ = v___y_2480_;
v_a_2418_ = v___x_2521_;
goto v___jp_2416_;
}
else
{
lean_object* v_a_2523_; 
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2414_);
lean_dec(v_pkgRoot_2413_);
lean_dec_ref(v_env_2412_);
v_a_2523_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2517_, 1);
v___y_2451_ = v___y_2478_;
v_a_2452_ = v_a_2523_;
goto v___jp_2450_;
}
}
}
else
{
lean_object* v_a_2524_; 
lean_dec_ref_known(v___x_2500_, 3);
lean_dec(v___y_2496_);
lean_dec(v___y_2480_);
lean_dec(v___y_2476_);
lean_dec(v_docCheckedModules_2414_);
lean_dec(v_pkgRoot_2413_);
lean_dec_ref(v_env_2412_);
lean_dec(v_sp_2411_);
v_a_2524_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2501_, 1);
v___y_2451_ = v___y_2478_;
v_a_2452_ = v_a_2524_;
goto v___jp_2450_;
}
}
v___jp_2525_:
{
lean_object* v_toCold_2535_; lean_object* v_currRecDepth_2536_; lean_object* v_ref_2537_; uint8_t v_suppressElabErrors_2538_; lean_object* v_fileName_2539_; lean_object* v_fileMap_2540_; lean_object* v_currNamespace_2541_; lean_object* v_openDecls_2542_; lean_object* v_initHeartbeats_2543_; lean_object* v_maxHeartbeats_2544_; lean_object* v_quotContext_2545_; lean_object* v_currMacroScope_2546_; lean_object* v_cancelTk_x3f_2547_; lean_object* v_inheritedTraceOptions_2548_; 
v_toCold_2535_ = lean_ctor_get(v___y_2533_, 0);
lean_inc_ref(v_toCold_2535_);
v_currRecDepth_2536_ = lean_ctor_get(v___y_2533_, 1);
lean_inc(v_currRecDepth_2536_);
v_ref_2537_ = lean_ctor_get(v___y_2533_, 2);
lean_inc(v_ref_2537_);
v_suppressElabErrors_2538_ = lean_ctor_get_uint8(v___y_2533_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_2533_);
v_fileName_2539_ = lean_ctor_get(v_toCold_2535_, 0);
lean_inc_ref(v_fileName_2539_);
v_fileMap_2540_ = lean_ctor_get(v_toCold_2535_, 1);
lean_inc_ref(v_fileMap_2540_);
v_currNamespace_2541_ = lean_ctor_get(v_toCold_2535_, 4);
lean_inc(v_currNamespace_2541_);
v_openDecls_2542_ = lean_ctor_get(v_toCold_2535_, 5);
lean_inc(v_openDecls_2542_);
v_initHeartbeats_2543_ = lean_ctor_get(v_toCold_2535_, 6);
lean_inc(v_initHeartbeats_2543_);
v_maxHeartbeats_2544_ = lean_ctor_get(v_toCold_2535_, 7);
lean_inc(v_maxHeartbeats_2544_);
v_quotContext_2545_ = lean_ctor_get(v_toCold_2535_, 8);
lean_inc(v_quotContext_2545_);
v_currMacroScope_2546_ = lean_ctor_get(v_toCold_2535_, 9);
lean_inc(v_currMacroScope_2546_);
v_cancelTk_x3f_2547_ = lean_ctor_get(v_toCold_2535_, 10);
lean_inc(v_cancelTk_x3f_2547_);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_toCold_2535_, 11);
lean_inc_ref(v_inheritedTraceOptions_2548_);
lean_dec_ref(v_toCold_2535_);
v___y_2476_ = v___y_2526_;
v___y_2477_ = v___y_2527_;
v___y_2478_ = v___y_2528_;
v___y_2479_ = v___y_2529_;
v___y_2480_ = v___y_2530_;
v___y_2481_ = v___y_2531_;
v___y_2482_ = v___y_2532_;
v_fileName_2483_ = v_fileName_2539_;
v_fileMap_2484_ = v_fileMap_2540_;
v_currNamespace_2485_ = v_currNamespace_2541_;
v_openDecls_2486_ = v_openDecls_2542_;
v_initHeartbeats_2487_ = v_initHeartbeats_2543_;
v_maxHeartbeats_2488_ = v_maxHeartbeats_2544_;
v_quotContext_2489_ = v_quotContext_2545_;
v_currMacroScope_2490_ = v_currMacroScope_2546_;
v_cancelTk_x3f_2491_ = v_cancelTk_x3f_2547_;
v_inheritedTraceOptions_2492_ = v_inheritedTraceOptions_2548_;
v_currRecDepth_2493_ = v_currRecDepth_2536_;
v_ref_2494_ = v_ref_2537_;
v_suppressElabErrors_2495_ = v_suppressElabErrors_2538_;
v___y_2496_ = v___y_2534_;
goto v___jp_2475_;
}
v___jp_2549_:
{
if (v___y_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v_env_2561_; lean_object* v_nextMacroScope_2562_; lean_object* v_ngen_2563_; lean_object* v_auxDeclNGen_2564_; lean_object* v_traceState_2565_; lean_object* v_messages_2566_; lean_object* v_infoState_2567_; lean_object* v_snapshotTasks_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2577_; 
v___x_2560_ = lean_st_ref_take(v___y_2556_);
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
lean_inc_ref(v___y_2553_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 5, v___y_2553_);
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
lean_ctor_set(v_reuseFailAlloc_2576_, 5, v___y_2553_);
lean_ctor_set(v_reuseFailAlloc_2576_, 6, v_messages_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 7, v_infoState_2567_);
lean_ctor_set(v_reuseFailAlloc_2576_, 8, v_snapshotTasks_2568_);
v___x_2574_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_st_ref_put(v___y_2556_, v___x_2574_);
lean_inc(v___y_2556_);
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2551_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2556_;
v___y_2531_ = v___y_2557_;
v___y_2532_ = v___y_2558_;
v___y_2533_ = v___y_2555_;
v___y_2534_ = v___y_2556_;
goto v___jp_2525_;
}
}
}
else
{
lean_inc(v___y_2556_);
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2551_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2556_;
v___y_2531_ = v___y_2557_;
v___y_2532_ = v___y_2558_;
v___y_2533_ = v___y_2555_;
v___y_2534_ = v___y_2556_;
goto v___jp_2525_;
}
}
v___jp_2579_:
{
if (v___y_2580_ == 0)
{
uint8_t v___x_2581_; uint8_t v___x_2582_; 
lean_dec(v_pkgRoot_2413_);
lean_dec_ref(v_env_2412_);
lean_dec(v_sp_2411_);
v___x_2581_ = 1;
v___x_2582_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2473_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2583_, 0, v___x_2582_);
v___y_2469_ = v___x_2583_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2585_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*1, v___y_2580_);
v___y_2469_ = v___x_2585_;
goto v___jp_2468_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v_env_2617_; uint8_t v___x_2618_; 
v___x_2586_ = lean_box(v___y_2580_);
lean_inc(v_docCheckedModules_2414_);
lean_inc(v_pkgRoot_2413_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2587_, 0, v_pkgRoot_2413_);
lean_closure_set(v___f_2587_, 1, v_docCheckedModules_2414_);
lean_closure_set(v___f_2587_, 2, v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2589_ = l_Lean_instInhabitedFileMap_default;
v___x_2590_ = l_Lean_Options_empty;
v___x_2591_ = lean_unsigned_to_nat(1000u);
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2596_ = l_Lean_firstFrontendMacroScope;
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_box(0);
v___x_2599_ = 0;
v___x_2600_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2601_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9));
v___x_2602_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2603_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2604_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2605_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2606_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2607_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19));
lean_inc_ref(v_env_2412_);
v___x_2608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2608_, 0, v_env_2412_);
lean_ctor_set(v___x_2608_, 1, v___x_2600_);
lean_ctor_set(v___x_2608_, 2, v___x_2601_);
lean_ctor_set(v___x_2608_, 3, v___x_2602_);
lean_ctor_set(v___x_2608_, 4, v___x_2603_);
lean_ctor_set(v___x_2608_, 5, v___x_2604_);
lean_ctor_set(v___x_2608_, 6, v___x_2605_);
lean_ctor_set(v___x_2608_, 7, v___x_2606_);
lean_ctor_set(v___x_2608_, 8, v___x_2607_);
v___x_2609_ = lean_io_get_num_heartbeats();
v___x_2610_ = lean_st_mk_ref(v___x_2608_);
v___x_2611_ = l_Lean_inheritedTraceOptions;
v___x_2612_ = lean_st_ref_get(v___x_2611_);
lean_inc(v___x_2612_);
lean_inc(v___x_2609_);
v___x_2613_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2588_);
lean_ctor_set(v___x_2613_, 1, v___x_2589_);
lean_ctor_set(v___x_2613_, 2, v___x_2590_);
lean_ctor_set(v___x_2613_, 3, v___x_2591_);
lean_ctor_set(v___x_2613_, 4, v___x_2592_);
lean_ctor_set(v___x_2613_, 5, v___x_2593_);
lean_ctor_set(v___x_2613_, 6, v___x_2609_);
lean_ctor_set(v___x_2613_, 7, v___x_2595_);
lean_ctor_set(v___x_2613_, 8, v___x_2592_);
lean_ctor_set(v___x_2613_, 9, v___x_2596_);
lean_ctor_set(v___x_2613_, 10, v___x_2597_);
lean_ctor_set(v___x_2613_, 11, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2594_);
lean_ctor_set(v___x_2614_, 2, v___x_2598_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3, v___x_2599_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3 + 1, v___x_2599_);
v___x_2615_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2616_ = lean_st_ref_get(v___x_2610_);
v_env_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_env_2617_);
lean_dec(v___x_2616_);
v___x_2618_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2617_);
lean_dec_ref(v_env_2617_);
if (v___x_2615_ == 0)
{
if (v___x_2618_ == 0)
{
lean_dec_ref_known(v___x_2614_, 3);
lean_inc(v___x_2610_);
v___y_2476_ = v___x_2594_;
v___y_2477_ = v___x_2599_;
v___y_2478_ = v___y_2580_;
v___y_2479_ = v___x_2590_;
v___y_2480_ = v___x_2610_;
v___y_2481_ = v___f_2587_;
v___y_2482_ = v___x_2615_;
v_fileName_2483_ = v___x_2588_;
v_fileMap_2484_ = v___x_2589_;
v_currNamespace_2485_ = v___x_2592_;
v_openDecls_2486_ = v___x_2593_;
v_initHeartbeats_2487_ = v___x_2609_;
v_maxHeartbeats_2488_ = v___x_2595_;
v_quotContext_2489_ = v___x_2592_;
v_currMacroScope_2490_ = v___x_2596_;
v_cancelTk_x3f_2491_ = v___x_2597_;
v_inheritedTraceOptions_2492_ = v___x_2612_;
v_currRecDepth_2493_ = v___x_2594_;
v_ref_2494_ = v___x_2598_;
v_suppressElabErrors_2495_ = v___x_2599_;
v___y_2496_ = v___x_2610_;
goto v___jp_2475_;
}
else
{
lean_dec(v___x_2612_);
lean_dec(v___x_2609_);
v___y_2550_ = v___x_2594_;
v___y_2551_ = v___y_2580_;
v___y_2552_ = v___x_2599_;
v___y_2553_ = v___x_2604_;
v___y_2554_ = v___x_2590_;
v___y_2555_ = v___x_2614_;
v___y_2556_ = v___x_2610_;
v___y_2557_ = v___f_2587_;
v___y_2558_ = v___x_2615_;
v___y_2559_ = v___x_2615_;
goto v___jp_2549_;
}
}
else
{
lean_dec(v___x_2612_);
lean_dec(v___x_2609_);
v___y_2550_ = v___x_2594_;
v___y_2551_ = v___y_2580_;
v___y_2552_ = v___x_2599_;
v___y_2553_ = v___x_2604_;
v___y_2554_ = v___x_2590_;
v___y_2555_ = v___x_2614_;
v___y_2556_ = v___x_2610_;
v___y_2557_ = v___f_2587_;
v___y_2558_ = v___x_2615_;
v___y_2559_ = v___x_2618_;
goto v___jp_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2624_, lean_object* v_linterOpts_2625_, lean_object* v_sp_2626_, lean_object* v_env_2627_, lean_object* v_pkgRoot_2628_, lean_object* v_docCheckedModules_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2624_, v_linterOpts_2625_, v_sp_2626_, v_env_2627_, v_pkgRoot_2628_, v_docCheckedModules_2629_);
lean_dec_ref(v_linterOpts_2625_);
lean_dec_ref(v_args_2624_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2632_, uint8_t v___y_2633_, lean_object* v_as_2634_, size_t v_sz_2635_, size_t v_i_2636_, lean_object* v_b_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2632_, v___y_2633_, v_as_2634_, v_sz_2635_, v_i_2636_, v_b_2637_, v___y_2638_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2642_, lean_object* v___y_2643_, lean_object* v_as_2644_, lean_object* v_sz_2645_, lean_object* v_i_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v___y_8106__boxed_2651_; size_t v_sz_boxed_2652_; size_t v_i_boxed_2653_; lean_object* v_res_2654_; 
v___y_8106__boxed_2651_ = lean_unbox(v___y_2643_);
v_sz_boxed_2652_ = lean_unbox_usize(v_sz_2645_);
lean_dec(v_sz_2645_);
v_i_boxed_2653_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_res_2654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2642_, v___y_8106__boxed_2651_, v_as_2644_, v_sz_boxed_2652_, v_i_boxed_2653_, v_b_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_as_2644_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2655_, lean_object* v_as_2656_, size_t v_i_2657_, size_t v_stop_2658_, lean_object* v_b_2659_){
_start:
{
lean_object* v___y_2661_; uint8_t v___x_2665_; 
v___x_2665_ = lean_usize_dec_eq(v_i_2657_, v_stop_2658_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v_linter_2667_; uint8_t v___x_2668_; 
v___x_2666_ = lean_array_uget_borrowed(v_as_2656_, v_i_2657_);
v_linter_2667_ = lean_ctor_get(v___x_2666_, 0);
v___x_2668_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2667_, v_linterOpts_2655_);
if (v___x_2668_ == 0)
{
v___y_2661_ = v_b_2659_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2669_; 
lean_inc(v___x_2666_);
v___x_2669_ = lean_array_push(v_b_2659_, v___x_2666_);
v___y_2661_ = v___x_2669_;
goto v___jp_2660_;
}
}
else
{
return v_b_2659_;
}
v___jp_2660_:
{
size_t v___x_2662_; size_t v___x_2663_; 
v___x_2662_ = ((size_t)1ULL);
v___x_2663_ = lean_usize_add(v_i_2657_, v___x_2662_);
v_i_2657_ = v___x_2663_;
v_b_2659_ = v___y_2661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2670_, lean_object* v_as_2671_, lean_object* v_i_2672_, lean_object* v_stop_2673_, lean_object* v_b_2674_){
_start:
{
size_t v_i_boxed_2675_; size_t v_stop_boxed_2676_; lean_object* v_res_2677_; 
v_i_boxed_2675_ = lean_unbox_usize(v_i_2672_);
lean_dec(v_i_2672_);
v_stop_boxed_2676_ = lean_unbox_usize(v_stop_2673_);
lean_dec(v_stop_2673_);
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2670_, v_as_2671_, v_i_boxed_2675_, v_stop_boxed_2676_, v_b_2674_);
lean_dec_ref(v_as_2671_);
lean_dec_ref(v_linterOpts_2670_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2680_, lean_object* v_as_2681_, size_t v_i_2682_, size_t v_stop_2683_, lean_object* v_b_2684_){
_start:
{
lean_object* v___y_2686_; uint8_t v___x_2690_; 
v___x_2690_ = lean_usize_dec_eq(v_i_2682_, v_stop_2683_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2717_; 
v___x_2691_ = lean_array_uget(v_as_2681_, v_i_2682_);
v_fst_2692_ = lean_ctor_get(v___x_2691_, 0);
v_snd_2693_ = lean_ctor_get(v___x_2691_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2695_ = v___x_2691_;
v_isShared_2696_ = v_isSharedCheck_2717_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_snd_2693_);
lean_inc(v_fst_2692_);
lean_dec(v___x_2691_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2717_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___y_2698_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_array_get_size(v_snd_2693_);
v___x_2708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2709_ = lean_nat_dec_lt(v___x_2706_, v___x_2707_);
if (v___x_2709_ == 0)
{
lean_dec(v_snd_2693_);
v___y_2698_ = v___x_2708_;
goto v___jp_2697_;
}
else
{
uint8_t v___x_2710_; 
v___x_2710_ = lean_nat_dec_le(v___x_2707_, v___x_2707_);
if (v___x_2710_ == 0)
{
if (v___x_2709_ == 0)
{
lean_dec(v_snd_2693_);
v___y_2698_ = v___x_2708_;
goto v___jp_2697_;
}
else
{
size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = lean_usize_of_nat(v___x_2707_);
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2680_, v_snd_2693_, v___x_2711_, v___x_2712_, v___x_2708_);
lean_dec(v_snd_2693_);
v___y_2698_ = v___x_2713_;
goto v___jp_2697_;
}
}
else
{
size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = ((size_t)0ULL);
v___x_2715_ = lean_usize_of_nat(v___x_2707_);
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2680_, v_snd_2693_, v___x_2714_, v___x_2715_, v___x_2708_);
lean_dec(v_snd_2693_);
v___y_2698_ = v___x_2716_;
goto v___jp_2697_;
}
}
v___jp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2699_ = lean_array_get_size(v___y_2698_);
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_nat_dec_eq(v___x_2699_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2703_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 1, v___y_2698_);
v___x_2703_ = v___x_2695_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_fst_2692_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___y_2698_);
v___x_2703_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_array_push(v_b_2684_, v___x_2703_);
v___y_2686_ = v___x_2704_;
goto v___jp_2685_;
}
}
else
{
lean_dec_ref(v___y_2698_);
lean_del_object(v___x_2695_);
lean_dec(v_fst_2692_);
v___y_2686_ = v_b_2684_;
goto v___jp_2685_;
}
}
}
}
else
{
return v_b_2684_;
}
v___jp_2685_:
{
size_t v___x_2687_; size_t v___x_2688_; 
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2682_, v___x_2687_);
v_i_2682_ = v___x_2688_;
v_b_2684_ = v___y_2686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2718_, lean_object* v_as_2719_, lean_object* v_i_2720_, lean_object* v_stop_2721_, lean_object* v_b_2722_){
_start:
{
size_t v_i_boxed_2723_; size_t v_stop_boxed_2724_; lean_object* v_res_2725_; 
v_i_boxed_2723_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_stop_boxed_2724_ = lean_unbox_usize(v_stop_2721_);
lean_dec(v_stop_2721_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2718_, v_as_2719_, v_i_boxed_2723_, v_stop_boxed_2724_, v_b_2722_);
lean_dec_ref(v_as_2719_);
lean_dec_ref(v_linterOpts_2718_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2726_, lean_object* v_as_2727_, lean_object* v_start_2728_, lean_object* v_stop_2729_){
_start:
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2731_ = lean_nat_dec_lt(v_start_2728_, v_stop_2729_);
if (v___x_2731_ == 0)
{
return v___x_2730_;
}
else
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = lean_array_get_size(v_as_2727_);
v___x_2733_ = lean_nat_dec_le(v_stop_2729_, v___x_2732_);
if (v___x_2733_ == 0)
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_nat_dec_lt(v_start_2728_, v___x_2732_);
if (v___x_2734_ == 0)
{
return v___x_2730_;
}
else
{
size_t v___x_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = lean_usize_of_nat(v_start_2728_);
v___x_2736_ = lean_usize_of_nat(v___x_2732_);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2726_, v_as_2727_, v___x_2735_, v___x_2736_, v___x_2730_);
return v___x_2737_;
}
}
else
{
size_t v___x_2738_; size_t v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_usize_of_nat(v_start_2728_);
v___x_2739_ = lean_usize_of_nat(v_stop_2729_);
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2726_, v_as_2727_, v___x_2738_, v___x_2739_, v___x_2730_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2741_, lean_object* v_as_2742_, lean_object* v_start_2743_, lean_object* v_stop_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2741_, v_as_2742_, v_start_2743_, v_stop_2744_);
lean_dec(v_stop_2744_);
lean_dec(v_start_2743_);
lean_dec_ref(v_as_2742_);
lean_dec_ref(v_linterOpts_2741_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2746_, lean_object* v_init_2747_, lean_object* v_x_2748_){
_start:
{
if (lean_obj_tag(v_x_2748_) == 0)
{
lean_object* v_k_2750_; lean_object* v_v_2751_; lean_object* v_l_2752_; lean_object* v_r_2753_; uint8_t v_anyUnlocated_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2770_; 
v_k_2750_ = lean_ctor_get(v_x_2748_, 1);
lean_inc(v_k_2750_);
v_v_2751_ = lean_ctor_get(v_x_2748_, 2);
lean_inc(v_v_2751_);
v_l_2752_ = lean_ctor_get(v_x_2748_, 3);
lean_inc(v_l_2752_);
v_r_2753_ = lean_ctor_get(v_x_2748_, 4);
lean_inc(v_r_2753_);
lean_dec_ref_known(v_x_2748_, 5);
v_anyUnlocated_2754_ = 1;
lean_inc(v_fst_2746_);
v___x_2755_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2746_, v_init_2747_, v_l_2752_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
v_a_2757_ = lean_ctor_get(v_a_2756_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_a_2756_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2759_ = v_a_2756_;
v_isShared_2760_ = v_isSharedCheck_2770_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v_a_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2770_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = l_Lean_Name_toString(v_k_2750_, v_anyUnlocated_2754_);
lean_inc(v_fst_2746_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 0);
lean_ctor_set(v___x_2759_, 0, v_fst_2746_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_fst_2746_);
v___x_2763_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
double v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2764_ = lean_float_of_nat(v_v_2751_);
v___x_2765_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2765_, 0, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2761_);
lean_ctor_set(v___x_2766_, 1, v___x_2763_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
v___x_2767_ = lean_array_push(v_a_2757_, v___x_2766_);
v_init_2747_ = v___x_2767_;
v_x_2748_ = v_r_2753_;
goto _start;
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v_fst_2746_);
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_init_2747_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2773_, lean_object* v_init_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2773_, v_init_2774_, v_x_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2778_, lean_object* v_k_2779_, lean_object* v_fallback_2780_){
_start:
{
if (lean_obj_tag(v_t_2778_) == 0)
{
lean_object* v_k_2781_; lean_object* v_v_2782_; lean_object* v_l_2783_; lean_object* v_r_2784_; uint8_t v___x_2785_; 
v_k_2781_ = lean_ctor_get(v_t_2778_, 1);
v_v_2782_ = lean_ctor_get(v_t_2778_, 2);
v_l_2783_ = lean_ctor_get(v_t_2778_, 3);
v_r_2784_ = lean_ctor_get(v_t_2778_, 4);
v___x_2785_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2779_, v_k_2781_);
switch(v___x_2785_)
{
case 0:
{
v_t_2778_ = v_l_2783_;
goto _start;
}
case 1:
{
lean_inc(v_v_2782_);
return v_v_2782_;
}
default: 
{
v_t_2778_ = v_r_2784_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2780_);
return v_fallback_2780_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2788_, lean_object* v_k_2789_, lean_object* v_fallback_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2788_, v_k_2789_, v_fallback_2790_);
lean_dec(v_fallback_2790_);
lean_dec(v_k_2789_);
lean_dec(v_t_2788_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2792_, size_t v_i_2793_, size_t v_stop_2794_, lean_object* v_b_2795_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_usize_dec_eq(v_i_2793_, v_stop_2794_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v_linter_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; 
v___x_2797_ = lean_array_uget_borrowed(v_as_2792_, v_i_2793_);
v_linter_2798_ = lean_ctor_get(v___x_2797_, 0);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2795_, v_linter_2798_, v___x_2799_);
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_nat_add(v___x_2800_, v___x_2801_);
lean_dec(v___x_2800_);
lean_inc(v_linter_2798_);
v___x_2803_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2798_, v___x_2802_, v_b_2795_);
v___x_2804_ = ((size_t)1ULL);
v___x_2805_ = lean_usize_add(v_i_2793_, v___x_2804_);
v_i_2793_ = v___x_2805_;
v_b_2795_ = v___x_2803_;
goto _start;
}
else
{
return v_b_2795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2807_, lean_object* v_i_2808_, lean_object* v_stop_2809_, lean_object* v_b_2810_){
_start:
{
size_t v_i_boxed_2811_; size_t v_stop_boxed_2812_; lean_object* v_res_2813_; 
v_i_boxed_2811_ = lean_unbox_usize(v_i_2808_);
lean_dec(v_i_2808_);
v_stop_boxed_2812_ = lean_unbox_usize(v_stop_2809_);
lean_dec(v_stop_2809_);
v_res_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2807_, v_i_boxed_2811_, v_stop_boxed_2812_, v_b_2810_);
lean_dec_ref(v_as_2807_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2814_, size_t v_sz_2815_, size_t v_i_2816_, lean_object* v_b_2817_){
_start:
{
lean_object* v_a_2820_; uint8_t v___x_2824_; 
v___x_2824_ = lean_usize_dec_lt(v_i_2816_, v_sz_2815_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_b_2817_);
return v___x_2825_;
}
else
{
lean_object* v_a_2826_; lean_object* v_fst_2827_; lean_object* v_snd_2828_; lean_object* v___y_2830_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_a_2826_ = lean_array_uget_borrowed(v_as_2814_, v_i_2816_);
v_fst_2827_ = lean_ctor_get(v_a_2826_, 0);
v_snd_2828_ = lean_ctor_get(v_a_2826_, 1);
v___x_2852_ = lean_box(1);
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = lean_array_get_size(v_snd_2828_);
v___x_2855_ = lean_nat_dec_lt(v___x_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
v___y_2830_ = v___x_2852_;
goto v___jp_2829_;
}
else
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_nat_dec_le(v___x_2854_, v___x_2854_);
if (v___x_2856_ == 0)
{
if (v___x_2855_ == 0)
{
v___y_2830_ = v___x_2852_;
goto v___jp_2829_;
}
else
{
size_t v___x_2857_; size_t v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = lean_usize_of_nat(v___x_2854_);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2828_, v___x_2857_, v___x_2858_, v___x_2852_);
v___y_2830_ = v___x_2859_;
goto v___jp_2829_;
}
}
else
{
size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = lean_usize_of_nat(v___x_2854_);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2828_, v___x_2860_, v___x_2861_, v___x_2852_);
v___y_2830_ = v___x_2862_;
goto v___jp_2829_;
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; 
lean_inc(v_fst_2827_);
v___x_2831_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2827_, v_b_2817_, v___y_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v_a_2833_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v_a_2833_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_a_2833_);
lean_dec(v_a_2832_);
v_a_2820_ = v_a_2833_;
goto v___jp_2819_;
}
else
{
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2843_; 
v_a_2834_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2836_ = v___x_2831_;
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2831_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_a_2834_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v_a_2834_, 1);
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
else
{
lean_object* v_a_2842_; 
lean_del_object(v___x_2836_);
v_a_2842_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v_a_2834_, 1);
v_a_2820_ = v_a_2842_;
goto v___jp_2819_;
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_a_2844_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2831_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2831_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
}
v___jp_2819_:
{
size_t v___x_2821_; size_t v___x_2822_; 
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_add(v_i_2816_, v___x_2821_);
v_i_2816_ = v___x_2822_;
v_b_2817_ = v_a_2820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2863_, lean_object* v_sz_2864_, lean_object* v_i_2865_, lean_object* v_b_2866_, lean_object* v___y_2867_){
_start:
{
size_t v_sz_boxed_2868_; size_t v_i_boxed_2869_; lean_object* v_res_2870_; 
v_sz_boxed_2868_ = lean_unbox_usize(v_sz_2864_);
lean_dec(v_sz_2864_);
v_i_boxed_2869_ = lean_unbox_usize(v_i_2865_);
lean_dec(v_i_2865_);
v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2863_, v_sz_boxed_2868_, v_i_boxed_2869_, v_b_2866_);
lean_dec_ref(v_as_2863_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2874_, lean_object* v_as_2875_, size_t v_sz_2876_, size_t v_i_2877_, lean_object* v_b_2878_){
_start:
{
lean_object* v_a_2881_; uint8_t v_anyUnlocated_2885_; 
v_anyUnlocated_2885_ = lean_usize_dec_lt(v_i_2877_, v_sz_2876_);
if (v_anyUnlocated_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v_fst_2874_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_b_2878_);
return v___x_2886_;
}
else
{
lean_object* v_fst_2887_; lean_object* v_snd_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2925_; 
v_fst_2887_ = lean_ctor_get(v_b_2878_, 0);
v_snd_2888_ = lean_ctor_get(v_b_2878_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_b_2878_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2890_ = v_b_2878_;
v_isShared_2891_ = v_isSharedCheck_2925_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_snd_2888_);
lean_inc(v_fst_2887_);
lean_dec(v_b_2878_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2925_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_a_2892_; lean_object* v_position_x3f_2893_; 
v_a_2892_ = lean_array_uget_borrowed(v_as_2875_, v_i_2877_);
v_position_x3f_2893_ = lean_ctor_get(v_a_2892_, 2);
if (lean_obj_tag(v_position_x3f_2893_) == 0)
{
lean_object* v_linter_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v_snd_2888_);
v_linter_2894_ = lean_ctor_get(v_a_2892_, 0);
v___x_2895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2894_);
v___x_2896_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2894_, v_anyUnlocated_2885_);
v___x_2897_ = lean_string_append(v___x_2895_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2899_ = lean_string_append(v___x_2897_, v___x_2898_);
lean_inc(v_fst_2874_);
v___x_2900_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2874_, v_anyUnlocated_2885_);
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
v___x_2904_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2904_, 1);
v___x_2905_ = lean_box(v_anyUnlocated_2885_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2905_);
v___x_2907_ = v___x_2890_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_fst_2887_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v_a_2881_ = v___x_2907_;
goto v___jp_2880_;
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_del_object(v___x_2890_);
lean_dec(v_fst_2887_);
lean_dec(v_fst_2874_);
v_a_2909_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2904_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2904_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_linter_2917_; lean_object* v_file_2918_; lean_object* v_val_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v_linter_2917_ = lean_ctor_get(v_a_2892_, 0);
v_file_2918_ = lean_ctor_get(v_a_2892_, 3);
v_val_2919_ = lean_ctor_get(v_position_x3f_2893_, 0);
lean_inc(v_linter_2917_);
lean_inc(v_val_2919_);
lean_inc_ref(v_file_2918_);
v___x_2920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2920_, 0, v_file_2918_);
lean_ctor_set(v___x_2920_, 1, v_val_2919_);
lean_ctor_set(v___x_2920_, 2, v_linter_2917_);
v___x_2921_ = lean_array_push(v_fst_2887_, v___x_2920_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2921_);
v___x_2923_ = v___x_2890_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_snd_2888_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
v_a_2881_ = v___x_2923_;
goto v___jp_2880_;
}
}
}
}
v___jp_2880_:
{
size_t v___x_2882_; size_t v___x_2883_; 
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_i_2877_, v___x_2882_);
v_i_2877_ = v___x_2883_;
v_b_2878_ = v_a_2881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2926_, lean_object* v_as_2927_, lean_object* v_sz_2928_, lean_object* v_i_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_){
_start:
{
size_t v_sz_boxed_2932_; size_t v_i_boxed_2933_; lean_object* v_res_2934_; 
v_sz_boxed_2932_ = lean_unbox_usize(v_sz_2928_);
lean_dec(v_sz_2928_);
v_i_boxed_2933_ = lean_unbox_usize(v_i_2929_);
lean_dec(v_i_2929_);
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2926_, v_as_2927_, v_sz_boxed_2932_, v_i_boxed_2933_, v_b_2930_);
lean_dec_ref(v_as_2927_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2935_, size_t v_sz_2936_, size_t v_i_2937_, lean_object* v_b_2938_){
_start:
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_usize_dec_lt(v_i_2937_, v_sz_2936_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_b_2938_);
return v___x_2941_;
}
else
{
lean_object* v_a_2942_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2969_; 
v_a_2942_ = lean_array_uget_borrowed(v_as_2935_, v_i_2937_);
v_fst_2943_ = lean_ctor_get(v_a_2942_, 0);
v_snd_2944_ = lean_ctor_get(v_a_2942_, 1);
v_fst_2945_ = lean_ctor_get(v_b_2938_, 0);
v_snd_2946_ = lean_ctor_get(v_b_2938_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_b_2938_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2948_ = v_b_2938_;
v_isShared_2949_ = v_isSharedCheck_2969_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_inc(v_fst_2945_);
lean_dec(v_b_2938_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2969_;
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
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_snd_2946_);
v___x_2951_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
size_t v_sz_2952_; size_t v___x_2953_; lean_object* v___x_2954_; 
v_sz_2952_ = lean_array_size(v_snd_2944_);
v___x_2953_ = ((size_t)0ULL);
lean_inc(v_fst_2943_);
v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2943_, v_snd_2944_, v_sz_2952_, v___x_2953_, v___x_2951_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2967_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v_fst_2956_ = lean_ctor_get(v_a_2955_, 0);
v_snd_2957_ = lean_ctor_get(v_a_2955_, 1);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_a_2955_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2959_ = v_a_2955_;
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_snd_2957_);
lean_inc(v_fst_2956_);
lean_dec(v_a_2955_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_fst_2956_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_snd_2957_);
v___x_2962_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
size_t v___x_2963_; size_t v___x_2964_; 
v___x_2963_ = ((size_t)1ULL);
v___x_2964_ = lean_usize_add(v_i_2937_, v___x_2963_);
v_i_2937_ = v___x_2964_;
v_b_2938_ = v___x_2962_;
goto _start;
}
}
}
else
{
return v___x_2954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2970_, lean_object* v_sz_2971_, lean_object* v_i_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_){
_start:
{
size_t v_sz_boxed_2975_; size_t v_i_boxed_2976_; lean_object* v_res_2977_; 
v_sz_boxed_2975_ = lean_unbox_usize(v_sz_2971_);
lean_dec(v_sz_2971_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2972_);
lean_dec(v_i_2972_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2970_, v_sz_boxed_2975_, v_i_boxed_2976_, v_b_2973_);
lean_dec_ref(v_as_2970_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_b_2981_){
_start:
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_b_2981_);
return v___x_2984_;
}
else
{
lean_object* v_a_2985_; lean_object* v_message_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_a_2985_ = lean_array_uget_borrowed(v_as_2978_, v_i_2980_);
v_message_2986_ = lean_ctor_get(v_a_2985_, 1);
v___x_2987_ = lean_box(0);
v___x_2988_ = 0;
lean_inc_ref(v_message_2986_);
v___x_2989_ = l_Lean_SerialMessage_toString(v_message_2986_, v___x_2988_);
v___x_2990_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2989_);
if (lean_obj_tag(v___x_2990_) == 0)
{
size_t v___x_2991_; size_t v___x_2992_; 
lean_dec_ref_known(v___x_2990_, 1);
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2980_, v___x_2991_);
v_i_2980_ = v___x_2992_;
v_b_2981_ = v___x_2987_;
goto _start;
}
else
{
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2994_, lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_){
_start:
{
size_t v_sz_boxed_2999_; size_t v_i_boxed_3000_; lean_object* v_res_3001_; 
v_sz_boxed_2999_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_3000_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2994_, v_sz_boxed_2999_, v_i_boxed_3000_, v_b_2997_);
lean_dec_ref(v_as_2994_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3004_, size_t v_sz_3005_, size_t v_i_3006_, lean_object* v_b_3007_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_b_3007_);
return v___x_3010_;
}
else
{
lean_object* v_a_3011_; lean_object* v_fst_3012_; lean_object* v_snd_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3011_ = lean_array_uget_borrowed(v_as_3004_, v_i_3006_);
v_fst_3012_ = lean_ctor_get(v_a_3011_, 0);
v_snd_3013_ = lean_ctor_get(v_a_3011_, 1);
v___x_3014_ = lean_box(0);
v___x_3015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3012_);
v___x_3016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3012_, v___x_3009_);
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3019_ = lean_string_append(v___x_3017_, v___x_3018_);
v___x_3020_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3019_);
if (lean_obj_tag(v___x_3020_) == 0)
{
size_t v_sz_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3020_, 1);
v_sz_3021_ = lean_array_size(v_snd_3013_);
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3013_, v_sz_3021_, v___x_3022_, v___x_3014_);
if (lean_obj_tag(v___x_3023_) == 0)
{
size_t v___x_3024_; size_t v___x_3025_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = ((size_t)1ULL);
v___x_3025_ = lean_usize_add(v_i_3006_, v___x_3024_);
v_i_3006_ = v___x_3025_;
v_b_3007_ = v___x_3014_;
goto _start;
}
else
{
return v___x_3023_;
}
}
else
{
return v___x_3020_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3027_, lean_object* v_sz_3028_, lean_object* v_i_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_){
_start:
{
size_t v_sz_boxed_3032_; size_t v_i_boxed_3033_; lean_object* v_res_3034_; 
v_sz_boxed_3032_ = lean_unbox_usize(v_sz_3028_);
lean_dec(v_sz_3028_);
v_i_boxed_3033_ = lean_unbox_usize(v_i_3029_);
lean_dec(v_i_3029_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3027_, v_sz_boxed_3032_, v_i_boxed_3033_, v_b_3030_);
lean_dec_ref(v_as_3027_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3039_, lean_object* v_linterOpts_3040_, lean_object* v_env_3041_, lean_object* v_mod_3042_){
_start:
{
uint8_t v_lintOnly_3044_; uint8_t v_mode_3045_; lean_object* v___y_3047_; uint8_t v___y_3048_; lean_object* v___y_3116_; lean_object* v___x_3122_; lean_object* v_textGroups_3123_; 
v_lintOnly_3044_ = lean_ctor_get_uint8(v_args_3039_, sizeof(void*)*4);
v_mode_3045_ = lean_ctor_get_uint8(v_args_3039_, sizeof(void*)*4 + 1);
v___x_3122_ = l_Lean_Name_getRoot(v_mod_3042_);
v_textGroups_3123_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3041_, v___x_3122_);
lean_dec(v___x_3122_);
if (v_lintOnly_3044_ == 0)
{
v___y_3116_ = v_textGroups_3123_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_array_get_size(v_textGroups_3123_);
v___x_3126_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3040_, v_textGroups_3123_, v___x_3124_, v___x_3125_);
lean_dec_ref(v_textGroups_3123_);
v___y_3116_ = v___x_3126_;
goto v___jp_3115_;
}
v___jp_3046_:
{
switch(v_mode_3045_)
{
case 0:
{
lean_object* v___x_3049_; size_t v_sz_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_box(0);
v_sz_3050_ = lean_array_size(v___y_3047_);
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3047_, v_sz_3050_, v___x_3051_, v___x_3049_);
lean_dec_ref(v___y_3047_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3060_; 
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3061_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3056_, 0, v___y_3048_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
v_a_3062_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3052_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3052_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
case 1:
{
lean_object* v___x_3070_; size_t v_sz_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3071_ = lean_array_size(v___y_3047_);
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3047_, v_sz_3071_, v___x_3072_, v___x_3070_);
lean_dec_ref(v___y_3047_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3085_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3085_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3085_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v_fst_3078_; lean_object* v_snd_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; lean_object* v___x_3083_; 
v_fst_3078_ = lean_ctor_get(v_a_3074_, 0);
lean_inc(v_fst_3078_);
v_snd_3079_ = lean_ctor_get(v_a_3074_, 1);
lean_inc(v_snd_3079_);
lean_dec(v_a_3074_);
v___x_3080_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3080_, 0, v_fst_3078_);
v___x_3081_ = lean_unbox(v_snd_3079_);
lean_dec(v_snd_3079_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*1, v___x_3081_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3080_);
v___x_3083_ = v___x_3076_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3080_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
v_a_3086_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3073_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3073_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3094_; size_t v_sz_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v_codeQualityEntries_3094_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3095_ = lean_array_size(v___y_3047_);
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3047_, v_sz_3095_, v___x_3096_, v_codeQualityEntries_3094_);
lean_dec_ref(v___y_3047_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3106_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_a_3098_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
v_a_3107_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3097_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3097_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = lean_array_get_size(v___y_3116_);
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_nat_dec_eq(v___x_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
uint8_t v___x_3120_; 
v___x_3120_ = 1;
v___y_3047_ = v___y_3116_;
v___y_3048_ = v___x_3120_;
goto v___jp_3046_;
}
else
{
uint8_t v___x_3121_; 
v___x_3121_ = 0;
v___y_3047_ = v___y_3116_;
v___y_3048_ = v___x_3121_;
goto v___jp_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3127_, lean_object* v_linterOpts_3128_, lean_object* v_env_3129_, lean_object* v_mod_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3127_, v_linterOpts_3128_, v_env_3129_, v_mod_3130_);
lean_dec(v_mod_3130_);
lean_dec_ref(v_env_3129_);
lean_dec_ref(v_linterOpts_3128_);
lean_dec_ref(v_args_3127_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3133_, lean_object* v_t_3134_, lean_object* v_k_3135_, lean_object* v_fallback_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3134_, v_k_3135_, v_fallback_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3138_, lean_object* v_t_3139_, lean_object* v_k_3140_, lean_object* v_fallback_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3138_, v_t_3139_, v_k_3140_, v_fallback_3141_);
lean_dec(v_fallback_3141_);
lean_dec(v_k_3140_);
lean_dec(v_t_3139_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3143_, lean_object* v_____r_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3148_, 0, v___y_3143_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3150_, lean_object* v_____r_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
uint8_t v___y_15643__boxed_3155_; lean_object* v_res_3156_; 
v___y_15643__boxed_3155_ = lean_unbox(v___y_3150_);
v_res_3156_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15643__boxed_3155_, v_____r_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
size_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3165_ = ((size_t)5ULL);
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = lean_unsigned_to_nat(32u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3170_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3166_);
lean_ctor_set(v___x_3170_, 3, v___x_3166_);
lean_ctor_set_usize(v___x_3170_, 4, v___x_3165_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3171_ = lean_box(1);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
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
lean_object* v___x_3179_; lean_object* v_toCold_3180_; lean_object* v_env_3181_; lean_object* v_options_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3179_ = lean_st_ref_get(v___y_3177_);
v_toCold_3180_ = lean_ctor_get(v___y_3176_, 0);
v_env_3181_ = lean_ctor_get(v___x_3179_, 0);
lean_inc_ref(v_env_3181_);
lean_dec(v___x_3179_);
v_options_3182_ = lean_ctor_get(v_toCold_3180_, 2);
v___x_3183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3182_);
v___x_3185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3185_, 0, v_env_3181_);
lean_ctor_set(v___x_3185_, 1, v___x_3183_);
lean_ctor_set(v___x_3185_, 2, v___x_3184_);
lean_ctor_set(v___x_3185_, 3, v_options_3182_);
v___x_3186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v_msgData_3175_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_ref_3197_; lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_ref_3197_ = lean_ctor_get(v___y_3194_, 2);
v___x_3198_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3193_, v___y_3194_, v___y_3195_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_inc(v_ref_3197_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_ref_3197_);
lean_ctor_set(v___x_3203_, 1, v_a_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 1);
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3213_, lean_object* v_msg_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_toCold_3218_; lean_object* v_currRecDepth_3219_; lean_object* v_ref_3220_; uint8_t v_diag_3221_; uint8_t v_suppressElabErrors_3222_; lean_object* v_ref_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_toCold_3218_ = lean_ctor_get(v___y_3215_, 0);
v_currRecDepth_3219_ = lean_ctor_get(v___y_3215_, 1);
v_ref_3220_ = lean_ctor_get(v___y_3215_, 2);
v_diag_3221_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*3);
v_suppressElabErrors_3222_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*3 + 1);
v_ref_3223_ = l_Lean_replaceRef(v_ref_3213_, v_ref_3220_);
lean_inc(v_currRecDepth_3219_);
lean_inc_ref(v_toCold_3218_);
v___x_3224_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3224_, 0, v_toCold_3218_);
lean_ctor_set(v___x_3224_, 1, v_currRecDepth_3219_);
lean_ctor_set(v___x_3224_, 2, v_ref_3223_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*3, v_diag_3221_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*3 + 1, v_suppressElabErrors_3222_);
v___x_3225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3214_, v___x_3224_, v___y_3216_);
lean_dec_ref_known(v___x_3224_, 3);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3226_, lean_object* v_msg_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3226_, v_msg_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v_ref_3226_);
return v_res_3231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3253_, lean_object* v_declHint_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v_env_3259_; uint8_t v___x_3260_; 
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_st_ref_get(v___y_3255_);
v_env_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3258_);
v___x_3260_ = l_Lean_Name_isAnonymous(v_declHint_3254_);
if (v___x_3260_ == 0)
{
uint8_t v_isExporting_3261_; 
v_isExporting_3261_ = lean_ctor_get_uint8(v_env_3259_, sizeof(void*)*8);
if (v_isExporting_3261_ == 0)
{
lean_object* v___x_3262_; 
lean_dec_ref(v_env_3259_);
lean_dec(v_declHint_3254_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_msg_3253_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
lean_inc_ref(v_env_3259_);
v___x_3263_ = l_Lean_Environment_setExporting(v_env_3259_, v___x_3260_);
lean_inc(v_declHint_3254_);
lean_inc_ref(v___x_3263_);
v___x_3264_ = l_Lean_Environment_contains(v___x_3263_, v_declHint_3254_, v_isExporting_3261_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_dec_ref(v___x_3263_);
lean_dec_ref(v_env_3259_);
lean_dec(v_declHint_3254_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_msg_3253_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v_c_3271_; lean_object* v___x_3272_; 
v___x_3266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3268_ = l_Lean_Options_empty;
v___x_3269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3263_);
lean_ctor_set(v___x_3269_, 1, v___x_3266_);
lean_ctor_set(v___x_3269_, 2, v___x_3267_);
lean_ctor_set(v___x_3269_, 3, v___x_3268_);
lean_inc(v_declHint_3254_);
v___x_3270_ = l_Lean_MessageData_ofConstName(v_declHint_3254_, v___x_3260_);
v_c_3271_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3271_, 0, v___x_3269_);
lean_ctor_set(v_c_3271_, 1, v___x_3270_);
v___x_3272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3259_, v_declHint_3254_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v_env_3259_);
lean_dec(v_declHint_3254_);
v___x_3273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v_c_3271_);
v___x_3275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_MessageData_note(v___x_3276_);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_msg_3253_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
else
{
lean_object* v_val_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3314_; 
v_val_3280_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3282_ = v___x_3272_;
v_isShared_3283_ = v_isSharedCheck_3314_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_val_3280_);
lean_dec(v___x_3272_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3314_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_mod_3286_; uint8_t v___x_3287_; 
v___x_3284_ = l_Lean_Environment_header(v_env_3259_);
lean_dec_ref(v_env_3259_);
v___x_3285_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3284_);
v_mod_3286_ = lean_array_get(v___x_3257_, v___x_3285_, v_val_3280_);
lean_dec(v_val_3280_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_isPrivateName(v_declHint_3254_);
lean_dec(v_declHint_3254_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_c_3271_);
v___x_3290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Lean_MessageData_ofName(v_mod_3286_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_MessageData_note(v___x_3295_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_msg_3253_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3297_);
v___x_3299_ = v___x_3282_;
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
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v_c_3271_);
v___x_3303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_MessageData_ofName(v_mod_3286_);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_MessageData_note(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_msg_3253_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3310_);
v___x_3312_ = v___x_3282_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3315_; 
lean_dec_ref(v_env_3259_);
lean_dec(v_declHint_3254_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_msg_3253_);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3316_, lean_object* v_declHint_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3316_, v_declHint_3317_, v___y_3318_);
lean_dec(v___y_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3321_, lean_object* v_declHint_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3336_; 
v___x_3326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3321_, v_declHint_3322_, v___y_3324_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3336_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3336_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3331_ = l_Lean_unknownIdentifierMessageTag;
v___x_3332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v_a_3327_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3332_);
v___x_3334_ = v___x_3329_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3337_, lean_object* v_declHint_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3337_, v_declHint_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3343_, lean_object* v_msg_3344_, lean_object* v_declHint_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; lean_object* v_a_3350_; lean_object* v___x_3351_; 
v___x_3349_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3344_, v_declHint_3345_, v___y_3346_, v___y_3347_);
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3343_, v_a_3350_, v___y_3346_, v___y_3347_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3352_, lean_object* v_msg_3353_, lean_object* v_declHint_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3352_, v_msg_3353_, v_declHint_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v_ref_3352_);
return v_res_3358_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3363_ = l_Lean_stringToMessageData(v___x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3364_, lean_object* v_constName_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3369_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3370_ = 0;
lean_inc(v_constName_3365_);
v___x_3371_ = l_Lean_MessageData_ofConstName(v_constName_3365_, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3369_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3364_, v___x_3374_, v_constName_3365_, v___y_3366_, v___y_3367_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3376_, lean_object* v_constName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3376_, v_constName_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_ref_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_ref_3386_; lean_object* v___x_3387_; 
v_ref_3386_ = lean_ctor_get(v___y_3383_, 2);
v___x_3387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3386_, v_constName_3382_, v___y_3383_, v___y_3384_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; lean_object* v_env_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_st_ref_get(v___y_3395_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref(v_env_3398_);
lean_dec(v___x_3397_);
v___x_3399_ = 0;
lean_inc(v_constName_3393_);
v___x_3400_ = l_Lean_Environment_find_x3f(v_env_3398_, v_constName_3393_, v___x_3399_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3393_, v___y_3394_, v___y_3395_);
return v___x_3401_;
}
else
{
lean_object* v_val_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_constName_3393_);
v_val_3402_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3400_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_val_3402_);
lean_dec(v___x_3400_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 0);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_val_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_box(0);
lean_inc(v_declName_3415_);
v___x_3420_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3446_; 
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v___x_3420_, 0);
lean_dec(v_unused_3447_);
v___x_3422_ = v___x_3420_;
v_isShared_3423_ = v_isSharedCheck_3446_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v___x_3420_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3446_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v_env_3425_; lean_object* v___x_3426_; 
v___x_3424_ = lean_st_ref_get(v___y_3417_);
v_env_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc_ref(v_env_3425_);
lean_dec(v___x_3424_);
v___x_3426_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3425_, v_declName_3415_);
lean_dec(v_declName_3415_);
lean_dec_ref(v_env_3425_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_box(0);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3427_);
v___x_3429_ = v___x_3422_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
else
{
lean_object* v_val_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3445_; 
v_val_3431_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3433_ = v___x_3426_;
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_val_3431_);
lean_dec(v___x_3426_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v_env_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3435_ = lean_st_ref_get(v___y_3417_);
v_env_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc_ref(v_env_3436_);
lean_dec(v___x_3435_);
v___x_3437_ = l_Lean_Environment_allImportedModuleNames(v_env_3436_);
lean_dec_ref(v_env_3436_);
v___x_3438_ = lean_array_get(v___x_3419_, v___x_3437_, v_val_3431_);
lean_dec(v_val_3431_);
lean_dec_ref(v___x_3437_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3438_);
v___x_3440_ = v___x_3433_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3440_);
v___x_3442_ = v___x_3422_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_declName_3415_);
v_a_3448_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3420_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3420_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3462_, lean_object* v_sp_3463_, lean_object* v___x_3464_, lean_object* v_as_3465_, size_t v_sz_3466_, size_t v_i_3467_, lean_object* v_b_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_a_3473_; uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_b_3468_);
return v___x_3478_;
}
else
{
lean_object* v_a_3479_; lean_object* v_fst_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3608_; 
v_a_3479_ = lean_array_uget(v_as_3465_, v_i_3467_);
v_fst_3480_ = lean_ctor_get(v_a_3479_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_a_3479_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v_a_3479_, 1);
lean_dec(v_unused_3609_);
v___x_3482_ = v_a_3479_;
v_isShared_3483_ = v_isSharedCheck_3608_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_fst_3480_);
lean_dec(v_a_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3608_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3607_; 
v_fst_3484_ = lean_ctor_get(v_b_3468_, 0);
v_snd_3485_ = lean_ctor_get(v_b_3468_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_b_3468_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3487_ = v_b_3468_;
v_isShared_3488_ = v_isSharedCheck_3607_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_snd_3485_);
lean_inc(v_fst_3484_);
lean_dec(v_b_3468_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3607_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; 
lean_inc(v_fst_3480_);
v___x_3489_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3480_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_object* v_optName_3491_; lean_object* v_ref_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v_snd_3485_);
v_optName_3491_ = lean_ctor_get(v_fst_3462_, 1);
v_ref_3492_ = lean_ctor_get(v___y_3469_, 2);
v___x_3493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3480_, v___x_3477_);
v___x_3494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3495_ = lean_string_append(v___x_3494_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3497_ = lean_string_append(v___x_3495_, v___x_3496_);
lean_inc(v_optName_3491_);
v___x_3498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3491_, v___x_3477_);
v___x_3499_ = lean_string_append(v___x_3497_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
v___x_3502_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3502_, 1);
lean_del_object(v___x_3482_);
v___x_3503_ = lean_box(v___x_3477_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3503_);
v___x_3505_ = v___x_3487_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
v_a_3473_ = v___x_3505_;
goto v___jp_3472_;
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3520_; 
lean_del_object(v___x_3487_);
lean_dec(v_fst_3484_);
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v_a_3507_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3509_ = v___x_3502_;
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3502_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3520_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3511_ = lean_io_error_to_string(v_a_3507_);
v___x_3512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
v___x_3513_ = l_Lean_MessageData_ofFormat(v___x_3512_);
lean_inc(v_ref_3492_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3513_);
lean_ctor_set(v___x_3482_, 0, v_ref_3492_);
v___x_3515_ = v___x_3482_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_ref_3492_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3515_);
v___x_3517_ = v___x_3509_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
else
{
lean_object* v_val_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3598_; 
v_val_3521_ = lean_ctor_get(v_a_3490_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3523_ = v_a_3490_;
v_isShared_3524_ = v_isSharedCheck_3598_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_val_3521_);
lean_dec(v_a_3490_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3598_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3480_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___y_3528_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3525_, 1);
if (lean_obj_tag(v_a_3526_) == 0)
{
lean_inc(v___x_3464_);
v___y_3528_ = v___x_3464_;
goto v___jp_3527_;
}
else
{
lean_object* v_val_3589_; 
v_val_3589_ = lean_ctor_get(v_a_3526_, 0);
lean_inc(v_val_3589_);
lean_dec_ref_known(v_a_3526_, 1);
v___y_3528_ = v_val_3589_;
goto v___jp_3527_;
}
v___jp_3527_:
{
lean_object* v_ref_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_ref_3529_ = lean_ctor_get(v___y_3469_, 2);
v___x_3530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3528_);
lean_inc(v_sp_3463_);
v___x_3531_ = l_Lean_SearchPath_findWithExt(v_sp_3463_, v___x_3530_, v___y_3528_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
if (lean_obj_tag(v_a_3532_) == 0)
{
lean_object* v_optName_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec(v_val_3521_);
lean_dec(v_snd_3485_);
v_optName_3533_ = lean_ctor_get(v_fst_3462_, 1);
v___x_3534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3535_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3528_, v___x_3477_);
v___x_3536_ = lean_string_append(v___x_3534_, v___x_3535_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3538_ = lean_string_append(v___x_3536_, v___x_3537_);
lean_inc(v_optName_3533_);
v___x_3539_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3533_, v___x_3477_);
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
v___x_3543_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3542_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3543_, 1);
lean_del_object(v___x_3523_);
lean_del_object(v___x_3482_);
v___x_3544_ = lean_box(v___x_3477_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3544_);
v___x_3546_ = v___x_3487_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
v_a_3473_ = v___x_3546_;
goto v___jp_3472_;
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3487_);
lean_dec(v_fst_3484_);
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v_a_3548_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3550_ = v___x_3543_;
v_isShared_3551_ = v_isSharedCheck_3563_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3543_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3563_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = lean_io_error_to_string(v_a_3548_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 3);
lean_ctor_set(v___x_3523_, 0, v___x_3552_);
v___x_3554_ = v___x_3523_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3555_ = l_Lean_MessageData_ofFormat(v___x_3554_);
lean_inc(v_ref_3529_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3555_);
lean_ctor_set(v___x_3482_, 0, v_ref_3529_);
v___x_3557_ = v___x_3482_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_ref_3529_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3557_);
v___x_3559_ = v___x_3550_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
}
else
{
lean_object* v_range_3564_; lean_object* v_val_3565_; lean_object* v_pos_3566_; lean_object* v_optName_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_dec(v___y_3528_);
lean_del_object(v___x_3523_);
lean_del_object(v___x_3482_);
v_range_3564_ = lean_ctor_get(v_val_3521_, 0);
lean_inc_ref(v_range_3564_);
lean_dec(v_val_3521_);
v_val_3565_ = lean_ctor_get(v_a_3532_, 0);
lean_inc(v_val_3565_);
lean_dec_ref_known(v_a_3532_, 1);
v_pos_3566_ = lean_ctor_get(v_range_3564_, 0);
lean_inc_ref(v_pos_3566_);
lean_dec_ref(v_range_3564_);
v_optName_3567_ = lean_ctor_get(v_fst_3462_, 1);
lean_inc(v_optName_3567_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v_val_3565_);
lean_ctor_set(v___x_3568_, 1, v_pos_3566_);
lean_ctor_set(v___x_3568_, 2, v_optName_3567_);
v___x_3569_ = lean_array_push(v_fst_3484_, v___x_3568_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3569_);
v___x_3571_ = v___x_3487_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_snd_3485_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
v_a_3473_ = v___x_3571_;
goto v___jp_3472_;
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___y_3528_);
lean_dec(v_val_3521_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v_a_3573_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3575_ = v___x_3531_;
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3531_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3588_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_io_error_to_string(v_a_3573_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 3);
lean_ctor_set(v___x_3523_, 0, v___x_3577_);
v___x_3579_ = v___x_3523_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3580_ = l_Lean_MessageData_ofFormat(v___x_3579_);
lean_inc(v_ref_3529_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3580_);
lean_ctor_set(v___x_3482_, 0, v_ref_3529_);
v___x_3582_ = v___x_3482_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_ref_3529_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3582_);
v___x_3584_ = v___x_3575_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_del_object(v___x_3523_);
lean_dec(v_val_3521_);
lean_del_object(v___x_3487_);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
lean_del_object(v___x_3482_);
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v_a_3590_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3525_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3525_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_del_object(v___x_3487_);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
lean_del_object(v___x_3482_);
lean_dec(v_fst_3480_);
lean_dec(v___x_3464_);
lean_dec(v_sp_3463_);
lean_dec_ref(v_fst_3462_);
v_a_3599_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3489_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3489_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
v___jp_3472_:
{
size_t v___x_3474_; size_t v___x_3475_; 
v___x_3474_ = ((size_t)1ULL);
v___x_3475_ = lean_usize_add(v_i_3467_, v___x_3474_);
v_i_3467_ = v___x_3475_;
v_b_3468_ = v_a_3473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3610_, lean_object* v_sp_3611_, lean_object* v___x_3612_, lean_object* v_as_3613_, lean_object* v_sz_3614_, lean_object* v_i_3615_, lean_object* v_b_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3614_);
lean_dec(v_sz_3614_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3615_);
lean_dec(v_i_3615_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3610_, v_sp_3611_, v___x_3612_, v_as_3613_, v_sz_boxed_3620_, v_i_boxed_3621_, v_b_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v_as_3613_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
if (lean_obj_tag(v_x_3624_) == 0)
{
return v_x_3623_;
}
else
{
lean_object* v_key_3625_; lean_object* v_value_3626_; lean_object* v_tail_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_key_3625_ = lean_ctor_get(v_x_3624_, 0);
v_value_3626_ = lean_ctor_get(v_x_3624_, 1);
v_tail_3627_ = lean_ctor_get(v_x_3624_, 2);
lean_inc(v_value_3626_);
lean_inc(v_key_3625_);
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v_key_3625_);
lean_ctor_set(v___x_3628_, 1, v_value_3626_);
v___x_3629_ = lean_array_push(v_x_3623_, v___x_3628_);
v_x_3623_ = v___x_3629_;
v_x_3624_ = v_tail_3627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3631_, v_x_3632_);
lean_dec(v_x_3632_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3634_, size_t v_i_3635_, size_t v_stop_3636_, lean_object* v_b_3637_){
_start:
{
uint8_t v___x_3638_; 
v___x_3638_ = lean_usize_dec_eq(v_i_3635_, v_stop_3636_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; lean_object* v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; 
v___x_3639_ = lean_array_uget_borrowed(v_as_3634_, v_i_3635_);
v___x_3640_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3637_, v___x_3639_);
v___x_3641_ = ((size_t)1ULL);
v___x_3642_ = lean_usize_add(v_i_3635_, v___x_3641_);
v_i_3635_ = v___x_3642_;
v_b_3637_ = v___x_3640_;
goto _start;
}
else
{
return v_b_3637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3644_, lean_object* v_i_3645_, lean_object* v_stop_3646_, lean_object* v_b_3647_){
_start:
{
size_t v_i_boxed_3648_; size_t v_stop_boxed_3649_; lean_object* v_res_3650_; 
v_i_boxed_3648_ = lean_unbox_usize(v_i_3645_);
lean_dec(v_i_3645_);
v_stop_boxed_3649_ = lean_unbox_usize(v_stop_3646_);
lean_dec(v_stop_3646_);
v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3644_, v_i_boxed_3648_, v_stop_boxed_3649_, v_b_3647_);
lean_dec_ref(v_as_3644_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3651_, lean_object* v___x_3652_, lean_object* v_as_3653_, size_t v_sz_3654_, size_t v_i_3655_, lean_object* v_b_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
uint8_t v___x_3660_; 
v___x_3660_ = lean_usize_dec_lt(v_i_3655_, v_sz_3654_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; 
lean_dec(v___x_3652_);
lean_dec(v_sp_3651_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_b_3656_);
return v___x_3661_;
}
else
{
lean_object* v_a_3662_; lean_object* v_fst_3663_; lean_object* v_snd_3664_; lean_object* v_fst_3665_; lean_object* v_snd_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3700_; 
v_a_3662_ = lean_array_uget_borrowed(v_as_3653_, v_i_3655_);
v_fst_3663_ = lean_ctor_get(v_a_3662_, 0);
v_snd_3664_ = lean_ctor_get(v_a_3662_, 1);
v_fst_3665_ = lean_ctor_get(v_b_3656_, 0);
v_snd_3666_ = lean_ctor_get(v_b_3656_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_b_3656_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3668_ = v_b_3656_;
v_isShared_3669_ = v_isSharedCheck_3700_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_snd_3666_);
lean_inc(v_fst_3665_);
lean_dec(v_b_3656_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3700_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___y_3671_; lean_object* v_size_3691_; lean_object* v_buckets_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v_size_3691_ = lean_ctor_get(v_snd_3664_, 0);
v_buckets_3692_ = lean_ctor_get(v_snd_3664_, 1);
v___x_3693_ = lean_mk_empty_array_with_capacity(v_size_3691_);
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = lean_array_get_size(v_buckets_3692_);
v___x_3696_ = lean_nat_dec_lt(v___x_3694_, v___x_3695_);
if (v___x_3696_ == 0)
{
v___y_3671_ = v___x_3693_;
goto v___jp_3670_;
}
else
{
size_t v___x_3697_; size_t v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = ((size_t)0ULL);
v___x_3698_ = lean_usize_of_nat(v___x_3695_);
v___x_3699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3692_, v___x_3697_, v___x_3698_, v___x_3693_);
v___y_3671_ = v___x_3699_;
goto v___jp_3670_;
}
v___jp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3669_ == 0)
{
v___x_3673_ = v___x_3668_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_fst_3665_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_snd_3666_);
v___x_3673_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v_sz_3674_ = lean_array_size(v___y_3671_);
v___x_3675_ = ((size_t)0ULL);
lean_inc(v___x_3652_);
lean_inc(v_sp_3651_);
lean_inc(v_fst_3663_);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3663_, v_sp_3651_, v___x_3652_, v___y_3671_, v_sz_3674_, v___x_3675_, v___x_3673_, v___y_3657_, v___y_3658_);
lean_dec_ref(v___y_3671_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v_fst_3678_; lean_object* v_snd_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3689_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v_fst_3678_ = lean_ctor_get(v_a_3677_, 0);
v_snd_3679_ = lean_ctor_get(v_a_3677_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3677_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3681_ = v_a_3677_;
v_isShared_3682_ = v_isSharedCheck_3689_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_snd_3679_);
lean_inc(v_fst_3678_);
lean_dec(v_a_3677_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3689_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_fst_3678_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_snd_3679_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
size_t v___x_3685_; size_t v___x_3686_; 
v___x_3685_ = ((size_t)1ULL);
v___x_3686_ = lean_usize_add(v_i_3655_, v___x_3685_);
v_i_3655_ = v___x_3686_;
v_b_3656_ = v___x_3684_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3652_);
lean_dec(v_sp_3651_);
return v___x_3676_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3701_, lean_object* v___x_3702_, lean_object* v_as_3703_, lean_object* v_sz_3704_, lean_object* v_i_3705_, lean_object* v_b_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
size_t v_sz_boxed_3710_; size_t v_i_boxed_3711_; lean_object* v_res_3712_; 
v_sz_boxed_3710_ = lean_unbox_usize(v_sz_3704_);
lean_dec(v_sz_3704_);
v_i_boxed_3711_ = lean_unbox_usize(v_i_3705_);
lean_dec(v_i_3705_);
v_res_3712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3701_, v___x_3702_, v_as_3703_, v_sz_boxed_3710_, v_i_boxed_3711_, v_b_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v_as_3703_);
return v_res_3712_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3713_, lean_object* v_as_3714_, size_t v_i_3715_, size_t v_stop_3716_){
_start:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_usize_dec_eq(v_i_3715_, v_stop_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v_snd_3719_; lean_object* v_size_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3718_ = lean_array_uget_borrowed(v_as_3714_, v_i_3715_);
v_snd_3719_ = lean_ctor_get(v___x_3718_, 1);
v_size_3720_ = lean_ctor_get(v_snd_3719_, 0);
v___x_3721_ = 1;
v___x_3722_ = lean_unsigned_to_nat(0u);
v___x_3723_ = lean_nat_dec_eq(v_size_3720_, v___x_3722_);
if (v___x_3723_ == 0)
{
return v___x_3721_;
}
else
{
if (v___y_3713_ == 0)
{
size_t v___x_3724_; size_t v___x_3725_; 
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3715_, v___x_3724_);
v_i_3715_ = v___x_3725_;
goto _start;
}
else
{
return v___x_3721_;
}
}
}
else
{
uint8_t v___x_3727_; 
v___x_3727_ = 0;
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3728_, lean_object* v_as_3729_, lean_object* v_i_3730_, lean_object* v_stop_3731_){
_start:
{
uint8_t v___y_16614__boxed_3732_; size_t v_i_boxed_3733_; size_t v_stop_boxed_3734_; uint8_t v_res_3735_; lean_object* v_r_3736_; 
v___y_16614__boxed_3732_ = lean_unbox(v___y_3728_);
v_i_boxed_3733_ = lean_unbox_usize(v_i_3730_);
lean_dec(v_i_3730_);
v_stop_boxed_3734_ = lean_unbox_usize(v_stop_3731_);
lean_dec(v_stop_3731_);
v_res_3735_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16614__boxed_3732_, v_as_3729_, v_i_boxed_3733_, v_stop_boxed_3734_);
lean_dec_ref(v_as_3729_);
v_r_3736_ = lean_box(v_res_3735_);
return v_r_3736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3737_, lean_object* v_v_3738_, lean_object* v_t_3739_){
_start:
{
lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; 
if (lean_obj_tag(v_t_3739_) == 0)
{
lean_object* v_size_3754_; lean_object* v_k_3755_; lean_object* v_v_3756_; lean_object* v_l_3757_; lean_object* v_r_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_4018_; 
v_size_3754_ = lean_ctor_get(v_t_3739_, 0);
v_k_3755_ = lean_ctor_get(v_t_3739_, 1);
v_v_3756_ = lean_ctor_get(v_t_3739_, 2);
v_l_3757_ = lean_ctor_get(v_t_3739_, 3);
v_r_3758_ = lean_ctor_get(v_t_3739_, 4);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_t_3739_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_3760_ = v_t_3739_;
v_isShared_3761_ = v_isSharedCheck_4018_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_r_3758_);
lean_inc(v_l_3757_);
lean_inc(v_v_3756_);
lean_inc(v_k_3755_);
lean_inc(v_size_3754_);
lean_dec(v_t_3739_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_4018_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; uint8_t v___y_3812_; lean_object* v_fst_4012_; lean_object* v_snd_4013_; lean_object* v_fst_4014_; lean_object* v_snd_4015_; uint8_t v___x_4016_; 
v_fst_4012_ = lean_ctor_get(v_k_3737_, 0);
v_snd_4013_ = lean_ctor_get(v_k_3737_, 1);
v_fst_4014_ = lean_ctor_get(v_k_3755_, 0);
v_snd_4015_ = lean_ctor_get(v_k_3755_, 1);
v___x_4016_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4012_, v_fst_4014_);
if (v___x_4016_ == 1)
{
uint8_t v___x_4017_; 
v___x_4017_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4013_, v_snd_4015_);
v___y_3812_ = v___x_4017_;
goto v___jp_3811_;
}
else
{
v___y_3812_ = v___x_4016_;
goto v___jp_3811_;
}
v___jp_3762_:
{
lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3770_ = lean_nat_add(v___y_3766_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec(v___y_3766_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 3, v___y_3767_);
lean_ctor_set(v___x_3760_, 0, v___x_3770_);
v___x_3772_ = v___x_3760_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v___y_3767_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_r_3758_);
v___x_3772_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3773_, 0, v___y_3765_);
lean_ctor_set(v___x_3773_, 1, v___y_3764_);
lean_ctor_set(v___x_3773_, 2, v___y_3763_);
lean_ctor_set(v___x_3773_, 3, v___y_3768_);
lean_ctor_set(v___x_3773_, 4, v___x_3772_);
return v___x_3773_;
}
}
v___jp_3775_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = lean_nat_add(v___y_3781_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec(v___y_3781_);
v___x_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v___y_3779_);
lean_ctor_set(v___x_3789_, 2, v___y_3783_);
lean_ctor_set(v___x_3789_, 3, v___y_3785_);
lean_ctor_set(v___x_3789_, 4, v___y_3777_);
v___x_3790_ = lean_nat_add(v___y_3786_, v___y_3778_);
lean_dec(v___y_3778_);
if (lean_obj_tag(v___y_3784_) == 0)
{
lean_object* v_size_3791_; 
v_size_3791_ = lean_ctor_get(v___y_3784_, 0);
lean_inc(v_size_3791_);
v___y_3763_ = v___y_3776_;
v___y_3764_ = v___y_3780_;
v___y_3765_ = v___y_3782_;
v___y_3766_ = v___x_3790_;
v___y_3767_ = v___y_3784_;
v___y_3768_ = v___x_3789_;
v___y_3769_ = v_size_3791_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_unsigned_to_nat(0u);
v___y_3763_ = v___y_3776_;
v___y_3764_ = v___y_3780_;
v___y_3765_ = v___y_3782_;
v___y_3766_ = v___x_3790_;
v___y_3767_ = v___y_3784_;
v___y_3768_ = v___x_3789_;
v___y_3769_ = v___x_3792_;
goto v___jp_3762_;
}
}
v___jp_3793_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = lean_nat_add(v___y_3800_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec(v___y_3800_);
v___x_3807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v_k_3755_);
lean_ctor_set(v___x_3807_, 2, v_v_3756_);
lean_ctor_set(v___x_3807_, 3, v_l_3757_);
lean_ctor_set(v___x_3807_, 4, v___y_3797_);
v___x_3808_ = lean_nat_add(v___y_3801_, v___y_3795_);
lean_dec(v___y_3795_);
if (lean_obj_tag(v___y_3794_) == 0)
{
lean_object* v_size_3809_; 
v_size_3809_ = lean_ctor_get(v___y_3794_, 0);
lean_inc(v_size_3809_);
v___y_3741_ = v___y_3794_;
v___y_3742_ = v___y_3796_;
v___y_3743_ = v___x_3807_;
v___y_3744_ = v___y_3799_;
v___y_3745_ = v___y_3798_;
v___y_3746_ = v___x_3808_;
v___y_3747_ = v___y_3802_;
v___y_3748_ = v___y_3803_;
v___y_3749_ = v___y_3804_;
v___y_3750_ = v_size_3809_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3810_; 
v___x_3810_ = lean_unsigned_to_nat(0u);
v___y_3741_ = v___y_3794_;
v___y_3742_ = v___y_3796_;
v___y_3743_ = v___x_3807_;
v___y_3744_ = v___y_3799_;
v___y_3745_ = v___y_3798_;
v___y_3746_ = v___x_3808_;
v___y_3747_ = v___y_3802_;
v___y_3748_ = v___y_3803_;
v___y_3749_ = v___y_3804_;
v___y_3750_ = v___x_3810_;
goto v___jp_3740_;
}
}
v___jp_3811_:
{
switch(v___y_3812_)
{
case 0:
{
lean_object* v_impl_3813_; lean_object* v___x_3814_; 
lean_dec(v_size_3754_);
v_impl_3813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3737_, v_v_3738_, v_l_3757_);
v___x_3814_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3758_) == 0)
{
lean_object* v_size_3815_; lean_object* v_size_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_l_3819_; lean_object* v_r_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_size_3815_ = lean_ctor_get(v_r_3758_, 0);
v_size_3816_ = lean_ctor_get(v_impl_3813_, 0);
lean_inc(v_size_3816_);
v_k_3817_ = lean_ctor_get(v_impl_3813_, 1);
lean_inc(v_k_3817_);
v_v_3818_ = lean_ctor_get(v_impl_3813_, 2);
lean_inc(v_v_3818_);
v_l_3819_ = lean_ctor_get(v_impl_3813_, 3);
lean_inc(v_l_3819_);
v_r_3820_ = lean_ctor_get(v_impl_3813_, 4);
lean_inc(v_r_3820_);
v___x_3821_ = lean_unsigned_to_nat(3u);
v___x_3822_ = lean_nat_mul(v___x_3821_, v_size_3815_);
v___x_3823_ = lean_nat_dec_lt(v___x_3822_, v_size_3816_);
lean_dec(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v_r_3820_);
lean_dec(v_l_3819_);
lean_dec(v_v_3818_);
lean_dec(v_k_3817_);
lean_del_object(v___x_3760_);
v___x_3824_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3825_ = lean_nat_add(v___x_3824_, v_size_3815_);
lean_dec(v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
lean_ctor_set(v___x_3826_, 1, v_k_3755_);
lean_ctor_set(v___x_3826_, 2, v_v_3756_);
lean_ctor_set(v___x_3826_, 3, v_impl_3813_);
lean_ctor_set(v___x_3826_, 4, v_r_3758_);
return v___x_3826_;
}
else
{
lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3863_; 
v_isSharedCheck_3863_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; lean_object* v_unused_3867_; lean_object* v_unused_3868_; 
v_unused_3864_ = lean_ctor_get(v_impl_3813_, 4);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_impl_3813_, 2);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_impl_3813_, 1);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3868_);
v___x_3828_ = v_impl_3813_;
v_isShared_3829_ = v_isSharedCheck_3863_;
goto v_resetjp_3827_;
}
else
{
lean_dec(v_impl_3813_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3863_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v_size_3830_; lean_object* v_size_3831_; lean_object* v_k_3832_; lean_object* v_v_3833_; lean_object* v_l_3834_; lean_object* v_r_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_size_3830_ = lean_ctor_get(v_l_3819_, 0);
v_size_3831_ = lean_ctor_get(v_r_3820_, 0);
v_k_3832_ = lean_ctor_get(v_r_3820_, 1);
v_v_3833_ = lean_ctor_get(v_r_3820_, 2);
v_l_3834_ = lean_ctor_get(v_r_3820_, 3);
v_r_3835_ = lean_ctor_get(v_r_3820_, 4);
v___x_3836_ = lean_unsigned_to_nat(2u);
v___x_3837_ = lean_nat_mul(v___x_3836_, v_size_3830_);
v___x_3838_ = lean_nat_dec_lt(v_size_3831_, v___x_3837_);
lean_dec(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_inc(v_r_3835_);
lean_inc(v_l_3834_);
lean_inc(v_v_3833_);
lean_inc(v_k_3832_);
lean_del_object(v___x_3828_);
lean_dec(v_r_3820_);
v___x_3839_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3840_ = lean_nat_add(v___x_3839_, v_size_3815_);
lean_dec(v___x_3839_);
v___x_3841_ = lean_nat_add(v___x_3814_, v_size_3830_);
if (lean_obj_tag(v_l_3834_) == 0)
{
lean_object* v_size_3842_; 
v_size_3842_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3842_);
lean_inc(v_size_3815_);
v___y_3776_ = v_v_3833_;
v___y_3777_ = v_l_3834_;
v___y_3778_ = v_size_3815_;
v___y_3779_ = v_k_3817_;
v___y_3780_ = v_k_3832_;
v___y_3781_ = v___x_3841_;
v___y_3782_ = v___x_3840_;
v___y_3783_ = v_v_3818_;
v___y_3784_ = v_r_3835_;
v___y_3785_ = v_l_3819_;
v___y_3786_ = v___x_3814_;
v___y_3787_ = v_size_3842_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3815_);
v___y_3776_ = v_v_3833_;
v___y_3777_ = v_l_3834_;
v___y_3778_ = v_size_3815_;
v___y_3779_ = v_k_3817_;
v___y_3780_ = v_k_3832_;
v___y_3781_ = v___x_3841_;
v___y_3782_ = v___x_3840_;
v___y_3783_ = v_v_3818_;
v___y_3784_ = v_r_3835_;
v___y_3785_ = v_l_3819_;
v___y_3786_ = v___x_3814_;
v___y_3787_ = v___x_3843_;
goto v___jp_3775_;
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
lean_del_object(v___x_3760_);
v___x_3844_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3845_ = lean_nat_add(v___x_3844_, v_size_3815_);
lean_dec(v___x_3844_);
v___x_3846_ = lean_nat_add(v___x_3814_, v_size_3815_);
v___x_3847_ = lean_nat_add(v___x_3846_, v_size_3831_);
lean_dec(v___x_3846_);
lean_inc_ref(v_r_3758_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 4, v_r_3758_);
lean_ctor_set(v___x_3828_, 3, v_r_3820_);
lean_ctor_set(v___x_3828_, 2, v_v_3756_);
lean_ctor_set(v___x_3828_, 1, v_k_3755_);
lean_ctor_set(v___x_3828_, 0, v___x_3847_);
v___x_3849_ = v___x_3828_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_r_3820_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_r_3758_);
v___x_3849_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_isSharedCheck_3856_ = !lean_is_exclusive(v_r_3758_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; lean_object* v_unused_3858_; lean_object* v_unused_3859_; lean_object* v_unused_3860_; lean_object* v_unused_3861_; 
v_unused_3857_ = lean_ctor_get(v_r_3758_, 4);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_r_3758_, 3);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_r_3758_, 2);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_r_3758_, 1);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_r_3758_, 0);
lean_dec(v_unused_3861_);
v___x_3851_ = v_r_3758_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_r_3758_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 4, v___x_3849_);
lean_ctor_set(v___x_3851_, 3, v_l_3819_);
lean_ctor_set(v___x_3851_, 2, v_v_3818_);
lean_ctor_set(v___x_3851_, 1, v_k_3817_);
lean_ctor_set(v___x_3851_, 0, v___x_3845_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_l_3819_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v___x_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3869_; 
lean_del_object(v___x_3760_);
v_l_3869_ = lean_ctor_get(v_impl_3813_, 3);
lean_inc(v_l_3869_);
if (lean_obj_tag(v_l_3869_) == 0)
{
lean_object* v_r_3870_; lean_object* v_k_3871_; lean_object* v_v_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3881_; 
v_r_3870_ = lean_ctor_get(v_impl_3813_, 4);
v_k_3871_ = lean_ctor_get(v_impl_3813_, 1);
v_v_3872_ = lean_ctor_get(v_impl_3813_, 2);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; lean_object* v_unused_3883_; 
v_unused_3882_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3883_);
v___x_3874_ = v_impl_3813_;
v_isShared_3875_ = v_isSharedCheck_3881_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_r_3870_);
lean_inc(v_v_3872_);
lean_inc(v_k_3871_);
lean_dec(v_impl_3813_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3881_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3870_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 3, v_r_3870_);
lean_ctor_set(v___x_3874_, 2, v_v_3756_);
lean_ctor_set(v___x_3874_, 1, v_k_3755_);
lean_ctor_set(v___x_3874_, 0, v___x_3814_);
v___x_3878_ = v___x_3874_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_r_3870_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v_r_3870_);
v___x_3878_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3876_);
lean_ctor_set(v___x_3879_, 1, v_k_3871_);
lean_ctor_set(v___x_3879_, 2, v_v_3872_);
lean_ctor_set(v___x_3879_, 3, v_l_3869_);
lean_ctor_set(v___x_3879_, 4, v___x_3878_);
return v___x_3879_;
}
}
}
else
{
lean_object* v_r_3884_; 
v_r_3884_ = lean_ctor_get(v_impl_3813_, 4);
lean_inc(v_r_3884_);
if (lean_obj_tag(v_r_3884_) == 0)
{
lean_object* v_k_3885_; lean_object* v_v_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3907_; 
v_k_3885_ = lean_ctor_get(v_impl_3813_, 1);
v_v_3886_ = lean_ctor_get(v_impl_3813_, 2);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; 
v_unused_3908_ = lean_ctor_get(v_impl_3813_, 4);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3910_);
v___x_3888_ = v_impl_3813_;
v_isShared_3889_ = v_isSharedCheck_3907_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_v_3886_);
lean_inc(v_k_3885_);
lean_dec(v_impl_3813_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3907_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v_k_3890_; lean_object* v_v_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3903_; 
v_k_3890_ = lean_ctor_get(v_r_3884_, 1);
v_v_3891_ = lean_ctor_get(v_r_3884_, 2);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_r_3884_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; 
v_unused_3904_ = lean_ctor_get(v_r_3884_, 4);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_r_3884_, 3);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_r_3884_, 0);
lean_dec(v_unused_3906_);
v___x_3893_ = v_r_3884_;
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_v_3891_);
lean_inc(v_k_3890_);
lean_dec(v_r_3884_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = lean_unsigned_to_nat(3u);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 4, v_l_3869_);
lean_ctor_set(v___x_3893_, 3, v_l_3869_);
lean_ctor_set(v___x_3893_, 2, v_v_3886_);
lean_ctor_set(v___x_3893_, 1, v_k_3885_);
lean_ctor_set(v___x_3893_, 0, v___x_3814_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_k_3885_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_v_3886_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_l_3869_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_l_3869_);
v___x_3897_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3899_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 4, v_l_3869_);
lean_ctor_set(v___x_3888_, 2, v_v_3756_);
lean_ctor_set(v___x_3888_, 1, v_k_3755_);
lean_ctor_set(v___x_3888_, 0, v___x_3814_);
v___x_3899_ = v___x_3888_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v_l_3869_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_l_3869_);
v___x_3899_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3895_);
lean_ctor_set(v___x_3900_, 1, v_k_3890_);
lean_ctor_set(v___x_3900_, 2, v_v_3891_);
lean_ctor_set(v___x_3900_, 3, v___x_3897_);
lean_ctor_set(v___x_3900_, 4, v___x_3899_);
return v___x_3900_;
}
}
}
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_unsigned_to_nat(2u);
v___x_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
lean_ctor_set(v___x_3912_, 1, v_k_3755_);
lean_ctor_set(v___x_3912_, 2, v_v_3756_);
lean_ctor_set(v___x_3912_, 3, v_impl_3813_);
lean_ctor_set(v___x_3912_, 4, v_r_3884_);
return v___x_3912_;
}
}
}
}
case 1:
{
lean_object* v___x_3913_; 
lean_del_object(v___x_3760_);
lean_dec(v_v_3756_);
lean_dec(v_k_3755_);
v___x_3913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3913_, 0, v_size_3754_);
lean_ctor_set(v___x_3913_, 1, v_k_3737_);
lean_ctor_set(v___x_3913_, 2, v_v_3738_);
lean_ctor_set(v___x_3913_, 3, v_l_3757_);
lean_ctor_set(v___x_3913_, 4, v_r_3758_);
return v___x_3913_;
}
default: 
{
lean_object* v_impl_3914_; lean_object* v___x_3915_; 
lean_del_object(v___x_3760_);
lean_dec(v_size_3754_);
v_impl_3914_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3737_, v_v_3738_, v_r_3758_);
v___x_3915_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3757_) == 0)
{
lean_object* v_size_3916_; lean_object* v_size_3917_; lean_object* v_k_3918_; lean_object* v_v_3919_; lean_object* v_l_3920_; lean_object* v_r_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_size_3916_ = lean_ctor_get(v_l_3757_, 0);
v_size_3917_ = lean_ctor_get(v_impl_3914_, 0);
lean_inc(v_size_3917_);
v_k_3918_ = lean_ctor_get(v_impl_3914_, 1);
lean_inc(v_k_3918_);
v_v_3919_ = lean_ctor_get(v_impl_3914_, 2);
lean_inc(v_v_3919_);
v_l_3920_ = lean_ctor_get(v_impl_3914_, 3);
lean_inc(v_l_3920_);
v_r_3921_ = lean_ctor_get(v_impl_3914_, 4);
lean_inc(v_r_3921_);
v___x_3922_ = lean_unsigned_to_nat(3u);
v___x_3923_ = lean_nat_mul(v___x_3922_, v_size_3916_);
v___x_3924_ = lean_nat_dec_lt(v___x_3923_, v_size_3917_);
lean_dec(v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec(v_r_3921_);
lean_dec(v_l_3920_);
lean_dec(v_v_3919_);
lean_dec(v_k_3918_);
v___x_3925_ = lean_nat_add(v___x_3915_, v_size_3916_);
v___x_3926_ = lean_nat_add(v___x_3925_, v_size_3917_);
lean_dec(v_size_3917_);
lean_dec(v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v_k_3755_);
lean_ctor_set(v___x_3927_, 2, v_v_3756_);
lean_ctor_set(v___x_3927_, 3, v_l_3757_);
lean_ctor_set(v___x_3927_, 4, v_impl_3914_);
return v___x_3927_;
}
else
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3962_; 
v_isSharedCheck_3962_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; lean_object* v_unused_3966_; lean_object* v_unused_3967_; 
v_unused_3963_ = lean_ctor_get(v_impl_3914_, 4);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_impl_3914_, 2);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_impl_3914_, 1);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_3967_);
v___x_3929_ = v_impl_3914_;
v_isShared_3930_ = v_isSharedCheck_3962_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_impl_3914_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3962_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v_size_3931_; lean_object* v_k_3932_; lean_object* v_v_3933_; lean_object* v_l_3934_; lean_object* v_r_3935_; lean_object* v_size_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_size_3931_ = lean_ctor_get(v_l_3920_, 0);
v_k_3932_ = lean_ctor_get(v_l_3920_, 1);
v_v_3933_ = lean_ctor_get(v_l_3920_, 2);
v_l_3934_ = lean_ctor_get(v_l_3920_, 3);
v_r_3935_ = lean_ctor_get(v_l_3920_, 4);
v_size_3936_ = lean_ctor_get(v_r_3921_, 0);
v___x_3937_ = lean_unsigned_to_nat(2u);
v___x_3938_ = lean_nat_mul(v___x_3937_, v_size_3936_);
v___x_3939_ = lean_nat_dec_lt(v_size_3931_, v___x_3938_);
lean_dec(v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
lean_inc(v_size_3936_);
lean_inc(v_r_3935_);
lean_inc(v_l_3934_);
lean_inc(v_v_3933_);
lean_inc(v_k_3932_);
lean_del_object(v___x_3929_);
lean_dec(v_l_3920_);
v___x_3940_ = lean_nat_add(v___x_3915_, v_size_3916_);
v___x_3941_ = lean_nat_add(v___x_3940_, v_size_3917_);
lean_dec(v_size_3917_);
if (lean_obj_tag(v_l_3934_) == 0)
{
lean_object* v_size_3942_; 
v_size_3942_ = lean_ctor_get(v_l_3934_, 0);
lean_inc(v_size_3942_);
v___y_3794_ = v_r_3935_;
v___y_3795_ = v_size_3936_;
v___y_3796_ = v_k_3932_;
v___y_3797_ = v_l_3934_;
v___y_3798_ = v_k_3918_;
v___y_3799_ = v___x_3941_;
v___y_3800_ = v___x_3940_;
v___y_3801_ = v___x_3915_;
v___y_3802_ = v_v_3933_;
v___y_3803_ = v_v_3919_;
v___y_3804_ = v_r_3921_;
v___y_3805_ = v_size_3942_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3943_; 
v___x_3943_ = lean_unsigned_to_nat(0u);
v___y_3794_ = v_r_3935_;
v___y_3795_ = v_size_3936_;
v___y_3796_ = v_k_3932_;
v___y_3797_ = v_l_3934_;
v___y_3798_ = v_k_3918_;
v___y_3799_ = v___x_3941_;
v___y_3800_ = v___x_3940_;
v___y_3801_ = v___x_3915_;
v___y_3802_ = v_v_3933_;
v___y_3803_ = v_v_3919_;
v___y_3804_ = v_r_3921_;
v___y_3805_ = v___x_3943_;
goto v___jp_3793_;
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3944_ = lean_nat_add(v___x_3915_, v_size_3916_);
v___x_3945_ = lean_nat_add(v___x_3944_, v_size_3917_);
lean_dec(v_size_3917_);
v___x_3946_ = lean_nat_add(v___x_3944_, v_size_3931_);
lean_dec(v___x_3944_);
lean_inc_ref(v_l_3757_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 4, v_l_3920_);
lean_ctor_set(v___x_3929_, 3, v_l_3757_);
lean_ctor_set(v___x_3929_, 2, v_v_3756_);
lean_ctor_set(v___x_3929_, 1, v_k_3755_);
lean_ctor_set(v___x_3929_, 0, v___x_3946_);
v___x_3948_ = v___x_3929_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_l_3757_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v_l_3920_);
v___x_3948_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_isSharedCheck_3955_ = !lean_is_exclusive(v_l_3757_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; 
v_unused_3956_ = lean_ctor_get(v_l_3757_, 4);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_l_3757_, 3);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_l_3757_, 2);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_l_3757_, 1);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_l_3757_, 0);
lean_dec(v_unused_3960_);
v___x_3950_ = v_l_3757_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_dec(v_l_3757_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 4, v_r_3921_);
lean_ctor_set(v___x_3950_, 3, v___x_3948_);
lean_ctor_set(v___x_3950_, 2, v_v_3919_);
lean_ctor_set(v___x_3950_, 1, v_k_3918_);
lean_ctor_set(v___x_3950_, 0, v___x_3945_);
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v_r_3921_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3968_; 
v_l_3968_ = lean_ctor_get(v_impl_3914_, 3);
lean_inc(v_l_3968_);
if (lean_obj_tag(v_l_3968_) == 0)
{
lean_object* v_r_3969_; lean_object* v_k_3970_; lean_object* v_v_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3992_; 
v_r_3969_ = lean_ctor_get(v_impl_3914_, 4);
v_k_3970_ = lean_ctor_get(v_impl_3914_, 1);
v_v_3971_ = lean_ctor_get(v_impl_3914_, 2);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; lean_object* v_unused_3994_; 
v_unused_3993_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_3993_);
v_unused_3994_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_3994_);
v___x_3973_ = v_impl_3914_;
v_isShared_3974_ = v_isSharedCheck_3992_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_r_3969_);
lean_inc(v_v_3971_);
lean_inc(v_k_3970_);
lean_dec(v_impl_3914_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3992_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v_k_3975_; lean_object* v_v_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3988_; 
v_k_3975_ = lean_ctor_get(v_l_3968_, 1);
v_v_3976_ = lean_ctor_get(v_l_3968_, 2);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_l_3968_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; lean_object* v_unused_3990_; lean_object* v_unused_3991_; 
v_unused_3989_ = lean_ctor_get(v_l_3968_, 4);
lean_dec(v_unused_3989_);
v_unused_3990_ = lean_ctor_get(v_l_3968_, 3);
lean_dec(v_unused_3990_);
v_unused_3991_ = lean_ctor_get(v_l_3968_, 0);
lean_dec(v_unused_3991_);
v___x_3978_ = v_l_3968_;
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_v_3976_);
lean_inc(v_k_3975_);
lean_dec(v_l_3968_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3969_, 2);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 4, v_r_3969_);
lean_ctor_set(v___x_3978_, 3, v_r_3969_);
lean_ctor_set(v___x_3978_, 2, v_v_3756_);
lean_ctor_set(v___x_3978_, 1, v_k_3755_);
lean_ctor_set(v___x_3978_, 0, v___x_3915_);
v___x_3982_ = v___x_3978_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3987_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3987_, 3, v_r_3969_);
lean_ctor_set(v_reuseFailAlloc_3987_, 4, v_r_3969_);
v___x_3982_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; 
lean_inc(v_r_3969_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 3, v_r_3969_);
lean_ctor_set(v___x_3973_, 0, v___x_3915_);
v___x_3984_ = v___x_3973_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_k_3970_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_v_3971_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_r_3969_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v_r_3969_);
v___x_3984_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3980_);
lean_ctor_set(v___x_3985_, 1, v_k_3975_);
lean_ctor_set(v___x_3985_, 2, v_v_3976_);
lean_ctor_set(v___x_3985_, 3, v___x_3982_);
lean_ctor_set(v___x_3985_, 4, v___x_3984_);
return v___x_3985_;
}
}
}
}
}
else
{
lean_object* v_r_3995_; 
v_r_3995_ = lean_ctor_get(v_impl_3914_, 4);
lean_inc(v_r_3995_);
if (lean_obj_tag(v_r_3995_) == 0)
{
lean_object* v_k_3996_; lean_object* v_v_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4006_; 
v_k_3996_ = lean_ctor_get(v_impl_3914_, 1);
v_v_3997_ = lean_ctor_get(v_impl_3914_, 2);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_impl_3914_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; lean_object* v_unused_4008_; lean_object* v_unused_4009_; 
v_unused_4007_ = lean_ctor_get(v_impl_3914_, 4);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v_impl_3914_, 3);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_impl_3914_, 0);
lean_dec(v_unused_4009_);
v___x_3999_ = v_impl_3914_;
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_v_3997_);
lean_inc(v_k_3996_);
lean_dec(v_impl_3914_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = lean_unsigned_to_nat(3u);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 4, v_l_3968_);
lean_ctor_set(v___x_3999_, 2, v_v_3756_);
lean_ctor_set(v___x_3999_, 1, v_k_3755_);
lean_ctor_set(v___x_3999_, 0, v___x_3915_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_l_3968_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_l_3968_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4001_);
lean_ctor_set(v___x_4004_, 1, v_k_3996_);
lean_ctor_set(v___x_4004_, 2, v_v_3997_);
lean_ctor_set(v___x_4004_, 3, v___x_4003_);
lean_ctor_set(v___x_4004_, 4, v_r_3995_);
return v___x_4004_;
}
}
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_unsigned_to_nat(2u);
v___x_4011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
lean_ctor_set(v___x_4011_, 1, v_k_3755_);
lean_ctor_set(v___x_4011_, 2, v_v_3756_);
lean_ctor_set(v___x_4011_, 3, v_r_3995_);
lean_ctor_set(v___x_4011_, 4, v_impl_3914_);
return v___x_4011_;
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
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_unsigned_to_nat(1u);
v___x_4020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
lean_ctor_set(v___x_4020_, 1, v_k_3737_);
lean_ctor_set(v___x_4020_, 2, v_v_3738_);
lean_ctor_set(v___x_4020_, 3, v_t_3739_);
lean_ctor_set(v___x_4020_, 4, v_t_3739_);
return v___x_4020_;
}
v___jp_3740_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = lean_nat_add(v___y_3746_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec(v___y_3746_);
v___x_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set(v___x_3752_, 1, v___y_3745_);
lean_ctor_set(v___x_3752_, 2, v___y_3748_);
lean_ctor_set(v___x_3752_, 3, v___y_3741_);
lean_ctor_set(v___x_3752_, 4, v___y_3749_);
v___x_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3753_, 0, v___y_3744_);
lean_ctor_set(v___x_3753_, 1, v___y_3742_);
lean_ctor_set(v___x_3753_, 2, v___y_3747_);
lean_ctor_set(v___x_3753_, 3, v___y_3743_);
lean_ctor_set(v___x_3753_, 4, v___x_3752_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4021_, lean_object* v_k_4022_, lean_object* v_fallback_4023_){
_start:
{
if (lean_obj_tag(v_t_4021_) == 0)
{
lean_object* v_k_4024_; lean_object* v_v_4025_; lean_object* v_l_4026_; lean_object* v_r_4027_; uint8_t v___y_4029_; lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v_fst_4034_; lean_object* v_snd_4035_; uint8_t v___x_4036_; 
v_k_4024_ = lean_ctor_get(v_t_4021_, 1);
v_v_4025_ = lean_ctor_get(v_t_4021_, 2);
v_l_4026_ = lean_ctor_get(v_t_4021_, 3);
v_r_4027_ = lean_ctor_get(v_t_4021_, 4);
v_fst_4032_ = lean_ctor_get(v_k_4022_, 0);
v_snd_4033_ = lean_ctor_get(v_k_4022_, 1);
v_fst_4034_ = lean_ctor_get(v_k_4024_, 0);
v_snd_4035_ = lean_ctor_get(v_k_4024_, 1);
v___x_4036_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4032_, v_fst_4034_);
if (v___x_4036_ == 1)
{
uint8_t v___x_4037_; 
v___x_4037_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4033_, v_snd_4035_);
v___y_4029_ = v___x_4037_;
goto v___jp_4028_;
}
else
{
v___y_4029_ = v___x_4036_;
goto v___jp_4028_;
}
v___jp_4028_:
{
switch(v___y_4029_)
{
case 0:
{
v_t_4021_ = v_l_4026_;
goto _start;
}
case 1:
{
lean_inc(v_v_4025_);
return v_v_4025_;
}
default: 
{
v_t_4021_ = v_r_4027_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4023_);
return v_fallback_4023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4038_, lean_object* v_k_4039_, lean_object* v_fallback_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4038_, v_k_4039_, v_fallback_4040_);
lean_dec(v_fallback_4040_);
lean_dec_ref(v_k_4039_);
lean_dec(v_t_4038_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4042_, lean_object* v_as_4043_, size_t v_sz_4044_, size_t v_i_4045_, lean_object* v_b_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = lean_usize_dec_lt(v_i_4045_, v_sz_4044_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; 
lean_dec(v___x_4042_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v_b_4046_);
return v___x_4051_;
}
else
{
lean_object* v_a_4052_; lean_object* v_fst_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4081_; 
v_a_4052_ = lean_array_uget(v_as_4043_, v_i_4045_);
v_fst_4053_ = lean_ctor_get(v_a_4052_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_a_4052_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v_a_4052_, 1);
lean_dec(v_unused_4082_);
v___x_4055_ = v_a_4052_;
v_isShared_4056_ = v_isSharedCheck_4081_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_fst_4053_);
lean_dec(v_a_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4081_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4053_);
v___x_4058_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4053_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___y_4061_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
if (lean_obj_tag(v_a_4059_) == 0)
{
lean_inc(v___x_4042_);
v___y_4061_ = v___x_4042_;
goto v___jp_4060_;
}
else
{
lean_object* v_val_4072_; 
v_val_4072_ = lean_ctor_get(v_a_4059_, 0);
lean_inc(v_val_4072_);
lean_dec_ref_known(v_a_4059_, 1);
v___y_4061_ = v_val_4072_;
goto v___jp_4060_;
}
v___jp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v_fst_4053_);
lean_ctor_set(v___x_4055_, 0, v___y_4061_);
v___x_4063_ = v___x_4055_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___y_4061_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_fst_4053_);
v___x_4063_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; size_t v___x_4068_; size_t v___x_4069_; 
v___x_4064_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4046_, v___x_4063_, v___x_4057_);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_nat_add(v___x_4064_, v___x_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4063_, v___x_4066_, v_b_4046_);
v___x_4068_ = ((size_t)1ULL);
v___x_4069_ = lean_usize_add(v_i_4045_, v___x_4068_);
v_i_4045_ = v___x_4069_;
v_b_4046_ = v___x_4067_;
goto _start;
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4055_);
lean_dec(v_fst_4053_);
lean_dec(v_b_4046_);
lean_dec(v___x_4042_);
v_a_4073_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4058_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4058_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4083_, lean_object* v_as_4084_, lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_sz_boxed_4091_; size_t v_i_boxed_4092_; lean_object* v_res_4093_; 
v_sz_boxed_4091_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4092_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4083_, v_as_4084_, v_sz_boxed_4091_, v_i_boxed_4092_, v_b_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec_ref(v_as_4084_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4094_, lean_object* v_init_4095_, lean_object* v_x_4096_){
_start:
{
if (lean_obj_tag(v_x_4096_) == 0)
{
lean_object* v_k_4098_; lean_object* v_v_4099_; lean_object* v_l_4100_; lean_object* v_r_4101_; uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v_a_4104_; lean_object* v_a_4105_; lean_object* v_fst_4106_; lean_object* v_snd_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4121_; 
v_k_4098_ = lean_ctor_get(v_x_4096_, 1);
lean_inc(v_k_4098_);
v_v_4099_ = lean_ctor_get(v_x_4096_, 2);
lean_inc(v_v_4099_);
v_l_4100_ = lean_ctor_get(v_x_4096_, 3);
lean_inc(v_l_4100_);
v_r_4101_ = lean_ctor_get(v_x_4096_, 4);
lean_inc(v_r_4101_);
lean_dec_ref_known(v_x_4096_, 5);
v___x_4102_ = 1;
lean_inc_ref(v_fst_4094_);
v___x_4103_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4094_, v_init_4095_, v_l_4100_);
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref(v___x_4103_);
v_a_4105_ = lean_ctor_get(v_a_4104_, 0);
lean_inc(v_a_4105_);
lean_dec(v_a_4104_);
v_fst_4106_ = lean_ctor_get(v_k_4098_, 0);
v_snd_4107_ = lean_ctor_get(v_k_4098_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_k_4098_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4109_ = v_k_4098_;
v_isShared_4110_ = v_isSharedCheck_4121_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_snd_4107_);
lean_inc(v_fst_4106_);
lean_dec(v_k_4098_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4121_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_optName_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v_optName_4111_ = lean_ctor_get(v_fst_4094_, 1);
lean_inc(v_optName_4111_);
v___x_4112_ = l_Lean_Name_toString(v_optName_4111_, v___x_4102_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 1);
v___x_4114_ = v___x_4109_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_fst_4106_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_snd_4107_);
v___x_4114_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
double v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4115_ = lean_float_of_nat(v_v_4099_);
v___x_4116_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4116_, 0, v___x_4115_);
v___x_4117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4112_);
lean_ctor_set(v___x_4117_, 1, v___x_4114_);
lean_ctor_set(v___x_4117_, 2, v___x_4116_);
v___x_4118_ = lean_array_push(v_a_4105_, v___x_4117_);
v_init_4095_ = v___x_4118_;
v_x_4096_ = v_r_4101_;
goto _start;
}
}
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec_ref(v_fst_4094_);
v___x_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_init_4095_);
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
return v___x_4123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4124_, lean_object* v_init_4125_, lean_object* v_x_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4124_, v_init_4125_, v_x_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4129_, lean_object* v_as_4130_, size_t v_sz_4131_, size_t v_i_4132_, lean_object* v_b_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_a_4138_; uint8_t v___x_4142_; 
v___x_4142_ = lean_usize_dec_lt(v_i_4132_, v_sz_4131_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; 
lean_dec(v___x_4129_);
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v_b_4133_);
return v___x_4143_;
}
else
{
lean_object* v_a_4144_; lean_object* v_snd_4145_; lean_object* v_fst_4146_; lean_object* v_size_4147_; lean_object* v_buckets_4148_; lean_object* v___x_4149_; lean_object* v___y_4151_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_a_4144_ = lean_array_uget_borrowed(v_as_4130_, v_i_4132_);
v_snd_4145_ = lean_ctor_get(v_a_4144_, 1);
v_fst_4146_ = lean_ctor_get(v_a_4144_, 0);
v_size_4147_ = lean_ctor_get(v_snd_4145_, 0);
v_buckets_4148_ = lean_ctor_get(v_snd_4145_, 1);
v___x_4149_ = lean_box(1);
v___x_4185_ = lean_mk_empty_array_with_capacity(v_size_4147_);
v___x_4186_ = lean_unsigned_to_nat(0u);
v___x_4187_ = lean_array_get_size(v_buckets_4148_);
v___x_4188_ = lean_nat_dec_lt(v___x_4186_, v___x_4187_);
if (v___x_4188_ == 0)
{
v___y_4151_ = v___x_4185_;
goto v___jp_4150_;
}
else
{
size_t v___x_4189_; size_t v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = ((size_t)0ULL);
v___x_4190_ = lean_usize_of_nat(v___x_4187_);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4148_, v___x_4189_, v___x_4190_, v___x_4185_);
v___y_4151_ = v___x_4191_;
goto v___jp_4150_;
}
v___jp_4150_:
{
size_t v_sz_4152_; size_t v___x_4153_; lean_object* v___x_4154_; 
v_sz_4152_ = lean_array_size(v___y_4151_);
v___x_4153_ = ((size_t)0ULL);
lean_inc(v___x_4129_);
v___x_4154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4129_, v___y_4151_, v_sz_4152_, v___x_4153_, v___x_4149_, v___y_4134_, v___y_4135_);
lean_dec_ref(v___y_4151_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
lean_inc(v_fst_4146_);
v___x_4156_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4146_, v_b_4133_, v_a_4155_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v_a_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v_a_4158_ = lean_ctor_get(v_a_4157_, 0);
lean_inc(v_a_4158_);
lean_dec(v_a_4157_);
v_a_4138_ = v_a_4158_;
goto v___jp_4137_;
}
else
{
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4168_; 
v_a_4159_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4161_ = v___x_4156_;
v_isShared_4162_ = v_isSharedCheck_4168_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4156_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4168_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
if (lean_obj_tag(v_a_4159_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; 
lean_dec(v___x_4129_);
v_a_4163_ = lean_ctor_get(v_a_4159_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v_a_4159_, 1);
if (v_isShared_4162_ == 0)
{
lean_ctor_set_tag(v___x_4161_, 0);
lean_ctor_set(v___x_4161_, 0, v_a_4163_);
v___x_4165_ = v___x_4161_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
else
{
lean_object* v_a_4167_; 
lean_del_object(v___x_4161_);
v_a_4167_ = lean_ctor_get(v_a_4159_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v_a_4159_, 1);
v_a_4138_ = v_a_4167_;
goto v___jp_4137_;
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v___x_4129_);
v_a_4169_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4156_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4156_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec_ref(v_b_4133_);
lean_dec(v___x_4129_);
v_a_4177_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4154_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4154_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
v___jp_4137_:
{
size_t v___x_4139_; size_t v___x_4140_; 
v___x_4139_ = ((size_t)1ULL);
v___x_4140_ = lean_usize_add(v_i_4132_, v___x_4139_);
v_i_4132_ = v___x_4140_;
v_b_4133_ = v_a_4138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4192_, lean_object* v_as_4193_, lean_object* v_sz_4194_, lean_object* v_i_4195_, lean_object* v_b_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
size_t v_sz_boxed_4200_; size_t v_i_boxed_4201_; lean_object* v_res_4202_; 
v_sz_boxed_4200_ = lean_unbox_usize(v_sz_4194_);
lean_dec(v_sz_4194_);
v_i_boxed_4201_ = lean_unbox_usize(v_i_4195_);
lean_dec(v_i_4195_);
v_res_4202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4192_, v_as_4193_, v_sz_boxed_4200_, v_i_boxed_4201_, v_b_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_as_4193_);
return v_res_4202_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = l_Lean_maxRecDepth;
v___x_4210_ = l_Lean_Options_empty;
v___x_4211_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4212_, lean_object* v_linterOpts_4213_, lean_object* v_sp_4214_, lean_object* v_env_4215_, lean_object* v_mod_4216_){
_start:
{
lean_object* v_a_4219_; lean_object* v_msg_4223_; lean_object* v_a_4228_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_a_4267_; lean_object* v___y_4271_; uint8_t v___y_4274_; uint8_t v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; uint8_t v___y_4281_; uint8_t v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; uint8_t v___y_4356_; uint8_t v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___x_4395_; lean_object* v___x_4396_; uint8_t v___x_4397_; lean_object* v___y_4399_; lean_object* v___x_4417_; uint8_t v___y_4419_; lean_object* v_env_4439_; uint8_t v___x_4440_; 
v___x_4242_ = l_Lean_Name_getRoot(v_mod_4216_);
v___x_4243_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4244_ = l_Lean_instInhabitedFileMap_default;
v___x_4245_ = l_Lean_Options_empty;
v___x_4246_ = lean_box(0);
v___x_4247_ = lean_box(0);
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4250_ = l_Lean_firstFrontendMacroScope;
v___x_4251_ = lean_box(0);
v___x_4252_ = lean_box(0);
v___x_4253_ = 0;
v___x_4254_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4255_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9));
v___x_4256_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4257_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_4258_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4259_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4260_ = 1;
v___x_4261_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4262_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19));
v___x_4263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4263_, 0, v_env_4215_);
lean_ctor_set(v___x_4263_, 1, v___x_4254_);
lean_ctor_set(v___x_4263_, 2, v___x_4255_);
lean_ctor_set(v___x_4263_, 3, v___x_4256_);
lean_ctor_set(v___x_4263_, 4, v___x_4257_);
lean_ctor_set(v___x_4263_, 5, v___x_4258_);
lean_ctor_set(v___x_4263_, 6, v___x_4259_);
lean_ctor_set(v___x_4263_, 7, v___x_4261_);
lean_ctor_set(v___x_4263_, 8, v___x_4262_);
v___x_4264_ = lean_io_get_num_heartbeats();
v___x_4265_ = lean_st_mk_ref(v___x_4263_);
v___x_4395_ = l_Lean_inheritedTraceOptions;
v___x_4396_ = lean_st_ref_get(v___x_4395_);
v___x_4397_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4417_ = lean_st_ref_get(v___x_4265_);
v_env_4439_ = lean_ctor_get(v___x_4417_, 0);
lean_inc_ref(v_env_4439_);
lean_dec(v___x_4417_);
v___x_4440_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4439_);
lean_dec_ref(v_env_4439_);
if (v___x_4397_ == 0)
{
if (v___x_4440_ == 0)
{
lean_inc(v___x_4265_);
v___y_4399_ = v___x_4265_;
goto v___jp_4398_;
}
else
{
v___y_4419_ = v___x_4397_;
goto v___jp_4418_;
}
}
else
{
v___y_4419_ = v___x_4440_;
goto v___jp_4418_;
}
v___jp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_mk_io_user_error(v_a_4219_);
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
v___jp_4222_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = l_Lean_MessageData_toString(v_msg_4223_);
v___x_4225_ = lean_mk_io_user_error(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
return v___x_4226_;
}
v___jp_4227_:
{
if (lean_obj_tag(v_a_4228_) == 0)
{
lean_object* v_msg_4229_; 
v_msg_4229_ = lean_ctor_get(v_a_4228_, 1);
lean_inc_ref(v_msg_4229_);
lean_dec_ref_known(v_a_4228_, 2);
v_msg_4223_ = v_msg_4229_;
goto v___jp_4222_;
}
else
{
lean_object* v_id_4230_; lean_object* v___x_4231_; 
v_id_4230_ = lean_ctor_get(v_a_4228_, 0);
lean_inc(v_id_4230_);
lean_dec_ref_known(v_a_4228_, 2);
v___x_4231_ = l_Lean_InternalExceptionId_getName(v_id_4230_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_dec(v_id_4230_);
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4234_ = 1;
v___x_4235_ = l_Lean_Name_toString(v_a_4232_, v___x_4234_);
v___x_4236_ = lean_string_append(v___x_4233_, v___x_4235_);
lean_dec_ref(v___x_4235_);
v_a_4219_ = v___x_4236_;
goto v___jp_4218_;
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec_ref_known(v___x_4231_, 1);
v___x_4237_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4238_ = l_Nat_reprFast(v_id_4230_);
v___x_4239_ = lean_string_append(v___x_4237_, v___x_4238_);
lean_dec_ref(v___x_4238_);
v___x_4240_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4241_ = lean_string_append(v___x_4239_, v___x_4240_);
v_a_4219_ = v___x_4241_;
goto v___jp_4218_;
}
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_st_ref_get(v___x_4265_);
lean_dec(v___x_4265_);
lean_dec(v___x_4268_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_a_4267_);
return v___x_4269_;
}
v___jp_4270_:
{
lean_object* v_a_4272_; 
v_a_4272_ = lean_ctor_get(v___y_4271_, 0);
lean_inc(v_a_4272_);
lean_dec_ref(v___y_4271_);
v_a_4267_ = v_a_4272_;
goto v___jp_4266_;
}
v___jp_4273_:
{
switch(v___y_4275_)
{
case 0:
{
lean_dec(v_sp_4214_);
if (v___y_4281_ == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4277_);
v___x_4282_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4216_, v___x_4260_);
v___x_4284_ = lean_string_append(v___x_4282_, v___x_4283_);
lean_dec_ref(v___x_4283_);
v___x_4285_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4286_ = lean_string_append(v___x_4284_, v___x_4285_);
v___x_4287_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4281_, v_a_4288_, v___y_4276_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
v___y_4271_ = v___x_4289_;
goto v___jp_4270_;
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
lean_dec(v___x_4265_);
v_a_4290_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4292_ = v___x_4287_;
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4287_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; lean_object* v___x_4296_; 
v___x_4294_ = lean_io_error_to_string(v_a_4290_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 3);
lean_ctor_set(v___x_4292_, 0, v___x_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4294_);
v___x_4296_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_MessageData_ofFormat(v___x_4296_);
v_msg_4223_ = v___x_4297_;
goto v___jp_4222_;
}
}
}
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4300_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4216_, v___y_4281_);
v___x_4302_ = lean_string_append(v___x_4300_, v___x_4301_);
lean_dec_ref(v___x_4301_);
v___x_4303_ = lean_array_get_size(v___y_4280_);
lean_dec_ref(v___y_4280_);
v___x_4304_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4278_, v___y_4277_, v___x_4260_, v___x_4302_, v___x_4303_, v___x_4260_, v___y_4276_, v___y_4279_);
lean_dec_ref(v___y_4277_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4304_, 1);
v___x_4306_ = l_Lean_MessageData_toString(v_a_4305_);
v___x_4307_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4306_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4281_, v_a_4308_, v___y_4276_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
v___y_4271_ = v___x_4309_;
goto v___jp_4270_;
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
lean_dec(v___x_4265_);
v_a_4310_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4312_ = v___x_4307_;
v_isShared_4313_ = v_isSharedCheck_4319_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4307_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4319_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4314_ = lean_io_error_to_string(v_a_4310_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 3);
lean_ctor_set(v___x_4312_, 0, v___x_4314_);
v___x_4316_ = v___x_4312_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_MessageData_ofFormat(v___x_4316_);
v_msg_4223_ = v___x_4317_;
goto v___jp_4222_;
}
}
}
}
else
{
lean_object* v_a_4320_; 
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
lean_dec(v___x_4265_);
v_a_4320_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4304_, 1);
v_a_4228_ = v_a_4320_;
goto v___jp_4227_;
}
}
}
case 1:
{
lean_object* v___x_4321_; lean_object* v_env_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; size_t v_sz_4326_; size_t v___x_4327_; lean_object* v___x_4328_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v_mod_4216_);
v___x_4321_ = lean_st_ref_get(v___y_4279_);
v_env_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc_ref(v_env_4322_);
lean_dec(v___x_4321_);
v___x_4323_ = l_Lean_Environment_mainModule(v_env_4322_);
lean_dec_ref(v_env_4322_);
v___x_4324_ = lean_box(v___y_4274_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4262_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v_sz_4326_ = lean_array_size(v___y_4278_);
v___x_4327_ = ((size_t)0ULL);
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4214_, v___x_4323_, v___y_4278_, v_sz_4326_, v___x_4327_, v___x_4325_, v___y_4276_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
lean_dec_ref(v___y_4278_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v_fst_4330_; lean_object* v_snd_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v_fst_4330_ = lean_ctor_get(v_a_4329_, 0);
lean_inc(v_fst_4330_);
v_snd_4331_ = lean_ctor_get(v_a_4329_, 1);
lean_inc(v_snd_4331_);
lean_dec(v_a_4329_);
v___x_4332_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4332_, 0, v_fst_4330_);
v___x_4333_ = lean_unbox(v_snd_4331_);
lean_dec(v_snd_4331_);
lean_ctor_set_uint8(v___x_4332_, sizeof(void*)*1, v___x_4333_);
v_a_4267_ = v___x_4332_;
goto v___jp_4266_;
}
else
{
lean_object* v_a_4334_; 
lean_dec(v___x_4265_);
v_a_4334_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4328_, 1);
v_a_4228_ = v_a_4334_;
goto v___jp_4227_;
}
}
default: 
{
lean_object* v___x_4335_; lean_object* v_env_4336_; lean_object* v___x_4337_; size_t v_sz_4338_; size_t v___x_4339_; lean_object* v___x_4340_; 
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v_mod_4216_);
lean_dec(v_sp_4214_);
v___x_4335_ = lean_st_ref_get(v___y_4279_);
v_env_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc_ref(v_env_4336_);
lean_dec(v___x_4335_);
v___x_4337_ = l_Lean_Environment_mainModule(v_env_4336_);
lean_dec_ref(v_env_4336_);
v_sz_4338_ = lean_array_size(v___y_4278_);
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4337_, v___y_4278_, v_sz_4338_, v___x_4339_, v___x_4262_, v___y_4276_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4276_);
lean_dec_ref(v___y_4278_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4340_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
lean_ctor_set_tag(v___x_4343_, 2);
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
v_a_4267_ = v___x_4346_;
goto v___jp_4266_;
}
}
}
else
{
lean_object* v_a_4349_; 
lean_dec(v___x_4265_);
v_a_4349_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4340_, 1);
v_a_4228_ = v_a_4349_;
goto v___jp_4227_;
}
}
}
}
v___jp_4350_:
{
lean_object* v___x_4357_; 
lean_inc_ref(v___y_4355_);
v___x_4357_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4353_, v___y_4355_, v___y_4352_, v___y_4354_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = lean_array_get_size(v_a_4358_);
v___x_4360_ = lean_nat_dec_lt(v___x_4248_, v___x_4359_);
if (v___x_4360_ == 0)
{
v___y_4274_ = v___y_4356_;
v___y_4275_ = v___y_4351_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4358_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4355_;
v___y_4281_ = v___x_4360_;
goto v___jp_4273_;
}
else
{
if (v___x_4360_ == 0)
{
v___y_4274_ = v___y_4356_;
v___y_4275_ = v___y_4351_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4358_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4355_;
v___y_4281_ = v___x_4360_;
goto v___jp_4273_;
}
else
{
size_t v___x_4361_; size_t v___x_4362_; uint8_t v___x_4363_; 
v___x_4361_ = ((size_t)0ULL);
v___x_4362_ = lean_usize_of_nat(v___x_4359_);
v___x_4363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4356_, v_a_4358_, v___x_4361_, v___x_4362_);
v___y_4274_ = v___y_4356_;
v___y_4275_ = v___y_4351_;
v___y_4276_ = v___y_4352_;
v___y_4277_ = v___y_4353_;
v___y_4278_ = v_a_4358_;
v___y_4279_ = v___y_4354_;
v___y_4280_ = v___y_4355_;
v___y_4281_ = v___x_4363_;
goto v___jp_4273_;
}
}
}
else
{
lean_object* v_a_4364_; 
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___x_4265_);
lean_dec(v_mod_4216_);
lean_dec(v_sp_4214_);
v_a_4364_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4357_, 1);
v_a_4228_ = v_a_4364_;
goto v___jp_4227_;
}
}
v___jp_4365_:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4370_, v___y_4367_, v___y_4369_);
lean_dec(v___y_4370_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v___x_4373_ = lean_array_get_size(v_a_4372_);
v___x_4374_ = lean_nat_dec_eq(v___x_4373_, v___x_4248_);
if (v___x_4374_ == 0)
{
v___y_4351_ = v___y_4366_;
v___y_4352_ = v___y_4367_;
v___y_4353_ = v___y_4368_;
v___y_4354_ = v___y_4369_;
v___y_4355_ = v_a_4372_;
v___y_4356_ = v___x_4374_;
goto v___jp_4350_;
}
else
{
uint8_t v___x_4375_; uint8_t v___x_4376_; 
v___x_4375_ = 0;
v___x_4376_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4366_, v___x_4375_);
if (v___x_4376_ == 0)
{
v___y_4351_ = v___y_4366_;
v___y_4352_ = v___y_4367_;
v___y_4353_ = v___y_4368_;
v___y_4354_ = v___y_4369_;
v___y_4355_ = v_a_4372_;
v___y_4356_ = v___x_4376_;
goto v___jp_4350_;
}
else
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec(v_a_4372_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v_sp_4214_);
v___x_4377_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4216_, v___x_4376_);
v___x_4379_ = lean_string_append(v___x_4377_, v___x_4378_);
lean_dec_ref(v___x_4378_);
v___x_4380_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4381_ = lean_string_append(v___x_4379_, v___x_4380_);
v___x_4382_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4381_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v___x_4383_; 
lean_dec_ref_known(v___x_4382_, 1);
v___x_4383_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4267_ = v___x_4383_;
goto v___jp_4266_;
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v___x_4265_);
v_a_4384_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4386_ = v___x_4382_;
v_isShared_4387_ = v_isSharedCheck_4393_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4382_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4393_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4388_ = lean_io_error_to_string(v_a_4384_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 3);
lean_ctor_set(v___x_4386_, 0, v___x_4388_);
v___x_4390_ = v___x_4386_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_MessageData_ofFormat(v___x_4390_);
v_msg_4223_ = v___x_4391_;
goto v___jp_4222_;
}
}
}
}
}
}
else
{
lean_object* v_a_4394_; 
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___x_4265_);
lean_dec(v_mod_4216_);
lean_dec(v_sp_4214_);
v_a_4394_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4371_, 1);
v_a_4228_ = v_a_4394_;
goto v___jp_4227_;
}
}
v___jp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4400_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
v___x_4401_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4243_);
lean_ctor_set(v___x_4401_, 1, v___x_4244_);
lean_ctor_set(v___x_4401_, 2, v___x_4245_);
lean_ctor_set(v___x_4401_, 3, v___x_4400_);
lean_ctor_set(v___x_4401_, 4, v___x_4246_);
lean_ctor_set(v___x_4401_, 5, v___x_4247_);
lean_ctor_set(v___x_4401_, 6, v___x_4264_);
lean_ctor_set(v___x_4401_, 7, v___x_4249_);
lean_ctor_set(v___x_4401_, 8, v___x_4246_);
lean_ctor_set(v___x_4401_, 9, v___x_4250_);
lean_ctor_set(v___x_4401_, 10, v___x_4251_);
lean_ctor_set(v___x_4401_, 11, v___x_4396_);
v___x_4402_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
lean_ctor_set(v___x_4402_, 1, v___x_4248_);
lean_ctor_set(v___x_4402_, 2, v___x_4252_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*3, v___x_4397_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*3 + 1, v___x_4253_);
v___x_4403_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4242_, v___y_4399_);
lean_dec(v___x_4242_);
if (lean_obj_tag(v___x_4403_) == 0)
{
uint8_t v_lintOnly_4404_; 
v_lintOnly_4404_ = lean_ctor_get_uint8(v_args_4212_, sizeof(void*)*4);
if (v_lintOnly_4404_ == 0)
{
lean_object* v_a_4405_; uint8_t v_mode_4406_; 
lean_dec_ref(v_linterOpts_4213_);
v_a_4405_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4403_, 1);
v_mode_4406_ = lean_ctor_get_uint8(v_args_4212_, sizeof(void*)*4 + 1);
v___y_4366_ = v_mode_4406_;
v___y_4367_ = v___x_4402_;
v___y_4368_ = v_a_4405_;
v___y_4369_ = v___y_4399_;
v___y_4370_ = v___x_4251_;
goto v___jp_4365_;
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4415_; 
v_a_4407_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4409_ = v___x_4403_;
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4403_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
uint8_t v_mode_4411_; lean_object* v___x_4413_; 
v_mode_4411_ = lean_ctor_get_uint8(v_args_4212_, sizeof(void*)*4 + 1);
if (v_isShared_4410_ == 0)
{
lean_ctor_set_tag(v___x_4409_, 1);
lean_ctor_set(v___x_4409_, 0, v_linterOpts_4213_);
v___x_4413_ = v___x_4409_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_linterOpts_4213_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
v___y_4366_ = v_mode_4411_;
v___y_4367_ = v___x_4402_;
v___y_4368_ = v_a_4407_;
v___y_4369_ = v___y_4399_;
v___y_4370_ = v___x_4413_;
goto v___jp_4365_;
}
}
}
}
else
{
lean_object* v_a_4416_; 
lean_dec_ref_known(v___x_4402_, 3);
lean_dec(v___y_4399_);
lean_dec(v___x_4265_);
lean_dec(v_mod_4216_);
lean_dec(v_sp_4214_);
lean_dec_ref(v_linterOpts_4213_);
v_a_4416_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4403_, 1);
v_a_4228_ = v_a_4416_;
goto v___jp_4227_;
}
}
v___jp_4418_:
{
if (v___y_4419_ == 0)
{
lean_object* v___x_4420_; lean_object* v_env_4421_; lean_object* v_nextMacroScope_4422_; lean_object* v_ngen_4423_; lean_object* v_auxDeclNGen_4424_; lean_object* v_traceState_4425_; lean_object* v_messages_4426_; lean_object* v_infoState_4427_; lean_object* v_snapshotTasks_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4437_; 
v___x_4420_ = lean_st_ref_take(v___x_4265_);
v_env_4421_ = lean_ctor_get(v___x_4420_, 0);
v_nextMacroScope_4422_ = lean_ctor_get(v___x_4420_, 1);
v_ngen_4423_ = lean_ctor_get(v___x_4420_, 2);
v_auxDeclNGen_4424_ = lean_ctor_get(v___x_4420_, 3);
v_traceState_4425_ = lean_ctor_get(v___x_4420_, 4);
v_messages_4426_ = lean_ctor_get(v___x_4420_, 6);
v_infoState_4427_ = lean_ctor_get(v___x_4420_, 7);
v_snapshotTasks_4428_ = lean_ctor_get(v___x_4420_, 8);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; 
v_unused_4438_ = lean_ctor_get(v___x_4420_, 5);
lean_dec(v_unused_4438_);
v___x_4430_ = v___x_4420_;
v_isShared_4431_ = v_isSharedCheck_4437_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snapshotTasks_4428_);
lean_inc(v_infoState_4427_);
lean_inc(v_messages_4426_);
lean_inc(v_traceState_4425_);
lean_inc(v_auxDeclNGen_4424_);
lean_inc(v_ngen_4423_);
lean_inc(v_nextMacroScope_4422_);
lean_inc(v_env_4421_);
lean_dec(v___x_4420_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4437_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = l_Lean_Kernel_enableDiag(v_env_4421_, v___x_4397_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 5, v___x_4258_);
lean_ctor_set(v___x_4430_, 0, v___x_4432_);
v___x_4434_ = v___x_4430_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_nextMacroScope_4422_);
lean_ctor_set(v_reuseFailAlloc_4436_, 2, v_ngen_4423_);
lean_ctor_set(v_reuseFailAlloc_4436_, 3, v_auxDeclNGen_4424_);
lean_ctor_set(v_reuseFailAlloc_4436_, 4, v_traceState_4425_);
lean_ctor_set(v_reuseFailAlloc_4436_, 5, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4436_, 6, v_messages_4426_);
lean_ctor_set(v_reuseFailAlloc_4436_, 7, v_infoState_4427_);
lean_ctor_set(v_reuseFailAlloc_4436_, 8, v_snapshotTasks_4428_);
v___x_4434_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_st_ref_put(v___x_4265_, v___x_4434_);
lean_inc(v___x_4265_);
v___y_4399_ = v___x_4265_;
goto v___jp_4398_;
}
}
}
else
{
lean_inc(v___x_4265_);
v___y_4399_ = v___x_4265_;
goto v___jp_4398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4441_, lean_object* v_linterOpts_4442_, lean_object* v_sp_4443_, lean_object* v_env_4444_, lean_object* v_mod_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4441_, v_linterOpts_4442_, v_sp_4443_, v_env_4444_, v_mod_4445_);
lean_dec_ref(v_args_4441_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4448_, lean_object* v_t_4449_, lean_object* v_k_4450_, lean_object* v_fallback_4451_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4449_, v_k_4450_, v_fallback_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4453_, lean_object* v_t_4454_, lean_object* v_k_4455_, lean_object* v_fallback_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4453_, v_t_4454_, v_k_4455_, v_fallback_4456_);
lean_dec(v_fallback_4456_);
lean_dec_ref(v_k_4455_);
lean_dec(v_t_4454_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4458_, lean_object* v_k_4459_, lean_object* v_v_4460_, lean_object* v_t_4461_, lean_object* v_hl_4462_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4459_, v_v_4460_, v_t_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4464_, lean_object* v_init_4465_, lean_object* v_x_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4464_, v_init_4465_, v_x_4466_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4471_, lean_object* v_init_4472_, lean_object* v_x_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4471_, v_init_4472_, v_x_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4478_, lean_object* v_constName_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4479_, v___y_4480_, v___y_4481_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4484_, lean_object* v_constName_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4484_, v_constName_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4490_, lean_object* v_ref_4491_, lean_object* v_constName_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4491_, v_constName_4492_, v___y_4493_, v___y_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4497_, lean_object* v_ref_4498_, lean_object* v_constName_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4497_, v_ref_4498_, v_constName_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v_ref_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4504_, lean_object* v_ref_4505_, lean_object* v_msg_4506_, lean_object* v_declHint_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4505_, v_msg_4506_, v_declHint_4507_, v___y_4508_, v___y_4509_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4512_, lean_object* v_ref_4513_, lean_object* v_msg_4514_, lean_object* v_declHint_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4512_, v_ref_4513_, v_msg_4514_, v_declHint_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v_ref_4513_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4520_, lean_object* v_declHint_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4520_, v_declHint_4521_, v___y_4523_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4526_, lean_object* v_declHint_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4526_, v_declHint_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4532_, lean_object* v_ref_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4533_, v_msg_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4539_, lean_object* v_ref_4540_, lean_object* v_msg_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4539_, v_ref_4540_, v_msg_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v_ref_4540_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4546_, lean_object* v_msg_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4547_, v___y_4548_, v___y_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4552_, lean_object* v_msg_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4552_, v_msg_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; uint32_t v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4560_ = l_Std_Format_defWidth;
v___x_4561_ = lean_unsigned_to_nat(0u);
v___x_4562_ = l_Std_Format_pretty(v_s_4558_, v___x_4560_, v___x_4561_, v___x_4561_);
v___x_4563_ = 10;
v___x_4564_ = lean_string_push(v___x_4562_, v___x_4563_);
v___x_4565_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4566_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4569_, size_t v_sz_4570_, size_t v_i_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v___x_4575_; 
v___x_4575_ = lean_usize_dec_lt(v_i_4571_, v_sz_4570_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4572_);
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; lean_object* v_a_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v_ref_4581_; lean_object* v___x_4582_; 
v___x_4577_ = lean_box(0);
v_a_4578_ = lean_array_uget_borrowed(v_as_4569_, v_i_4571_);
v___x_4579_ = lean_box(0);
lean_inc(v_a_4578_);
v___x_4580_ = l_Lean_MessageData_format(v_a_4578_, v___x_4579_);
v_ref_4581_ = lean_ctor_get(v___y_4573_, 2);
v___x_4582_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4580_);
if (lean_obj_tag(v___x_4582_) == 0)
{
size_t v___x_4583_; size_t v___x_4584_; 
lean_dec_ref_known(v___x_4582_, 1);
v___x_4583_ = ((size_t)1ULL);
v___x_4584_ = lean_usize_add(v_i_4571_, v___x_4583_);
v_i_4571_ = v___x_4584_;
v_b_4572_ = v___x_4577_;
goto _start;
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4597_; 
v_a_4586_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4588_ = v___x_4582_;
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4582_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4590_ = lean_io_error_to_string(v_a_4586_);
v___x_4591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
v___x_4592_ = l_Lean_MessageData_ofFormat(v___x_4591_);
lean_inc(v_ref_4581_);
v___x_4593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4593_, 0, v_ref_4581_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4593_);
v___x_4595_ = v___x_4588_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4598_, lean_object* v_sz_4599_, lean_object* v_i_4600_, lean_object* v_b_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
size_t v_sz_boxed_4604_; size_t v_i_boxed_4605_; lean_object* v_res_4606_; 
v_sz_boxed_4604_ = lean_unbox_usize(v_sz_4599_);
lean_dec(v_sz_4599_);
v_i_boxed_4605_ = lean_unbox_usize(v_i_4600_);
lean_dec(v_i_4600_);
v_res_4606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4598_, v_sz_boxed_4604_, v_i_boxed_4605_, v_b_4601_, v___y_4602_);
lean_dec_ref(v___y_4602_);
lean_dec_ref(v_as_4598_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4607_, lean_object* v_entries_4608_, lean_object* v_____r_4609_, uint8_t v_anyFailed_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v___x_4614_; size_t v_sz_4615_; size_t v___x_4616_; lean_object* v___x_4617_; 
v___x_4614_ = lean_box(0);
v_sz_4615_ = lean_array_size(v_errors_4607_);
v___x_4616_ = ((size_t)0ULL);
v___x_4617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4607_, v_sz_4615_, v___x_4616_, v___x_4614_, v___y_4611_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4626_; 
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4617_, 0);
lean_dec(v_unused_4627_);
v___x_4619_ = v___x_4617_;
v_isShared_4620_ = v_isSharedCheck_4626_;
goto v_resetjp_4618_;
}
else
{
lean_dec(v___x_4617_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4626_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
v___x_4621_ = lean_box(v_anyFailed_4610_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_entries_4608_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v___x_4622_);
v___x_4624_ = v___x_4619_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v_entries_4608_);
v_a_4628_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4617_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4617_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4636_, lean_object* v_entries_4637_, lean_object* v_____r_4638_, lean_object* v_anyFailed_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
uint8_t v_anyFailed_boxed_4643_; lean_object* v_res_4644_; 
v_anyFailed_boxed_4643_ = lean_unbox(v_anyFailed_4639_);
v_res_4644_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4636_, v_entries_4637_, v_____r_4638_, v_anyFailed_boxed_4643_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec_ref(v_errors_4636_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4645_, lean_object* v_env_4646_, lean_object* v_mod_4647_){
_start:
{
lean_object* v_a_4650_; lean_object* v_a_4654_; uint8_t v_anyFailed_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___y_4697_; lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; lean_object* v___y_4716_; lean_object* v___x_4735_; uint8_t v___y_4737_; lean_object* v_env_4757_; uint8_t v___x_4758_; 
v_anyFailed_4671_ = 0;
v___x_4672_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4673_ = l_Lean_instInhabitedFileMap_default;
v___x_4674_ = l_Lean_Options_empty;
v___x_4675_ = lean_box(0);
v___x_4676_ = lean_box(0);
v___x_4677_ = lean_unsigned_to_nat(0u);
v___x_4678_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4679_ = l_Lean_firstFrontendMacroScope;
v___x_4680_ = lean_box(0);
v___x_4681_ = lean_box(0);
v___x_4682_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4683_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9));
v___x_4684_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4685_ = lean_unsigned_to_nat(32u);
v___x_4686_ = lean_mk_empty_array_with_capacity(v___x_4685_);
lean_dec_ref(v___x_4686_);
v___x_4687_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_4688_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4689_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4690_ = 1;
v___x_4691_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4692_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19));
v___x_4693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4693_, 0, v_env_4646_);
lean_ctor_set(v___x_4693_, 1, v___x_4682_);
lean_ctor_set(v___x_4693_, 2, v___x_4683_);
lean_ctor_set(v___x_4693_, 3, v___x_4684_);
lean_ctor_set(v___x_4693_, 4, v___x_4687_);
lean_ctor_set(v___x_4693_, 5, v___x_4688_);
lean_ctor_set(v___x_4693_, 6, v___x_4689_);
lean_ctor_set(v___x_4693_, 7, v___x_4691_);
lean_ctor_set(v___x_4693_, 8, v___x_4692_);
v___x_4694_ = lean_io_get_num_heartbeats();
v___x_4695_ = lean_st_mk_ref(v___x_4693_);
v___x_4712_ = l_Lean_inheritedTraceOptions;
v___x_4713_ = lean_st_ref_get(v___x_4712_);
v___x_4714_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4735_ = lean_st_ref_get(v___x_4695_);
v_env_4757_ = lean_ctor_get(v___x_4735_, 0);
lean_inc_ref(v_env_4757_);
lean_dec(v___x_4735_);
v___x_4758_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4757_);
lean_dec_ref(v_env_4757_);
if (v___x_4714_ == 0)
{
if (v___x_4758_ == 0)
{
lean_inc(v___x_4695_);
v___y_4716_ = v___x_4695_;
goto v___jp_4715_;
}
else
{
v___y_4737_ = v___x_4714_;
goto v___jp_4736_;
}
}
else
{
v___y_4737_ = v___x_4758_;
goto v___jp_4736_;
}
v___jp_4649_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = lean_mk_io_user_error(v_a_4650_);
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
v___jp_4653_:
{
if (lean_obj_tag(v_a_4654_) == 0)
{
lean_object* v_msg_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v_msg_4655_ = lean_ctor_get(v_a_4654_, 1);
lean_inc_ref(v_msg_4655_);
lean_dec_ref_known(v_a_4654_, 2);
v___x_4656_ = l_Lean_MessageData_toString(v_msg_4655_);
v___x_4657_ = lean_mk_io_user_error(v___x_4656_);
v___x_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
else
{
lean_object* v_id_4659_; lean_object* v___x_4660_; 
v_id_4659_ = lean_ctor_get(v_a_4654_, 0);
lean_inc(v_id_4659_);
lean_dec_ref_known(v_a_4654_, 2);
v___x_4660_ = l_Lean_InternalExceptionId_getName(v_id_4659_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_dec(v_id_4659_);
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v___x_4662_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4663_ = 1;
v___x_4664_ = l_Lean_Name_toString(v_a_4661_, v___x_4663_);
v___x_4665_ = lean_string_append(v___x_4662_, v___x_4664_);
lean_dec_ref(v___x_4664_);
v_a_4650_ = v___x_4665_;
goto v___jp_4649_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
lean_dec_ref_known(v___x_4660_, 1);
v___x_4666_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4667_ = l_Nat_reprFast(v_id_4659_);
v___x_4668_ = lean_string_append(v___x_4666_, v___x_4667_);
lean_dec_ref(v___x_4667_);
v___x_4669_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4670_ = lean_string_append(v___x_4668_, v___x_4669_);
v_a_4650_ = v___x_4670_;
goto v___jp_4649_;
}
}
}
v___jp_4696_:
{
if (lean_obj_tag(v___y_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4710_; 
v_a_4698_ = lean_ctor_get(v___y_4697_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___y_4697_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4700_ = v___y_4697_;
v_isShared_4701_ = v_isSharedCheck_4710_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___y_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4710_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4702_; lean_object* v_fst_4703_; lean_object* v_snd_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4708_; 
v___x_4702_ = lean_st_ref_get(v___x_4695_);
lean_dec(v___x_4695_);
lean_dec(v___x_4702_);
v_fst_4703_ = lean_ctor_get(v_a_4698_, 0);
lean_inc(v_fst_4703_);
v_snd_4704_ = lean_ctor_get(v_a_4698_, 1);
lean_inc(v_snd_4704_);
lean_dec(v_a_4698_);
v___x_4705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4705_, 0, v_fst_4703_);
v___x_4706_ = lean_unbox(v_snd_4704_);
lean_dec(v_snd_4704_);
lean_ctor_set_uint8(v___x_4705_, sizeof(void*)*1, v___x_4706_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 0, v___x_4705_);
v___x_4708_ = v___x_4700_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v___x_4705_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
else
{
lean_object* v_a_4711_; 
lean_dec(v___x_4695_);
v_a_4711_ = lean_ctor_get(v___y_4697_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___y_4697_, 1);
v_a_4654_ = v_a_4711_;
goto v___jp_4653_;
}
}
v___jp_4715_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4717_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
v___x_4718_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4672_);
lean_ctor_set(v___x_4718_, 1, v___x_4673_);
lean_ctor_set(v___x_4718_, 2, v___x_4674_);
lean_ctor_set(v___x_4718_, 3, v___x_4717_);
lean_ctor_set(v___x_4718_, 4, v___x_4675_);
lean_ctor_set(v___x_4718_, 5, v___x_4676_);
lean_ctor_set(v___x_4718_, 6, v___x_4694_);
lean_ctor_set(v___x_4718_, 7, v___x_4678_);
lean_ctor_set(v___x_4718_, 8, v___x_4675_);
lean_ctor_set(v___x_4718_, 9, v___x_4679_);
lean_ctor_set(v___x_4718_, 10, v___x_4680_);
lean_ctor_set(v___x_4718_, 11, v___x_4713_);
v___x_4719_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4719_, 0, v___x_4718_);
lean_ctor_set(v___x_4719_, 1, v___x_4677_);
lean_ctor_set(v___x_4719_, 2, v___x_4681_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*3, v___x_4714_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*3 + 1, v_anyFailed_4671_);
v___x_4720_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4719_, v___y_4716_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v_sp_4645_);
lean_ctor_set(v___x_4722_, 1, v_mod_4647_);
v___x_4723_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4721_, v___x_4722_, v___x_4719_, v___y_4716_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v_entries_4725_; lean_object* v_errors_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v_entries_4725_ = lean_ctor_get(v_a_4724_, 0);
lean_inc_ref(v_entries_4725_);
v_errors_4726_ = lean_ctor_get(v_a_4724_, 1);
lean_inc_ref(v_errors_4726_);
lean_dec(v_a_4724_);
v___x_4727_ = lean_array_get_size(v_errors_4726_);
v___x_4728_ = lean_nat_dec_eq(v___x_4727_, v___x_4677_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = lean_box(0);
v___x_4730_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4726_, v_entries_4725_, v___x_4729_, v___x_4690_, v___x_4719_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref_known(v___x_4719_, 3);
lean_dec_ref(v_errors_4726_);
v___y_4697_ = v___x_4730_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_box(0);
v___x_4732_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4726_, v_entries_4725_, v___x_4731_, v_anyFailed_4671_, v___x_4719_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref_known(v___x_4719_, 3);
lean_dec_ref(v_errors_4726_);
v___y_4697_ = v___x_4732_;
goto v___jp_4696_;
}
}
else
{
lean_object* v_a_4733_; 
lean_dec_ref_known(v___x_4719_, 3);
lean_dec(v___y_4716_);
lean_dec(v___x_4695_);
v_a_4733_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4723_, 1);
v_a_4654_ = v_a_4733_;
goto v___jp_4653_;
}
}
else
{
lean_object* v_a_4734_; 
lean_dec_ref_known(v___x_4719_, 3);
lean_dec(v___y_4716_);
lean_dec(v___x_4695_);
lean_dec(v_mod_4647_);
lean_dec(v_sp_4645_);
v_a_4734_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4720_, 1);
v_a_4654_ = v_a_4734_;
goto v___jp_4653_;
}
}
v___jp_4736_:
{
if (v___y_4737_ == 0)
{
lean_object* v___x_4738_; lean_object* v_env_4739_; lean_object* v_nextMacroScope_4740_; lean_object* v_ngen_4741_; lean_object* v_auxDeclNGen_4742_; lean_object* v_traceState_4743_; lean_object* v_messages_4744_; lean_object* v_infoState_4745_; lean_object* v_snapshotTasks_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4755_; 
v___x_4738_ = lean_st_ref_take(v___x_4695_);
v_env_4739_ = lean_ctor_get(v___x_4738_, 0);
v_nextMacroScope_4740_ = lean_ctor_get(v___x_4738_, 1);
v_ngen_4741_ = lean_ctor_get(v___x_4738_, 2);
v_auxDeclNGen_4742_ = lean_ctor_get(v___x_4738_, 3);
v_traceState_4743_ = lean_ctor_get(v___x_4738_, 4);
v_messages_4744_ = lean_ctor_get(v___x_4738_, 6);
v_infoState_4745_ = lean_ctor_get(v___x_4738_, 7);
v_snapshotTasks_4746_ = lean_ctor_get(v___x_4738_, 8);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4755_ == 0)
{
lean_object* v_unused_4756_; 
v_unused_4756_ = lean_ctor_get(v___x_4738_, 5);
lean_dec(v_unused_4756_);
v___x_4748_ = v___x_4738_;
v_isShared_4749_ = v_isSharedCheck_4755_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_snapshotTasks_4746_);
lean_inc(v_infoState_4745_);
lean_inc(v_messages_4744_);
lean_inc(v_traceState_4743_);
lean_inc(v_auxDeclNGen_4742_);
lean_inc(v_ngen_4741_);
lean_inc(v_nextMacroScope_4740_);
lean_inc(v_env_4739_);
lean_dec(v___x_4738_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4755_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4750_; lean_object* v___x_4752_; 
v___x_4750_ = l_Lean_Kernel_enableDiag(v_env_4739_, v___x_4714_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 5, v___x_4688_);
lean_ctor_set(v___x_4748_, 0, v___x_4750_);
v___x_4752_ = v___x_4748_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_nextMacroScope_4740_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_ngen_4741_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_auxDeclNGen_4742_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v_traceState_4743_);
lean_ctor_set(v_reuseFailAlloc_4754_, 5, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4754_, 6, v_messages_4744_);
lean_ctor_set(v_reuseFailAlloc_4754_, 7, v_infoState_4745_);
lean_ctor_set(v_reuseFailAlloc_4754_, 8, v_snapshotTasks_4746_);
v___x_4752_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4753_; 
v___x_4753_ = lean_st_ref_put(v___x_4695_, v___x_4752_);
lean_inc(v___x_4695_);
v___y_4716_ = v___x_4695_;
goto v___jp_4715_;
}
}
}
else
{
lean_inc(v___x_4695_);
v___y_4716_ = v___x_4695_;
goto v___jp_4715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4759_, lean_object* v_env_4760_, lean_object* v_mod_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4759_, v_env_4760_, v_mod_4761_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4764_, size_t v_sz_4765_, size_t v_i_4766_, lean_object* v_b_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4764_, v_sz_4765_, v_i_4766_, v_b_4767_, v___y_4768_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4772_, lean_object* v_sz_4773_, lean_object* v_i_4774_, lean_object* v_b_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
size_t v_sz_boxed_4779_; size_t v_i_boxed_4780_; lean_object* v_res_4781_; 
v_sz_boxed_4779_ = lean_unbox_usize(v_sz_4773_);
lean_dec(v_sz_4773_);
v_i_boxed_4780_ = lean_unbox_usize(v_i_4774_);
lean_dec(v_i_4774_);
v_res_4781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4772_, v_sz_boxed_4779_, v_i_boxed_4780_, v_b_4775_, v___y_4776_, v___y_4777_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec_ref(v_as_4772_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_enable_initializer_execution();
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4786_){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = lean_compacted_region_free(v_region_4786_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4789_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4795_, lean_object* v_k_4796_, uint8_t v_v_4797_){
_start:
{
lean_object* v_map_4798_; uint8_t v_hasTrace_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4813_; 
v_map_4798_ = lean_ctor_get(v_o_4795_, 0);
v_hasTrace_4799_ = lean_ctor_get_uint8(v_o_4795_, sizeof(void*)*1);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_o_4795_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4801_ = v_o_4795_;
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_map_4798_);
lean_dec(v_o_4795_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4803_, 0, v_v_4797_);
lean_inc(v_k_4796_);
v___x_4804_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4796_, v___x_4803_, v_map_4798_);
if (v_hasTrace_4799_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; lean_object* v___x_4808_; 
v___x_4805_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4806_ = l_Lean_Name_isPrefixOf(v___x_4805_, v_k_4796_);
lean_dec(v_k_4796_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4804_);
v___x_4808_ = v___x_4801_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4804_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_ctor_set_uint8(v___x_4808_, sizeof(void*)*1, v___x_4806_);
return v___x_4808_;
}
}
else
{
lean_object* v___x_4811_; 
lean_dec(v_k_4796_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4804_);
v___x_4811_ = v___x_4801_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4804_);
lean_ctor_set_uint8(v_reuseFailAlloc_4812_, sizeof(void*)*1, v_hasTrace_4799_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4814_, lean_object* v_k_4815_, lean_object* v_v_4816_){
_start:
{
uint8_t v_v_boxed_4817_; lean_object* v_res_4818_; 
v_v_boxed_4817_ = lean_unbox(v_v_4816_);
v_res_4818_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4814_, v_k_4815_, v_v_boxed_4817_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; uint32_t v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4821_ = lean_unsigned_to_nat(80u);
v___x_4822_ = l_Lean_Json_pretty(v_s_4819_, v___x_4821_);
v___x_4823_ = 10;
v___x_4824_ = lean_string_push(v___x_4822_, v___x_4823_);
v___x_4825_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4824_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4829_, size_t v_sz_4830_, size_t v_i_4831_, lean_object* v_b_4832_){
_start:
{
uint8_t v___x_4834_; 
v___x_4834_ = lean_usize_dec_lt(v_i_4831_, v_sz_4830_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; 
v___x_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_b_4832_);
return v___x_4835_;
}
else
{
lean_object* v___x_4836_; lean_object* v_a_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4836_ = lean_box(0);
v_a_4837_ = lean_array_uget_borrowed(v_as_4829_, v_i_4831_);
lean_inc(v_a_4837_);
v___x_4838_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4837_);
v___x_4839_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4838_);
if (lean_obj_tag(v___x_4839_) == 0)
{
size_t v___x_4840_; size_t v___x_4841_; 
lean_dec_ref_known(v___x_4839_, 1);
v___x_4840_ = ((size_t)1ULL);
v___x_4841_ = lean_usize_add(v_i_4831_, v___x_4840_);
v_i_4831_ = v___x_4841_;
v_b_4832_ = v___x_4836_;
goto _start;
}
else
{
return v___x_4839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4843_, lean_object* v_sz_4844_, lean_object* v_i_4845_, lean_object* v_b_4846_, lean_object* v___y_4847_){
_start:
{
size_t v_sz_boxed_4848_; size_t v_i_boxed_4849_; lean_object* v_res_4850_; 
v_sz_boxed_4848_ = lean_unbox_usize(v_sz_4844_);
lean_dec(v_sz_4844_);
v_i_boxed_4849_ = lean_unbox_usize(v_i_4845_);
lean_dec(v_i_4845_);
v_res_4850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4843_, v_sz_boxed_4848_, v_i_boxed_4849_, v_b_4846_);
lean_dec_ref(v_as_4843_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4851_, size_t v_sz_4852_, size_t v_i_4853_, lean_object* v_bs_4854_){
_start:
{
uint8_t v_anyUnlocated_4855_; 
v_anyUnlocated_4855_ = lean_usize_dec_lt(v_i_4853_, v_sz_4852_);
if (v_anyUnlocated_4855_ == 0)
{
return v_bs_4854_;
}
else
{
lean_object* v___x_4856_; uint8_t v_anyFailed_4857_; lean_object* v_v_4858_; lean_object* v_bs_x27_4859_; lean_object* v___x_4860_; size_t v___x_4861_; size_t v___x_4862_; lean_object* v___x_4863_; 
v___x_4856_ = lean_unsigned_to_nat(0u);
v_anyFailed_4857_ = lean_nat_dec_eq(v___x_4851_, v___x_4856_);
v_v_4858_ = lean_array_uget(v_bs_4854_, v_i_4853_);
v_bs_x27_4859_ = lean_array_uset(v_bs_4854_, v_i_4853_, v___x_4856_);
v___x_4860_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4860_, 0, v_v_4858_);
lean_ctor_set_uint8(v___x_4860_, sizeof(void*)*1, v_anyFailed_4857_);
lean_ctor_set_uint8(v___x_4860_, sizeof(void*)*1 + 1, v_anyUnlocated_4855_);
lean_ctor_set_uint8(v___x_4860_, sizeof(void*)*1 + 2, v_anyFailed_4857_);
v___x_4861_ = ((size_t)1ULL);
v___x_4862_ = lean_usize_add(v_i_4853_, v___x_4861_);
v___x_4863_ = lean_array_uset(v_bs_x27_4859_, v_i_4853_, v___x_4860_);
v_i_4853_ = v___x_4862_;
v_bs_4854_ = v___x_4863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4865_, lean_object* v_sz_4866_, lean_object* v_i_4867_, lean_object* v_bs_4868_){
_start:
{
size_t v_sz_boxed_4869_; size_t v_i_boxed_4870_; lean_object* v_res_4871_; 
v_sz_boxed_4869_ = lean_unbox_usize(v_sz_4866_);
lean_dec(v_sz_4866_);
v_i_boxed_4870_ = lean_unbox_usize(v_i_4867_);
lean_dec(v_i_4867_);
v_res_4871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4865_, v_sz_boxed_4869_, v_i_boxed_4870_, v_bs_4868_);
lean_dec(v___x_4865_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4872_, size_t v_i_4873_, size_t v_stop_4874_, lean_object* v_b_4875_){
_start:
{
uint8_t v___x_4876_; 
v___x_4876_ = lean_usize_dec_eq(v_i_4873_, v_stop_4874_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v_fst_4878_; lean_object* v_snd_4879_; uint8_t v___x_4880_; lean_object* v___x_4881_; size_t v___x_4882_; size_t v___x_4883_; 
v___x_4877_ = lean_array_uget_borrowed(v_as_4872_, v_i_4873_);
v_fst_4878_ = lean_ctor_get(v___x_4877_, 0);
v_snd_4879_ = lean_ctor_get(v___x_4877_, 1);
v___x_4880_ = lean_unbox(v_snd_4879_);
lean_inc(v_fst_4878_);
v___x_4881_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4875_, v_fst_4878_, v___x_4880_);
v___x_4882_ = ((size_t)1ULL);
v___x_4883_ = lean_usize_add(v_i_4873_, v___x_4882_);
v_i_4873_ = v___x_4883_;
v_b_4875_ = v___x_4881_;
goto _start;
}
else
{
return v_b_4875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4885_, lean_object* v_i_4886_, lean_object* v_stop_4887_, lean_object* v_b_4888_){
_start:
{
size_t v_i_boxed_4889_; size_t v_stop_boxed_4890_; lean_object* v_res_4891_; 
v_i_boxed_4889_ = lean_unbox_usize(v_i_4886_);
lean_dec(v_i_4886_);
v_stop_boxed_4890_ = lean_unbox_usize(v_stop_4887_);
lean_dec(v_stop_4887_);
v_res_4891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4885_, v_i_boxed_4889_, v_stop_boxed_4890_, v_b_4888_);
lean_dec_ref(v_as_4885_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4901_, lean_object* v_checkImports_4902_, lean_object* v_args_4903_, lean_object* v___x_4904_, lean_object* v_as_4905_, size_t v_sz_4906_, size_t v_i_4907_, lean_object* v_b_4908_){
_start:
{
lean_object* v_a_4911_; lean_object* v___x_4915_; uint8_t v_anyFailed_4916_; uint8_t v_anyUnlocated_4917_; lean_object* v___x_4918_; lean_object* v_envLinterModule_4919_; uint8_t v___x_4920_; 
v___x_4915_ = lean_unsigned_to_nat(0u);
v_anyFailed_4916_ = lean_nat_dec_eq(v___x_4901_, v___x_4915_);
v_anyUnlocated_4917_ = 1;
v___x_4918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4919_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4919_, 0, v___x_4918_);
lean_ctor_set_uint8(v_envLinterModule_4919_, sizeof(void*)*1, v_anyFailed_4916_);
lean_ctor_set_uint8(v_envLinterModule_4919_, sizeof(void*)*1 + 1, v_anyUnlocated_4917_);
lean_ctor_set_uint8(v_envLinterModule_4919_, sizeof(void*)*1 + 2, v_anyFailed_4916_);
v___x_4920_ = lean_usize_dec_lt(v_i_4907_, v_sz_4906_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; 
lean_dec_ref_known(v_envLinterModule_4919_, 1);
lean_dec(v___x_4904_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_b_4908_);
return v___x_4921_;
}
else
{
lean_object* v_snd_4922_; lean_object* v_snd_4923_; lean_object* v_snd_4924_; lean_object* v_snd_4925_; lean_object* v_fst_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_5239_; 
v_snd_4922_ = lean_ctor_get(v_b_4908_, 1);
lean_inc(v_snd_4922_);
v_snd_4923_ = lean_ctor_get(v_snd_4922_, 1);
lean_inc(v_snd_4923_);
v_snd_4924_ = lean_ctor_get(v_snd_4923_, 1);
lean_inc(v_snd_4924_);
v_snd_4925_ = lean_ctor_get(v_snd_4924_, 1);
lean_inc(v_snd_4925_);
v_fst_4926_ = lean_ctor_get(v_b_4908_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_b_4908_);
if (v_isSharedCheck_5239_ == 0)
{
lean_object* v_unused_5240_; 
v_unused_5240_ = lean_ctor_get(v_b_4908_, 1);
lean_dec(v_unused_5240_);
v___x_4928_ = v_b_4908_;
v_isShared_4929_ = v_isSharedCheck_5239_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_fst_4926_);
lean_dec(v_b_4908_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_5239_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_fst_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_5237_; 
v_fst_4930_ = lean_ctor_get(v_snd_4922_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v_snd_4922_);
if (v_isSharedCheck_5237_ == 0)
{
lean_object* v_unused_5238_; 
v_unused_5238_ = lean_ctor_get(v_snd_4922_, 1);
lean_dec(v_unused_5238_);
v___x_4932_ = v_snd_4922_;
v_isShared_4933_ = v_isSharedCheck_5237_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_fst_4930_);
lean_dec(v_snd_4922_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_5237_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v_fst_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_5235_; 
v_fst_4934_ = lean_ctor_get(v_snd_4923_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v_snd_4923_);
if (v_isSharedCheck_5235_ == 0)
{
lean_object* v_unused_5236_; 
v_unused_5236_ = lean_ctor_get(v_snd_4923_, 1);
lean_dec(v_unused_5236_);
v___x_4936_ = v_snd_4923_;
v_isShared_4937_ = v_isSharedCheck_5235_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_fst_4934_);
lean_dec(v_snd_4923_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_5235_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v_fst_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_5233_; 
v_fst_4938_ = lean_ctor_get(v_snd_4924_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v_snd_4924_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; 
v_unused_5234_ = lean_ctor_get(v_snd_4924_, 1);
lean_dec(v_unused_5234_);
v___x_4940_ = v_snd_4924_;
v_isShared_4941_ = v_isSharedCheck_5233_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_fst_4938_);
lean_dec(v_snd_4924_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_5233_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v_fst_4942_; lean_object* v_snd_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_5232_; 
v_fst_4942_ = lean_ctor_get(v_snd_4925_, 0);
v_snd_4943_ = lean_ctor_get(v_snd_4925_, 1);
v_isSharedCheck_5232_ = !lean_is_exclusive(v_snd_4925_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_4945_ = v_snd_4925_;
v_isShared_4946_ = v_isSharedCheck_5232_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_snd_4943_);
lean_inc(v_fst_4942_);
lean_dec(v_snd_4925_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_5232_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; lean_object* v_a_4948_; lean_object* v___y_4950_; lean_object* v___y_4951_; uint8_t v_anyFailed_4952_; uint8_t v_anyUnlocated_4953_; lean_object* v_records_4954_; lean_object* v_codeQualityEntries_4955_; lean_object* v___y_5102_; lean_object* v___y_5103_; uint8_t v_anyFailed_5104_; uint8_t v_anyUnlocated_5105_; lean_object* v_records_5106_; lean_object* v_codeQualityEntries_5107_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_4947_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_4948_ = lean_array_uget_borrowed(v_as_4905_, v_i_4907_);
v___x_5165_ = lean_enable_initializer_execution();
lean_inc(v_a_4948_);
v___x_5166_ = l_Lean_findOLean(v_a_4948_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v___x_5168_ = l_Lean_readModuleData(v_a_5167_);
lean_dec(v_a_5167_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v_fst_5170_; lean_object* v_snd_5171_; uint8_t v___x_5172_; uint8_t v___y_5174_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
v_fst_5170_ = lean_ctor_get(v_a_5169_, 0);
lean_inc(v_fst_5170_);
v_snd_5171_ = lean_ctor_get(v_a_5169_, 1);
lean_inc(v_snd_5171_);
lean_dec(v_a_5169_);
v___x_5172_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5170_);
lean_dec(v_fst_5170_);
if (v___x_5172_ == 0)
{
uint8_t v___x_5214_; 
v___x_5214_ = 2;
v___y_5174_ = v___x_5214_;
goto v___jp_5173_;
}
else
{
uint8_t v___x_5215_; 
v___x_5215_ = 1;
v___y_5174_ = v___x_5215_;
goto v___jp_5173_;
}
v___jp_5173_:
{
lean_object* v___x_5175_; 
v___x_5175_ = lean_compacted_region_free(v_snd_5171_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint32_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
lean_dec_ref_known(v___x_5175_, 1);
lean_inc(v_a_4948_);
v___x_5176_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5176_, 0, v_a_4948_);
lean_ctor_set_uint8(v___x_5176_, sizeof(void*)*1, v_anyFailed_4916_);
lean_ctor_set_uint8(v___x_5176_, sizeof(void*)*1 + 1, v_anyUnlocated_4917_);
lean_ctor_set_uint8(v___x_5176_, sizeof(void*)*1 + 2, v_anyFailed_4916_);
v___x_5177_ = lean_unsigned_to_nat(2u);
v___x_5178_ = lean_mk_empty_array_with_capacity(v___x_5177_);
v___x_5179_ = lean_array_push(v___x_5178_, v___x_5176_);
v___x_5180_ = lean_array_push(v___x_5179_, v_envLinterModule_4919_);
v___x_5181_ = l_Array_append___redArg(v___x_5180_, v_checkImports_4902_);
v___x_5182_ = l_Lean_Options_empty;
v___x_5183_ = 1024;
v___x_5184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5185_ = lean_box(1);
v___x_5186_ = l_Lean_importModules(v___x_5181_, v___x_5182_, v___x_5183_, v___x_5184_, v_anyFailed_4916_, v_anyUnlocated_4917_, v___y_5174_, v___x_5185_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v_linterOverrides_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5186_, 1);
v_linterOverrides_5188_ = lean_ctor_get(v_args_4903_, 0);
v___x_5189_ = lean_array_get_size(v_linterOverrides_5188_);
v___x_5190_ = lean_nat_dec_lt(v___x_4915_, v___x_5189_);
if (v___x_5190_ == 0)
{
v___y_5125_ = v_a_5187_;
v___y_5126_ = v___x_5182_;
goto v___jp_5124_;
}
else
{
uint8_t v___x_5191_; 
v___x_5191_ = lean_nat_dec_le(v___x_5189_, v___x_5189_);
if (v___x_5191_ == 0)
{
if (v___x_5190_ == 0)
{
v___y_5125_ = v_a_5187_;
v___y_5126_ = v___x_5182_;
goto v___jp_5124_;
}
else
{
size_t v___x_5192_; size_t v___x_5193_; lean_object* v___x_5194_; 
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = lean_usize_of_nat(v___x_5189_);
v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5188_, v___x_5192_, v___x_5193_, v___x_5182_);
v___y_5125_ = v_a_5187_;
v___y_5126_ = v___x_5194_;
goto v___jp_5124_;
}
}
else
{
size_t v___x_5195_; size_t v___x_5196_; lean_object* v___x_5197_; 
v___x_5195_ = ((size_t)0ULL);
v___x_5196_ = lean_usize_of_nat(v___x_5189_);
v___x_5197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5188_, v___x_5195_, v___x_5196_, v___x_5182_);
v___y_5125_ = v_a_5187_;
v___y_5126_ = v___x_5197_;
goto v___jp_5124_;
}
}
}
else
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_dec(v_fst_4938_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4934_);
lean_del_object(v___x_4932_);
lean_dec(v_fst_4930_);
lean_del_object(v___x_4928_);
lean_dec(v_fst_4926_);
lean_dec(v___x_4904_);
v_a_5198_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5186_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5186_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
v___x_5203_ = v___x_5200_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_dec(v_fst_4938_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4934_);
lean_del_object(v___x_4932_);
lean_dec(v_fst_4930_);
lean_del_object(v___x_4928_);
lean_dec(v_fst_4926_);
lean_dec_ref_known(v_envLinterModule_4919_, 1);
lean_dec(v___x_4904_);
v_a_5206_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5175_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5175_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_dec(v_fst_4938_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4934_);
lean_del_object(v___x_4932_);
lean_dec(v_fst_4930_);
lean_del_object(v___x_4928_);
lean_dec(v_fst_4926_);
lean_dec_ref_known(v_envLinterModule_4919_, 1);
lean_dec(v___x_4904_);
v_a_5216_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5168_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5168_);
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
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_dec(v_fst_4938_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4934_);
lean_del_object(v___x_4932_);
lean_dec(v_fst_4930_);
lean_del_object(v___x_4928_);
lean_dec(v_fst_4926_);
lean_dec_ref_known(v_envLinterModule_4919_, 1);
lean_dec(v___x_4904_);
v_a_5224_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_5166_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5166_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
v___jp_4949_:
{
uint8_t v_mode_4956_; uint8_t v___x_4957_; uint8_t v___x_4958_; 
v_mode_4956_ = lean_ctor_get_uint8(v_args_4903_, sizeof(void*)*4 + 1);
v___x_4957_ = 2;
v___x_4958_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4956_, v___x_4957_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4959_ = l_Lean_Name_getRoot(v_a_4948_);
lean_inc(v___x_4904_);
v___x_4960_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4903_, v___y_4951_, v___x_4904_, v___y_4950_, v___x_4959_, v_fst_4942_);
lean_dec_ref(v___y_4951_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v_outcome_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v_outcome_4962_ = lean_ctor_get(v_a_4961_, 0);
if (lean_obj_tag(v_outcome_4962_) == 0)
{
uint8_t v_failed_4963_; 
v_failed_4963_ = lean_ctor_get_uint8(v_outcome_4962_, 0);
if (v_failed_4963_ == 0)
{
lean_object* v_checkedModules_4964_; lean_object* v___x_4966_; 
v_checkedModules_4964_ = lean_ctor_get(v_a_4961_, 1);
lean_inc(v_checkedModules_4964_);
lean_dec(v_a_4961_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v_checkedModules_4964_);
v___x_4966_ = v___x_4945_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_checkedModules_4964_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_snd_4943_);
v___x_4966_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
lean_object* v___x_4968_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_4966_);
lean_ctor_set(v___x_4940_, 0, v_codeQualityEntries_4955_);
v___x_4968_ = v___x_4940_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_codeQualityEntries_4955_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4970_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_4968_);
lean_ctor_set(v___x_4936_, 0, v_records_4954_);
v___x_4970_ = v___x_4936_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_records_4954_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_4970_);
lean_ctor_set(v___x_4932_, 0, v___x_4971_);
v___x_4973_ = v___x_4932_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4978_, 1, v___x_4970_);
v___x_4973_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4974_ = lean_box(v_anyFailed_4952_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 1, v___x_4973_);
lean_ctor_set(v___x_4928_, 0, v___x_4974_);
v___x_4976_ = v___x_4928_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4974_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4973_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
v_a_4911_ = v___x_4976_;
goto v___jp_4910_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4982_; lean_object* v___x_4984_; 
v_checkedModules_4982_ = lean_ctor_get(v_a_4961_, 1);
lean_inc(v_checkedModules_4982_);
lean_dec(v_a_4961_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v_checkedModules_4982_);
v___x_4984_ = v___x_4945_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_checkedModules_4982_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_snd_4943_);
v___x_4984_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4986_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_4984_);
lean_ctor_set(v___x_4940_, 0, v_codeQualityEntries_4955_);
v___x_4986_ = v___x_4940_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_codeQualityEntries_4955_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4988_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_4986_);
lean_ctor_set(v___x_4936_, 0, v_records_4954_);
v___x_4988_ = v___x_4936_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_records_4954_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4989_; lean_object* v___x_4991_; 
v___x_4989_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_4988_);
lean_ctor_set(v___x_4932_, 0, v___x_4989_);
v___x_4991_ = v___x_4932_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4989_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4988_);
v___x_4991_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4992_ = lean_box(v_anyUnlocated_4917_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 1, v___x_4991_);
lean_ctor_set(v___x_4928_, 0, v___x_4992_);
v___x_4994_ = v___x_4928_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4991_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
v_a_4911_ = v___x_4994_;
goto v___jp_4910_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5000_; lean_object* v_records_5001_; uint8_t v_unlocated_5002_; lean_object* v___x_5003_; 
lean_inc_ref(v_outcome_4962_);
v_checkedModules_5000_ = lean_ctor_get(v_a_4961_, 1);
lean_inc(v_checkedModules_5000_);
lean_dec(v_a_4961_);
v_records_5001_ = lean_ctor_get(v_outcome_4962_, 0);
lean_inc_ref(v_records_5001_);
v_unlocated_5002_ = lean_ctor_get_uint8(v_outcome_4962_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4962_, 1);
v___x_5003_ = l_Array_append___redArg(v_records_4954_, v_records_5001_);
lean_dec_ref(v_records_5001_);
if (v_unlocated_5002_ == 0)
{
lean_object* v___x_5005_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v_checkedModules_5000_);
v___x_5005_ = v___x_4945_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_checkedModules_5000_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v_snd_4943_);
v___x_5005_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5007_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_5005_);
lean_ctor_set(v___x_4940_, 0, v_codeQualityEntries_4955_);
v___x_5007_ = v___x_4940_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_codeQualityEntries_4955_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5009_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_5007_);
lean_ctor_set(v___x_4936_, 0, v___x_5003_);
v___x_5009_ = v___x_4936_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_5009_);
lean_ctor_set(v___x_4932_, 0, v___x_5010_);
v___x_5012_ = v___x_4932_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5009_);
v___x_5012_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
v___x_5013_ = lean_box(v_anyFailed_4952_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 1, v___x_5012_);
lean_ctor_set(v___x_4928_, 0, v___x_5013_);
v___x_5015_ = v___x_4928_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___x_5012_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
v_a_4911_ = v___x_5015_;
goto v___jp_4910_;
}
}
}
}
}
}
else
{
lean_object* v___x_5022_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 0, v_checkedModules_5000_);
v___x_5022_ = v___x_4945_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_checkedModules_5000_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v_snd_4943_);
v___x_5022_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
lean_object* v___x_5024_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_5022_);
lean_ctor_set(v___x_4940_, 0, v_codeQualityEntries_4955_);
v___x_5024_ = v___x_4940_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_codeQualityEntries_4955_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5026_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_5024_);
lean_ctor_set(v___x_4936_, 0, v___x_5003_);
v___x_5026_ = v___x_4936_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5024_);
v___x_5026_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
lean_object* v___x_5027_; lean_object* v___x_5029_; 
v___x_5027_ = lean_box(v_anyUnlocated_4917_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_5026_);
lean_ctor_set(v___x_4932_, 0, v___x_5027_);
v___x_5029_ = v___x_4932_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5027_);
lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5026_);
v___x_5029_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5030_ = lean_box(v_anyFailed_4952_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 1, v___x_5029_);
lean_ctor_set(v___x_4928_, 0, v___x_5030_);
v___x_5032_ = v___x_4928_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v___x_5029_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
v_a_4911_ = v___x_5032_;
goto v___jp_4910_;
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
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec_ref(v_codeQualityEntries_4955_);
lean_dec_ref(v_records_4954_);
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_del_object(v___x_4940_);
lean_del_object(v___x_4936_);
lean_del_object(v___x_4932_);
lean_del_object(v___x_4928_);
lean_dec(v___x_4904_);
v_a_5038_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_4960_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_4960_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
lean_object* v___x_5046_; lean_object* v_fst_5047_; lean_object* v_snd_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5100_; 
lean_del_object(v___x_4928_);
v___x_5046_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4903_, v___y_4951_, v___y_4950_, v_a_4948_, v_snd_4943_);
lean_dec_ref(v___y_4951_);
v_fst_5047_ = lean_ctor_get(v___x_5046_, 0);
v_snd_5048_ = lean_ctor_get(v___x_5046_, 1);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5050_ = v___x_5046_;
v_isShared_5051_ = v_isSharedCheck_5100_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_snd_5048_);
lean_inc(v_fst_5047_);
lean_dec(v___x_5046_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5100_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = l_Array_append___redArg(v_codeQualityEntries_4955_, v_fst_5047_);
lean_dec(v_fst_5047_);
lean_inc(v_a_4948_);
lean_inc(v___x_4904_);
v___x_5053_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4904_, v___y_4950_, v_a_4948_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v_entries_5055_; uint8_t v_failed_5056_; lean_object* v___x_5057_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_a_5054_);
lean_dec_ref_known(v___x_5053_, 1);
v_entries_5055_ = lean_ctor_get(v_a_5054_, 0);
lean_inc_ref(v_entries_5055_);
v_failed_5056_ = lean_ctor_get_uint8(v_a_5054_, sizeof(void*)*1);
lean_dec(v_a_5054_);
v___x_5057_ = l_Array_append___redArg(v___x_5052_, v_entries_5055_);
lean_dec_ref(v_entries_5055_);
if (v_failed_5056_ == 0)
{
lean_object* v___x_5059_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v_fst_4942_);
v___x_5059_ = v___x_5050_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_fst_4942_);
lean_ctor_set(v_reuseFailAlloc_5074_, 1, v_snd_5048_);
v___x_5059_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5061_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___x_5059_);
lean_ctor_set(v___x_4945_, 0, v___x_5057_);
v___x_5061_ = v___x_4945_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v___x_5059_);
v___x_5061_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
lean_object* v___x_5063_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_5061_);
lean_ctor_set(v___x_4940_, 0, v_records_4954_);
v___x_5063_ = v___x_4940_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_records_4954_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_5061_);
v___x_5063_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
lean_object* v___x_5064_; lean_object* v___x_5066_; 
v___x_5064_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_5063_);
lean_ctor_set(v___x_4936_, 0, v___x_5064_);
v___x_5066_ = v___x_4936_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5064_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v___x_5063_);
v___x_5066_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = lean_box(v_anyFailed_4952_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_5066_);
lean_ctor_set(v___x_4932_, 0, v___x_5067_);
v___x_5069_ = v___x_4932_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v___x_5066_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
v_a_4911_ = v___x_5069_;
goto v___jp_4910_;
}
}
}
}
}
}
else
{
lean_object* v___x_5076_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v_fst_4942_);
v___x_5076_ = v___x_5050_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_fst_4942_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v_snd_5048_);
v___x_5076_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5078_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___x_5076_);
lean_ctor_set(v___x_4945_, 0, v___x_5057_);
v___x_5078_ = v___x_4945_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v___x_5076_);
v___x_5078_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; 
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 1, v___x_5078_);
lean_ctor_set(v___x_4940_, 0, v_records_4954_);
v___x_5080_ = v___x_4940_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_records_4954_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___x_5081_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 1, v___x_5080_);
lean_ctor_set(v___x_4936_, 0, v___x_5081_);
v___x_5083_ = v___x_4936_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5081_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v___x_5080_);
v___x_5083_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5084_ = lean_box(v_anyUnlocated_4917_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_5083_);
lean_ctor_set(v___x_4932_, 0, v___x_5084_);
v___x_5086_ = v___x_4932_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v___x_5083_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
v_a_4911_ = v___x_5086_;
goto v___jp_4910_;
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
lean_dec_ref(v___x_5052_);
lean_del_object(v___x_5050_);
lean_dec(v_snd_5048_);
lean_dec_ref(v_records_4954_);
lean_del_object(v___x_4945_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_del_object(v___x_4936_);
lean_del_object(v___x_4932_);
lean_dec(v___x_4904_);
v_a_5092_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5053_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5053_);
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
}
}
v___jp_5101_:
{
lean_object* v___x_5108_; 
lean_inc(v_a_4948_);
lean_inc_ref(v___y_5102_);
lean_inc(v___x_4904_);
lean_inc_ref(v___y_5103_);
v___x_5108_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4903_, v___y_5103_, v___x_4904_, v___y_5102_, v_a_4948_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
switch(lean_obj_tag(v_a_5109_))
{
case 0:
{
uint8_t v_failed_5110_; 
v_failed_5110_ = lean_ctor_get_uint8(v_a_5109_, 0);
lean_dec_ref_known(v_a_5109_, 0);
if (v_failed_5110_ == 0)
{
v___y_4950_ = v___y_5102_;
v___y_4951_ = v___y_5103_;
v_anyFailed_4952_ = v_anyFailed_5104_;
v_anyUnlocated_4953_ = v_anyUnlocated_5105_;
v_records_4954_ = v_records_5106_;
v_codeQualityEntries_4955_ = v_codeQualityEntries_5107_;
goto v___jp_4949_;
}
else
{
v___y_4950_ = v___y_5102_;
v___y_4951_ = v___y_5103_;
v_anyFailed_4952_ = v_anyUnlocated_4917_;
v_anyUnlocated_4953_ = v_anyUnlocated_5105_;
v_records_4954_ = v_records_5106_;
v_codeQualityEntries_4955_ = v_codeQualityEntries_5107_;
goto v___jp_4949_;
}
}
case 1:
{
lean_object* v_records_5111_; uint8_t v_unlocated_5112_; lean_object* v___x_5113_; 
v_records_5111_ = lean_ctor_get(v_a_5109_, 0);
lean_inc_ref(v_records_5111_);
v_unlocated_5112_ = lean_ctor_get_uint8(v_a_5109_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5109_, 1);
v___x_5113_ = l_Array_append___redArg(v_records_5106_, v_records_5111_);
lean_dec_ref(v_records_5111_);
if (v_unlocated_5112_ == 0)
{
v___y_4950_ = v___y_5102_;
v___y_4951_ = v___y_5103_;
v_anyFailed_4952_ = v_anyFailed_5104_;
v_anyUnlocated_4953_ = v_anyUnlocated_5105_;
v_records_4954_ = v___x_5113_;
v_codeQualityEntries_4955_ = v_codeQualityEntries_5107_;
goto v___jp_4949_;
}
else
{
v___y_4950_ = v___y_5102_;
v___y_4951_ = v___y_5103_;
v_anyFailed_4952_ = v_anyFailed_5104_;
v_anyUnlocated_4953_ = v_anyUnlocated_4917_;
v_records_4954_ = v___x_5113_;
v_codeQualityEntries_4955_ = v_codeQualityEntries_5107_;
goto v___jp_4949_;
}
}
default: 
{
lean_object* v_entries_5114_; lean_object* v___x_5115_; 
v_entries_5114_ = lean_ctor_get(v_a_5109_, 0);
lean_inc_ref(v_entries_5114_);
lean_dec_ref_known(v_a_5109_, 1);
v___x_5115_ = l_Array_append___redArg(v_codeQualityEntries_5107_, v_entries_5114_);
lean_dec_ref(v_entries_5114_);
v___y_4950_ = v___y_5102_;
v___y_4951_ = v___y_5103_;
v_anyFailed_4952_ = v_anyFailed_5104_;
v_anyUnlocated_4953_ = v_anyUnlocated_5105_;
v_records_4954_ = v_records_5106_;
v_codeQualityEntries_4955_ = v___x_5115_;
goto v___jp_4949_;
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec_ref(v_codeQualityEntries_5107_);
lean_dec_ref(v_records_5106_);
lean_dec_ref(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_del_object(v___x_4936_);
lean_del_object(v___x_4932_);
lean_del_object(v___x_4928_);
lean_dec(v___x_4904_);
v_a_5116_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5108_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5108_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
v___jp_5124_:
{
lean_object* v___x_5127_; lean_object* v_toEnvExtension_5128_; lean_object* v_asyncMode_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v_merged_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5163_; 
v___x_5127_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5128_ = lean_ctor_get(v___x_5127_, 0);
v_asyncMode_5129_ = lean_ctor_get(v_toEnvExtension_5128_, 2);
v___x_5130_ = lean_box(0);
lean_inc_ref(v___y_5125_);
v___x_5131_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4947_, v___x_5127_, v___y_5125_, v_asyncMode_5129_, v___x_5130_);
v_merged_5132_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5163_ == 0)
{
lean_object* v_unused_5164_; 
v_unused_5164_ = lean_ctor_get(v___x_5131_, 1);
lean_dec(v_unused_5164_);
v___x_5134_ = v___x_5131_;
v_isShared_5135_ = v_isSharedCheck_5163_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_merged_5132_);
lean_dec(v___x_5131_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5163_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 1, v_merged_5132_);
lean_ctor_set(v___x_5134_, 0, v___y_5126_);
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___y_5126_);
lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_merged_5132_);
v___x_5137_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5138_; 
v___x_5138_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4903_, v___x_5137_, v___y_5125_, v_a_4948_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5138_, 1);
switch(lean_obj_tag(v_a_5139_))
{
case 0:
{
uint8_t v___x_5140_; 
v___x_5140_ = lean_unbox(v_fst_4926_);
lean_dec(v_fst_4926_);
if (v___x_5140_ == 0)
{
uint8_t v_failed_5141_; uint8_t v___x_5142_; 
v_failed_5141_ = lean_ctor_get_uint8(v_a_5139_, 0);
lean_dec_ref_known(v_a_5139_, 0);
v___x_5142_ = lean_unbox(v_fst_4930_);
lean_dec(v_fst_4930_);
v___y_5102_ = v___y_5125_;
v___y_5103_ = v___x_5137_;
v_anyFailed_5104_ = v_failed_5141_;
v_anyUnlocated_5105_ = v___x_5142_;
v_records_5106_ = v_fst_4934_;
v_codeQualityEntries_5107_ = v_fst_4938_;
goto v___jp_5101_;
}
else
{
uint8_t v___x_5143_; 
lean_dec_ref_known(v_a_5139_, 0);
v___x_5143_ = lean_unbox(v_fst_4930_);
lean_dec(v_fst_4930_);
v___y_5102_ = v___y_5125_;
v___y_5103_ = v___x_5137_;
v_anyFailed_5104_ = v_anyUnlocated_4917_;
v_anyUnlocated_5105_ = v___x_5143_;
v_records_5106_ = v_fst_4934_;
v_codeQualityEntries_5107_ = v_fst_4938_;
goto v___jp_5101_;
}
}
case 1:
{
lean_object* v_records_5144_; uint8_t v_unlocated_5145_; lean_object* v___x_5146_; 
v_records_5144_ = lean_ctor_get(v_a_5139_, 0);
lean_inc_ref(v_records_5144_);
v_unlocated_5145_ = lean_ctor_get_uint8(v_a_5139_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5139_, 1);
v___x_5146_ = l_Array_append___redArg(v_fst_4934_, v_records_5144_);
lean_dec_ref(v_records_5144_);
if (v_unlocated_5145_ == 0)
{
uint8_t v___x_5147_; uint8_t v___x_5148_; 
v___x_5147_ = lean_unbox(v_fst_4926_);
lean_dec(v_fst_4926_);
v___x_5148_ = lean_unbox(v_fst_4930_);
lean_dec(v_fst_4930_);
v___y_5102_ = v___y_5125_;
v___y_5103_ = v___x_5137_;
v_anyFailed_5104_ = v___x_5147_;
v_anyUnlocated_5105_ = v___x_5148_;
v_records_5106_ = v___x_5146_;
v_codeQualityEntries_5107_ = v_fst_4938_;
goto v___jp_5101_;
}
else
{
uint8_t v___x_5149_; 
lean_dec(v_fst_4930_);
v___x_5149_ = lean_unbox(v_fst_4926_);
lean_dec(v_fst_4926_);
v___y_5102_ = v___y_5125_;
v___y_5103_ = v___x_5137_;
v_anyFailed_5104_ = v___x_5149_;
v_anyUnlocated_5105_ = v_anyUnlocated_4917_;
v_records_5106_ = v___x_5146_;
v_codeQualityEntries_5107_ = v_fst_4938_;
goto v___jp_5101_;
}
}
default: 
{
lean_object* v_entries_5150_; lean_object* v___x_5151_; uint8_t v___x_5152_; uint8_t v___x_5153_; 
v_entries_5150_ = lean_ctor_get(v_a_5139_, 0);
lean_inc_ref(v_entries_5150_);
lean_dec_ref_known(v_a_5139_, 1);
v___x_5151_ = l_Array_append___redArg(v_fst_4938_, v_entries_5150_);
lean_dec_ref(v_entries_5150_);
v___x_5152_ = lean_unbox(v_fst_4926_);
lean_dec(v_fst_4926_);
v___x_5153_ = lean_unbox(v_fst_4930_);
lean_dec(v_fst_4930_);
v___y_5102_ = v___y_5125_;
v___y_5103_ = v___x_5137_;
v_anyFailed_5104_ = v___x_5152_;
v_anyUnlocated_5105_ = v___x_5153_;
v_records_5106_ = v_fst_4934_;
v_codeQualityEntries_5107_ = v___x_5151_;
goto v___jp_5101_;
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v___x_5137_);
lean_dec_ref(v___y_5125_);
lean_del_object(v___x_4945_);
lean_dec(v_snd_4943_);
lean_dec(v_fst_4942_);
lean_del_object(v___x_4940_);
lean_dec(v_fst_4938_);
lean_del_object(v___x_4936_);
lean_dec(v_fst_4934_);
lean_del_object(v___x_4932_);
lean_dec(v_fst_4930_);
lean_del_object(v___x_4928_);
lean_dec(v_fst_4926_);
lean_dec(v___x_4904_);
v_a_5154_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5138_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5138_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
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
}
}
v___jp_4910_:
{
size_t v___x_4912_; size_t v___x_4913_; 
v___x_4912_ = ((size_t)1ULL);
v___x_4913_ = lean_usize_add(v_i_4907_, v___x_4912_);
v_i_4907_ = v___x_4913_;
v_b_4908_ = v_a_4911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5241_, lean_object* v_checkImports_5242_, lean_object* v_args_5243_, lean_object* v___x_5244_, lean_object* v_as_5245_, lean_object* v_sz_5246_, lean_object* v_i_5247_, lean_object* v_b_5248_, lean_object* v___y_5249_){
_start:
{
size_t v_sz_boxed_5250_; size_t v_i_boxed_5251_; lean_object* v_res_5252_; 
v_sz_boxed_5250_ = lean_unbox_usize(v_sz_5246_);
lean_dec(v_sz_5246_);
v_i_boxed_5251_ = lean_unbox_usize(v_i_5247_);
lean_dec(v_i_5247_);
v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5241_, v_checkImports_5242_, v_args_5243_, v___x_5244_, v_as_5245_, v_sz_boxed_5250_, v_i_boxed_5251_, v_b_5248_);
lean_dec_ref(v_as_5245_);
lean_dec_ref(v_args_5243_);
lean_dec_ref(v_checkImports_5242_);
lean_dec(v___x_5241_);
return v_res_5252_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5253_ = l_Lean_NameSet_empty;
v___x_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___x_5253_);
lean_ctor_set(v___x_5254_, 1, v___x_5253_);
return v___x_5254_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5255_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5256_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5257_, 0, v___x_5256_);
lean_ctor_set(v___x_5257_, 1, v___x_5255_);
return v___x_5257_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5258_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5259_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
lean_ctor_set(v___x_5260_, 1, v___x_5258_);
return v___x_5260_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5262_; lean_object* v___x_5263_; 
v___x_5262_ = 0;
v___x_5263_ = lean_box_uint32(v___x_5262_);
return v___x_5263_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5264_; lean_object* v___x_5265_; 
v___x_5264_ = 1;
v___x_5265_ = lean_box_uint32(v___x_5264_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5266_){
_start:
{
lean_object* v_mods_5268_; uint8_t v_mode_5269_; lean_object* v_checks_5270_; lean_object* v_srcSearchPath_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; uint8_t v_anyFailed_5274_; 
v_mods_5268_ = lean_ctor_get(v_args_5266_, 1);
lean_inc_ref(v_mods_5268_);
v_mode_5269_ = lean_ctor_get_uint8(v_args_5266_, sizeof(void*)*4 + 1);
v_checks_5270_ = lean_ctor_get(v_args_5266_, 2);
v_srcSearchPath_5271_ = lean_ctor_get(v_args_5266_, 3);
v___x_5272_ = lean_array_get_size(v_mods_5268_);
v___x_5273_ = lean_unsigned_to_nat(0u);
v_anyFailed_5274_ = lean_nat_dec_eq(v___x_5272_, v___x_5273_);
if (v_anyFailed_5274_ == 0)
{
size_t v_sz_5275_; size_t v___x_5276_; lean_object* v_checkImports_5277_; lean_object* v___x_5278_; 
v_sz_5275_ = lean_array_size(v_checks_5270_);
v___x_5276_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5270_);
v_checkImports_5277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5272_, v_sz_5275_, v___x_5276_, v_checks_5270_);
v___x_5278_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; size_t v_sz_5286_; lean_object* v___x_5287_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc(v_a_5279_);
lean_dec_ref_known(v___x_5278_, 1);
lean_inc(v_srcSearchPath_5271_);
v___x_5280_ = l_List_appendTR___redArg(v_srcSearchPath_5271_, v_a_5279_);
v___x_5281_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5282_ = lean_box(v_anyFailed_5274_);
v___x_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
lean_ctor_set(v___x_5283_, 1, v___x_5281_);
v___x_5284_ = lean_box(v_anyFailed_5274_);
v___x_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5285_, 0, v___x_5284_);
lean_ctor_set(v___x_5285_, 1, v___x_5283_);
v_sz_5286_ = lean_array_size(v_mods_5268_);
v___x_5287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5272_, v_checkImports_5277_, v_args_5266_, v___x_5280_, v_mods_5268_, v_sz_5286_, v___x_5276_, v___x_5285_);
lean_dec_ref(v_mods_5268_);
lean_dec_ref(v_args_5266_);
lean_dec_ref(v_checkImports_5277_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5359_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5359_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5359_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
switch(v_mode_5269_)
{
case 0:
{
lean_object* v_fst_5292_; uint8_t v___x_5293_; 
v_fst_5292_ = lean_ctor_get(v_a_5288_, 0);
lean_inc(v_fst_5292_);
lean_dec(v_a_5288_);
v___x_5293_ = lean_unbox(v_fst_5292_);
lean_dec(v_fst_5292_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; lean_object* v___x_5296_; 
v___x_5294_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5294_);
v___x_5296_ = v___x_5290_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5300_; 
v___x_5298_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5298_);
v___x_5300_ = v___x_5290_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
case 1:
{
lean_object* v_snd_5302_; lean_object* v_snd_5303_; lean_object* v_fst_5304_; lean_object* v_fst_5305_; lean_object* v___x_5306_; 
v_snd_5302_ = lean_ctor_get(v_a_5288_, 1);
lean_inc(v_snd_5302_);
lean_del_object(v___x_5290_);
lean_dec(v_a_5288_);
v_snd_5303_ = lean_ctor_get(v_snd_5302_, 1);
lean_inc(v_snd_5303_);
v_fst_5304_ = lean_ctor_get(v_snd_5302_, 0);
lean_inc(v_fst_5304_);
lean_dec(v_snd_5302_);
v_fst_5305_ = lean_ctor_get(v_snd_5303_, 0);
lean_inc(v_fst_5305_);
lean_dec(v_snd_5303_);
v___x_5306_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5305_);
lean_dec(v_fst_5305_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5319_; 
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5306_, 0);
lean_dec(v_unused_5320_);
v___x_5308_ = v___x_5306_;
v_isShared_5309_ = v_isSharedCheck_5319_;
goto v_resetjp_5307_;
}
else
{
lean_dec(v___x_5306_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5319_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_unbox(v_fst_5304_);
lean_dec(v_fst_5304_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; lean_object* v___x_5313_; 
v___x_5311_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5311_);
v___x_5313_ = v___x_5308_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
else
{
lean_object* v___x_5315_; lean_object* v___x_5317_; 
v___x_5315_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5315_);
v___x_5317_ = v___x_5308_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec(v_fst_5304_);
v_a_5321_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5306_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5306_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
default: 
{
lean_object* v_snd_5329_; lean_object* v_snd_5330_; lean_object* v_snd_5331_; lean_object* v_fst_5332_; lean_object* v_fst_5333_; lean_object* v___x_5334_; size_t v_sz_5335_; lean_object* v___x_5336_; 
v_snd_5329_ = lean_ctor_get(v_a_5288_, 1);
lean_del_object(v___x_5290_);
v_snd_5330_ = lean_ctor_get(v_snd_5329_, 1);
v_snd_5331_ = lean_ctor_get(v_snd_5330_, 1);
lean_inc(v_snd_5331_);
v_fst_5332_ = lean_ctor_get(v_a_5288_, 0);
lean_inc(v_fst_5332_);
lean_dec(v_a_5288_);
v_fst_5333_ = lean_ctor_get(v_snd_5331_, 0);
lean_inc(v_fst_5333_);
lean_dec(v_snd_5331_);
v___x_5334_ = lean_box(0);
v_sz_5335_ = lean_array_size(v_fst_5333_);
v___x_5336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5333_, v_sz_5335_, v___x_5276_, v___x_5334_);
lean_dec(v_fst_5333_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5349_; 
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5349_ == 0)
{
lean_object* v_unused_5350_; 
v_unused_5350_ = lean_ctor_get(v___x_5336_, 0);
lean_dec(v_unused_5350_);
v___x_5338_ = v___x_5336_;
v_isShared_5339_ = v_isSharedCheck_5349_;
goto v_resetjp_5337_;
}
else
{
lean_dec(v___x_5336_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5349_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
uint8_t v___x_5340_; 
v___x_5340_ = lean_unbox(v_fst_5332_);
lean_dec(v_fst_5332_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5343_; 
v___x_5341_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5341_);
v___x_5343_ = v___x_5338_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5341_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
else
{
lean_object* v___x_5345_; lean_object* v___x_5347_; 
v___x_5345_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5345_);
v___x_5347_ = v___x_5338_;
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
}
}
else
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_dec(v_fst_5332_);
v_a_5351_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5336_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5336_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
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
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
v_a_5360_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5287_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5287_);
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
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec_ref(v_checkImports_5277_);
lean_dec_ref(v_mods_5268_);
lean_dec_ref(v_args_5266_);
v_a_5368_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5278_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5278_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
else
{
lean_object* v___x_5376_; lean_object* v___x_5377_; 
lean_dec_ref(v_mods_5268_);
lean_dec_ref(v_args_5266_);
v___x_5376_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5377_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5376_);
if (lean_obj_tag(v___x_5377_) == 0)
{
lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5385_; 
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5385_ == 0)
{
lean_object* v_unused_5386_; 
v_unused_5386_ = lean_ctor_get(v___x_5377_, 0);
lean_dec(v_unused_5386_);
v___x_5379_ = v___x_5377_;
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
else
{
lean_dec(v___x_5377_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5385_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5381_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 0, v___x_5381_);
v___x_5383_ = v___x_5379_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___x_5381_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
v_a_5387_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5377_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5377_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lake_BuiltinLint_run(v_args_5395_);
return v_res_5397_;
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
