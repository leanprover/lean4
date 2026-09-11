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
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_nbuckets_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_774_ = lean_array_get_size(v_data_773_);
v___x_775_ = lean_unsigned_to_nat(2u);
v_nbuckets_776_ = lean_nat_mul(v___x_774_, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_box(0);
v___x_779_ = lean_mk_array(v_nbuckets_776_, v___x_778_);
v___x_780_ = lean_array_propagate_mark(v_data_773_, v___x_779_);
v___x_781_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_777_, v_data_773_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 0;
return v___x_784_;
}
else
{
lean_object* v_key_785_; lean_object* v_tail_786_; uint8_t v___x_787_; 
v_key_785_ = lean_ctor_get(v_x_783_, 0);
v_tail_786_ = lean_ctor_get(v_x_783_, 2);
v___x_787_ = lean_nat_dec_eq(v_key_785_, v_a_782_);
if (v___x_787_ == 0)
{
v_x_783_ = v_tail_786_;
goto _start;
}
else
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec(v_a_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_793_, lean_object* v_b_794_, lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
lean_dec(v_b_794_);
lean_dec(v_a_793_);
return v_x_795_;
}
else
{
lean_object* v_key_796_; lean_object* v_value_797_; lean_object* v_tail_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_key_796_ = lean_ctor_get(v_x_795_, 0);
v_value_797_ = lean_ctor_get(v_x_795_, 1);
v_tail_798_ = lean_ctor_get(v_x_795_, 2);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_810_ == 0)
{
v___x_800_ = v_x_795_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_tail_798_);
lean_inc(v_value_797_);
lean_inc(v_key_796_);
lean_dec(v_x_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_nat_dec_eq(v_key_796_, v_a_793_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_793_, v_b_794_, v_tail_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 2, v___x_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_key_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_value_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v_value_797_);
lean_dec(v_key_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_b_794_);
lean_ctor_set(v___x_800_, 0, v_a_793_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_793_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_b_794_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_tail_798_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_811_, lean_object* v_a_812_, lean_object* v_b_813_){
_start:
{
lean_object* v_size_814_; lean_object* v_buckets_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_858_; 
v_size_814_ = lean_ctor_get(v_m_811_, 0);
v_buckets_815_ = lean_ctor_get(v_m_811_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_m_811_);
if (v_isSharedCheck_858_ == 0)
{
v___x_817_ = v_m_811_;
v_isShared_818_ = v_isSharedCheck_858_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_buckets_815_);
lean_inc(v_size_814_);
lean_dec(v_m_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_858_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v_fold_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; lean_object* v_bkt_832_; uint8_t v___x_833_; 
v___x_819_ = lean_array_get_size(v_buckets_815_);
v___x_820_ = lean_uint64_of_nat(v_a_812_);
v___x_821_ = 32ULL;
v___x_822_ = lean_uint64_shift_right(v___x_820_, v___x_821_);
v_fold_823_ = lean_uint64_xor(v___x_820_, v___x_822_);
v___x_824_ = 16ULL;
v___x_825_ = lean_uint64_shift_right(v_fold_823_, v___x_824_);
v___x_826_ = lean_uint64_xor(v_fold_823_, v___x_825_);
v___x_827_ = lean_uint64_to_usize(v___x_826_);
v___x_828_ = lean_usize_of_nat(v___x_819_);
v___x_829_ = ((size_t)1ULL);
v___x_830_ = lean_usize_sub(v___x_828_, v___x_829_);
v___x_831_ = lean_usize_land(v___x_827_, v___x_830_);
v_bkt_832_ = lean_array_uget_borrowed(v_buckets_815_, v___x_831_);
v___x_833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_812_, v_bkt_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v_size_x27_835_; lean_object* v___x_836_; lean_object* v_buckets_x27_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v_size_x27_835_ = lean_nat_add(v_size_814_, v___x_834_);
lean_dec(v_size_814_);
lean_inc(v_bkt_832_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v_a_812_);
lean_ctor_set(v___x_836_, 1, v_b_813_);
lean_ctor_set(v___x_836_, 2, v_bkt_832_);
v_buckets_x27_837_ = lean_array_uset(v_buckets_815_, v___x_831_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(4u);
v___x_839_ = lean_nat_mul(v_size_x27_835_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(3u);
v___x_841_ = lean_nat_div(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_array_get_size(v_buckets_x27_837_);
v___x_843_ = lean_nat_dec_le(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v_val_844_; lean_object* v___x_846_; 
v_val_844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_837_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_val_844_);
lean_ctor_set(v___x_817_, 0, v_size_x27_835_);
v___x_846_ = v___x_817_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_val_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_buckets_x27_837_);
lean_ctor_set(v___x_817_, 0, v_size_x27_835_);
v___x_849_ = v___x_817_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_buckets_x27_837_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v___x_851_; lean_object* v_buckets_x27_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_inc(v_bkt_832_);
v___x_851_ = lean_box(0);
v_buckets_x27_852_ = lean_array_uset(v_buckets_815_, v___x_831_, v___x_851_);
v___x_853_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_812_, v_b_813_, v_bkt_832_);
v___x_854_ = lean_array_uset(v_buckets_x27_852_, v___x_831_, v___x_853_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_854_);
v___x_856_ = v___x_817_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_size_814_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_859_, lean_object* v_as_860_, size_t v_i_861_, size_t v_stop_862_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_eq(v_i_861_, v_stop_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = lean_array_uget_borrowed(v_as_860_, v_i_861_);
v___x_865_ = lean_name_eq(v_a_859_, v___x_864_);
if (v___x_865_ == 0)
{
size_t v___x_866_; size_t v___x_867_; 
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_861_, v___x_866_);
v_i_861_ = v___x_867_;
goto _start;
}
else
{
return v___x_865_;
}
}
else
{
uint8_t v___x_869_; 
v___x_869_ = 0;
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_870_, lean_object* v_as_871_, lean_object* v_i_872_, lean_object* v_stop_873_){
_start:
{
size_t v_i_boxed_874_; size_t v_stop_boxed_875_; uint8_t v_res_876_; lean_object* v_r_877_; 
v_i_boxed_874_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_stop_boxed_875_ = lean_unbox_usize(v_stop_873_);
lean_dec(v_stop_873_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_870_, v_as_871_, v_i_boxed_874_, v_stop_boxed_875_);
lean_dec_ref(v_as_871_);
lean_dec(v_a_870_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_array_get_size(v_as_878_);
v___x_882_ = lean_nat_dec_lt(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
return v___x_882_;
}
else
{
if (v___x_882_ == 0)
{
return v___x_882_;
}
else
{
size_t v___x_883_; size_t v___x_884_; uint8_t v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_881_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_879_, v_as_878_, v___x_883_, v___x_884_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_886_, lean_object* v_a_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_as_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_890_, lean_object* v_fallback_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_inc(v_fallback_891_);
return v_fallback_891_;
}
else
{
lean_object* v_key_893_; lean_object* v_value_894_; lean_object* v_tail_895_; uint8_t v___x_896_; 
v_key_893_ = lean_ctor_get(v_x_892_, 0);
v_value_894_ = lean_ctor_get(v_x_892_, 1);
v_tail_895_ = lean_ctor_get(v_x_892_, 2);
v___x_896_ = lean_nat_dec_eq(v_key_893_, v_a_890_);
if (v___x_896_ == 0)
{
v_x_892_ = v_tail_895_;
goto _start;
}
else
{
lean_inc(v_value_894_);
return v_value_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_898_, lean_object* v_fallback_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_898_, v_fallback_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_fallback_899_);
lean_dec(v_a_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_902_, lean_object* v_a_903_, lean_object* v_fallback_904_){
_start:
{
lean_object* v_buckets_905_; lean_object* v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_fold_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_buckets_905_ = lean_ctor_get(v_m_902_, 1);
v___x_906_ = lean_array_get_size(v_buckets_905_);
v___x_907_ = lean_uint64_of_nat(v_a_903_);
v___x_908_ = 32ULL;
v___x_909_ = lean_uint64_shift_right(v___x_907_, v___x_908_);
v_fold_910_ = lean_uint64_xor(v___x_907_, v___x_909_);
v___x_911_ = 16ULL;
v___x_912_ = lean_uint64_shift_right(v_fold_910_, v___x_911_);
v___x_913_ = lean_uint64_xor(v_fold_910_, v___x_912_);
v___x_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = lean_usize_of_nat(v___x_906_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_sub(v___x_915_, v___x_916_);
v___x_918_ = lean_usize_land(v___x_914_, v___x_917_);
v___x_919_ = lean_array_uget_borrowed(v_buckets_905_, v___x_918_);
v___x_920_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_903_, v_fallback_904_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_921_, lean_object* v_a_922_, lean_object* v_fallback_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_921_, v_a_922_, v_fallback_923_);
lean_dec(v_fallback_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_m_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_){
_start:
{
lean_object* v_a_933_; uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_b_930_);
return v___x_938_;
}
else
{
lean_object* v_a_939_; lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_a_939_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
v_fst_940_ = lean_ctor_get(v_a_939_, 0);
v_snd_941_ = lean_ctor_get(v_a_939_, 1);
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_930_, v_fst_940_, v___x_942_);
v___x_944_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_943_, v_snd_941_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_inc(v_snd_941_);
v___x_945_ = lean_array_push(v___x_943_, v_snd_941_);
lean_inc(v_fst_940_);
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_930_, v_fst_940_, v___x_945_);
v_a_933_ = v___x_946_;
goto v___jp_932_;
}
else
{
lean_dec(v___x_943_);
v_a_933_ = v_b_930_;
goto v___jp_932_;
}
}
v___jp_932_:
{
size_t v___x_934_; size_t v___x_935_; 
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_929_, v___x_934_);
v_i_929_ = v___x_935_;
v_b_930_ = v_a_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_){
_start:
{
size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v_sz_boxed_952_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_953_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_947_, v_sz_boxed_952_, v_i_boxed_953_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_putStr_958_; lean_object* v___x_959_; 
v___x_957_ = lean_get_stdout();
v_putStr_958_ = lean_ctor_get(v___x_957_, 4);
lean_inc_ref(v_putStr_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = lean_apply_2(v_putStr_958_, v_s_955_, lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_963_){
_start:
{
uint32_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = 10;
v___x_966_ = lean_string_push(v_s_963_, v___x_965_);
v___x_967_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_968_);
return v_res_970_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_971_, lean_object* v_a_972_, lean_object* v_b_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_972_, v___x_971_);
v___x_975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_973_, v___x_971_);
v___x_976_ = lean_string_dec_lt(v___x_974_, v___x_975_);
lean_dec_ref(v___x_975_);
lean_dec_ref(v___x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
uint8_t v___x_11503__boxed_980_; uint8_t v_res_981_; lean_object* v_r_982_; 
v___x_11503__boxed_980_ = lean_unbox(v___x_977_);
v_res_981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11503__boxed_980_, v_a_978_, v_b_979_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v_hi_985_, lean_object* v_pivot_986_, lean_object* v_as_987_, lean_object* v_i_988_, lean_object* v_k_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_lt(v_k_989_, v_hi_985_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v_k_989_);
lean_dec(v_pivot_986_);
v___x_991_ = lean_array_fswap(v_as_987_, v_i_988_, v_hi_985_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_i_988_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
else
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_993_ = lean_nat_dec_lt(v___x_983_, v___x_984_);
v___x_994_ = lean_array_fget_borrowed(v_as_987_, v_k_989_);
lean_inc(v___x_994_);
v___x_995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_994_, v___x_993_);
lean_inc(v_pivot_986_);
v___x_996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_986_, v___x_993_);
v___x_997_ = lean_string_dec_lt(v___x_995_, v___x_996_);
lean_dec_ref(v___x_996_);
lean_dec_ref(v___x_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_add(v_k_989_, v___x_998_);
lean_dec(v_k_989_);
v_k_989_ = v___x_999_;
goto _start;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = lean_array_fswap(v_as_987_, v_i_988_, v_k_989_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_988_, v___x_1002_);
lean_dec(v_i_988_);
v___x_1004_ = lean_nat_add(v_k_989_, v___x_1002_);
lean_dec(v_k_989_);
v_as_987_ = v___x_1001_;
v_i_988_ = v___x_1003_;
v_k_989_ = v___x_1004_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_hi_1008_, lean_object* v_pivot_1009_, lean_object* v_as_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1006_, v___x_1007_, v_hi_1008_, v_pivot_1009_, v_as_1010_, v_i_1011_, v_k_1012_);
lean_dec(v_hi_1008_);
lean_dec(v___x_1007_);
lean_dec(v___x_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_n_1016_, lean_object* v_as_1017_, lean_object* v_lo_1018_, lean_object* v_hi_1019_){
_start:
{
lean_object* v___y_1021_; uint8_t v___x_1031_; 
v___x_1031_ = lean_nat_dec_lt(v_lo_1018_, v_hi_1019_);
if (v___x_1031_ == 0)
{
lean_dec(v_lo_1018_);
return v_as_1017_;
}
else
{
uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_mid_1035_; lean_object* v___y_1037_; lean_object* v___y_1043_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1032_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
v___x_1033_ = lean_nat_add(v_lo_1018_, v_hi_1019_);
v___x_1034_ = lean_unsigned_to_nat(1u);
v_mid_1035_ = lean_nat_shiftr(v___x_1033_, v___x_1034_);
lean_dec(v___x_1033_);
v___x_1048_ = lean_array_fget_borrowed(v_as_1017_, v_mid_1035_);
v___x_1049_ = lean_array_fget_borrowed(v_as_1017_, v_lo_1018_);
lean_inc(v___x_1049_);
lean_inc(v___x_1048_);
v___x_1050_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1032_, v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
v___y_1043_ = v_as_1017_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_array_fswap(v_as_1017_, v_lo_1018_, v_mid_1035_);
v___y_1043_ = v___x_1051_;
goto v___jp_1042_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_array_fget_borrowed(v___y_1037_, v_mid_1035_);
v___x_1039_ = lean_array_fget_borrowed(v___y_1037_, v_hi_1019_);
lean_inc(v___x_1039_);
lean_inc(v___x_1038_);
v___x_1040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1032_, v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec(v_mid_1035_);
v___y_1021_ = v___y_1037_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_array_fswap(v___y_1037_, v_mid_1035_, v_hi_1019_);
lean_dec(v_mid_1035_);
v___y_1021_ = v___x_1041_;
goto v___jp_1020_;
}
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_array_fget_borrowed(v___y_1043_, v_hi_1019_);
v___x_1045_ = lean_array_fget_borrowed(v___y_1043_, v_lo_1018_);
lean_inc(v___x_1045_);
lean_inc(v___x_1044_);
v___x_1046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1032_, v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
v___y_1037_ = v___y_1043_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_array_fswap(v___y_1043_, v_lo_1018_, v_hi_1019_);
v___y_1037_ = v___x_1047_;
goto v___jp_1036_;
}
}
}
v___jp_1020_:
{
lean_object* v_pivot_1022_; lean_object* v___x_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; uint8_t v___x_1026_; 
v_pivot_1022_ = lean_array_fget(v___y_1021_, v_hi_1019_);
lean_inc_n(v_lo_1018_, 2);
v___x_1023_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1014_, v___x_1015_, v_hi_1019_, v_pivot_1022_, v___y_1021_, v_lo_1018_, v_lo_1018_);
v_fst_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v___x_1023_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v___x_1023_);
v___x_1026_ = lean_nat_dec_le(v_hi_1019_, v_fst_1024_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1014_, v___x_1015_, v_n_1016_, v_snd_1025_, v_lo_1018_, v_fst_1024_);
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = lean_nat_add(v_fst_1024_, v___x_1028_);
lean_dec(v_fst_1024_);
v_as_1017_ = v___x_1027_;
v_lo_1018_ = v___x_1029_;
goto _start;
}
else
{
lean_dec(v_fst_1024_);
lean_dec(v_lo_1018_);
return v_snd_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v_n_1054_, lean_object* v_as_1055_, lean_object* v_lo_1056_, lean_object* v_hi_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1052_, v___x_1053_, v_n_1054_, v_as_1055_, v_lo_1056_, v_hi_1057_);
lean_dec(v_hi_1057_);
lean_dec(v_n_1054_);
lean_dec(v___x_1053_);
lean_dec(v___x_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_bs_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v___x_1061_);
return v_bs_1066_;
}
else
{
uint8_t v___x_1068_; lean_object* v_v_1069_; lean_object* v___x_1070_; lean_object* v_bs_x27_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1068_ = lean_nat_dec_lt(v___x_1062_, v___x_1063_);
v_v_1069_ = lean_array_uget(v_bs_1066_, v_i_1065_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v_bs_x27_1071_ = lean_array_uset(v_bs_1066_, v_i_1065_, v___x_1070_);
v___x_1072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1061_);
v___x_1073_ = lean_string_append(v___x_1061_, v___x_1072_);
v___x_1074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1069_, v___x_1068_);
v___x_1075_ = lean_string_append(v___x_1073_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
v___x_1078_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1079_ = lean_string_append(v___x_1077_, v___x_1078_);
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_add(v_i_1065_, v___x_1080_);
v___x_1082_ = lean_array_uset(v_bs_x27_1071_, v_i_1065_, v___x_1079_);
v_i_1065_ = v___x_1081_;
v_bs_1066_ = v___x_1082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_bs_1089_){
_start:
{
size_t v_sz_boxed_1090_; size_t v_i_boxed_1091_; lean_object* v_res_1092_; 
v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1084_, v___x_1085_, v___x_1086_, v_sz_boxed_1090_, v_i_boxed_1091_, v_bs_1089_);
lean_dec(v___x_1086_);
lean_dec(v___x_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1093_, size_t v_sz_1094_, size_t v_i_1095_, lean_object* v_b_1096_){
_start:
{
lean_object* v_a_1099_; uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1095_, v_sz_1094_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_b_1096_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1148_; 
v_a_1105_ = lean_array_uget_borrowed(v_as_1093_, v_i_1095_);
v_fst_1106_ = lean_ctor_get(v_a_1105_, 0);
v_snd_1107_ = lean_ctor_get(v_a_1105_, 1);
v_fst_1108_ = lean_ctor_get(v_b_1096_, 0);
v_snd_1109_ = lean_ctor_get(v_b_1096_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_b_1096_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1111_ = v_b_1096_;
v_isShared_1112_ = v_isSharedCheck_1148_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snd_1109_);
lean_inc(v_fst_1108_);
lean_dec(v_b_1096_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1148_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_sub(v_fst_1106_, v___x_1113_);
v___x_1115_ = lean_array_get_size(v_fst_1108_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; 
lean_dec(v___x_1114_);
if (v_isShared_1112_ == 0)
{
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_fst_1108_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_snd_1109_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
v_a_1099_ = v___x_1118_;
goto v___jp_1098_;
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; lean_object* v___x_1137_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___x_1142_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_fget_borrowed(v_fst_1108_, v___x_1114_);
v___x_1122_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1121_);
v___x_1137_ = lean_array_get_size(v_snd_1107_);
v___x_1142_ = lean_nat_dec_eq(v___x_1137_, v___x_1120_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___y_1145_; uint8_t v___x_1147_; 
v___x_1143_ = lean_nat_sub(v___x_1137_, v___x_1113_);
v___x_1147_ = lean_nat_dec_le(v___x_1120_, v___x_1143_);
if (v___x_1147_ == 0)
{
lean_inc(v___x_1143_);
v___y_1145_ = v___x_1143_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___x_1120_;
goto v___jp_1144_;
}
v___jp_1144_:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_nat_dec_le(v___y_1145_, v___x_1143_);
if (v___x_1146_ == 0)
{
lean_dec(v___x_1143_);
lean_inc(v___y_1145_);
v___y_1139_ = v___y_1145_;
v___y_1140_ = v___y_1145_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v___y_1145_;
v___y_1140_ = v___x_1143_;
goto v___jp_1138_;
}
}
}
else
{
lean_inc(v_snd_1107_);
v___y_1124_ = v_snd_1107_;
goto v___jp_1123_;
}
v___jp_1123_:
{
size_t v_sz_1125_; size_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v_sz_1125_ = lean_array_size(v___y_1124_);
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1122_, v___x_1114_, v___x_1115_, v_sz_1125_, v___x_1126_, v___y_1124_);
lean_inc(v___x_1114_);
v___x_1128_ = l_Array_extract___redArg(v_fst_1108_, v___x_1120_, v___x_1114_);
v___x_1129_ = l_Array_append___redArg(v___x_1128_, v___x_1127_);
v___x_1130_ = l_Array_extract___redArg(v_fst_1108_, v___x_1114_, v___x_1115_);
lean_dec(v_fst_1108_);
v___x_1131_ = l_Array_append___redArg(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = lean_array_get_size(v___x_1127_);
lean_dec_ref(v___x_1127_);
v___x_1133_ = lean_nat_add(v_snd_1109_, v___x_1132_);
lean_dec(v_snd_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1133_);
lean_ctor_set(v___x_1111_, 0, v___x_1131_);
v___x_1135_ = v___x_1111_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
v_a_1099_ = v___x_1135_;
goto v___jp_1098_;
}
}
v___jp_1138_:
{
lean_object* v___x_1141_; 
lean_inc(v_snd_1107_);
v___x_1141_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1114_, v___x_1115_, v___x_1137_, v_snd_1107_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
v___y_1124_ = v___x_1141_;
goto v___jp_1123_;
}
}
}
}
v___jp_1098_:
{
size_t v___x_1100_; size_t v___x_1101_; 
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1095_, v___x_1100_);
v_i_1095_ = v___x_1101_;
v_b_1096_ = v_a_1099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1149_, lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_b_1152_, lean_object* v___y_1153_){
_start:
{
size_t v_sz_boxed_1154_; size_t v_i_boxed_1155_; lean_object* v_res_1156_; 
v_sz_boxed_1154_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1149_, v_sz_boxed_1154_, v_i_boxed_1155_, v_b_1152_);
lean_dec_ref(v_as_1149_);
return v_res_1156_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_unsigned_to_nat(16u);
v___x_1159_ = lean_mk_array(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_b_1176_){
_start:
{
lean_object* v_a_1179_; uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_b_1176_);
return v___x_1184_;
}
else
{
lean_object* v_a_1185_; lean_object* v_snd_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1295_; 
v_a_1185_ = lean_array_uget_borrowed(v_as_1173_, v_i_1175_);
v_snd_1186_ = lean_ctor_get(v_a_1185_, 1);
lean_inc(v_snd_1186_);
v_fst_1187_ = lean_ctor_get(v_snd_1186_, 0);
v_snd_1188_ = lean_ctor_get(v_snd_1186_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_snd_1186_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1190_ = v_snd_1186_;
v_isShared_1191_ = v_isSharedCheck_1295_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_snd_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1295_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; size_t v_sz_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1);
v_sz_1194_ = lean_array_size(v_snd_1188_);
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1188_, v_sz_1194_, v___x_1195_, v___x_1193_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___x_1212_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_box(0);
v___x_1212_ = l_IO_FS_readFile(v_fst_1187_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_size_1217_; lean_object* v_buckets_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; size_t v_sz_1221_; lean_object* v___x_1222_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1266_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
lean_dec(v_snd_1188_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_n(v_a_1213_, 2);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = lean_string_utf8_byte_size(v_a_1213_);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1192_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v___x_1215_);
v_size_1217_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_size_1217_);
v_buckets_1218_ = lean_ctor_get(v_a_1197_, 1);
lean_inc_ref(v_buckets_1218_);
lean_dec(v_a_1197_);
v___x_1219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1220_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1213_, v___x_1215_, v___x_1214_, v___x_1216_, v___x_1219_);
lean_dec_ref_known(v___x_1215_, 3);
v_sz_1221_ = lean_array_size(v___x_1220_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1221_, v___x_1195_, v___x_1220_);
v___x_1272_ = lean_mk_empty_array_with_capacity(v_size_1217_);
lean_dec(v_size_1217_);
v___x_1273_ = lean_array_get_size(v_buckets_1218_);
v___x_1274_ = lean_nat_dec_lt(v___x_1192_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_dec_ref(v_buckets_1218_);
v___y_1266_ = v___x_1272_;
goto v___jp_1265_;
}
else
{
size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_usize_of_nat(v___x_1273_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1218_, v___x_1195_, v___x_1275_, v___x_1272_);
lean_dec_ref(v_buckets_1218_);
v___y_1266_ = v___x_1276_;
goto v___jp_1265_;
}
v___jp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1192_);
lean_ctor_set(v___x_1190_, 0, v___x_1222_);
v___x_1227_ = v___x_1190_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1192_);
v___x_1227_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
size_t v_sz_1228_; lean_object* v___x_1229_; 
v_sz_1228_ = lean_array_size(v___y_1225_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1225_, v_sz_1228_, v___x_1195_, v___x_1227_);
lean_dec_ref(v___y_1225_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v_fst_1231_; lean_object* v_snd_1232_; uint8_t v___x_1233_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v_fst_1231_ = lean_ctor_get(v_a_1230_, 0);
lean_inc(v_fst_1231_);
v_snd_1232_ = lean_ctor_get(v_a_1230_, 1);
lean_inc(v_snd_1232_);
lean_dec(v_a_1230_);
v___x_1233_ = lean_nat_dec_lt(v___x_1192_, v_snd_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_snd_1232_);
lean_dec(v_fst_1231_);
lean_dec(v_fst_1187_);
v_a_1179_ = v___x_1198_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1232_);
v___x_1235_ = l_Nat_reprFast(v_snd_1232_);
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1238_ = lean_string_append(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_nat_dec_eq(v_snd_1232_, v___y_1224_);
lean_dec(v_snd_1232_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1200_ = v_fst_1231_;
v___y_1201_ = v___x_1238_;
v___y_1202_ = v___x_1240_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1200_ = v_fst_1231_;
v___y_1201_ = v___x_1238_;
v___y_1202_ = v___x_1241_;
goto v___jp_1199_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_fst_1187_);
v_a_1242_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1229_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1229_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1257_; 
v___x_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1252_, v___y_1253_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec(v___y_1252_);
v___y_1224_ = v___y_1254_;
v___y_1225_ = v___x_1257_;
goto v___jp_1223_;
}
v___jp_1258_:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_le(v___y_1263_, v___y_1262_);
if (v___x_1264_ == 0)
{
lean_dec(v___y_1262_);
lean_inc(v___y_1263_);
v___y_1252_ = v___y_1259_;
v___y_1253_ = v___y_1260_;
v___y_1254_ = v___y_1261_;
v___y_1255_ = v___y_1263_;
v___y_1256_ = v___y_1263_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v___y_1259_;
v___y_1253_ = v___y_1260_;
v___y_1254_ = v___y_1261_;
v___y_1255_ = v___y_1263_;
v___y_1256_ = v___y_1262_;
goto v___jp_1251_;
}
}
v___jp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_array_get_size(v___y_1266_);
v___x_1269_ = lean_nat_dec_eq(v___x_1268_, v___x_1192_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_nat_sub(v___x_1268_, v___x_1267_);
v___x_1271_ = lean_nat_dec_le(v___x_1192_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_inc(v___x_1270_);
v___y_1259_ = v___x_1268_;
v___y_1260_ = v___y_1266_;
v___y_1261_ = v___x_1267_;
v___y_1262_ = v___x_1270_;
v___y_1263_ = v___x_1270_;
goto v___jp_1258_;
}
else
{
v___y_1259_ = v___x_1268_;
v___y_1260_ = v___y_1266_;
v___y_1261_ = v___x_1267_;
v___y_1262_ = v___x_1270_;
v___y_1263_ = v___x_1192_;
goto v___jp_1258_;
}
}
else
{
v___y_1224_ = v___x_1267_;
v___y_1225_ = v___y_1266_;
goto v___jp_1223_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec_ref_known(v___x_1212_, 1);
lean_dec(v_a_1197_);
lean_del_object(v___x_1190_);
v___x_1277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1278_ = lean_string_append(v___x_1277_, v_fst_1187_);
lean_dec(v_fst_1187_);
v___x_1279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1280_ = lean_string_append(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_array_get_size(v_snd_1188_);
lean_dec(v_snd_1188_);
v___x_1282_ = l_Nat_reprFast(v___x_1281_);
v___x_1283_ = lean_string_append(v___x_1280_, v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1285_ = lean_string_append(v___x_1283_, v___x_1284_);
v___x_1286_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref_known(v___x_1286_, 1);
v_a_1179_ = v___x_1198_;
goto v___jp_1178_;
}
else
{
return v___x_1286_;
}
}
v___jp_1199_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1203_ = lean_string_append(v___y_1201_, v___y_1202_);
v___x_1204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2));
v___x_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
v___x_1206_ = lean_string_append(v___x_1205_, v_fst_1187_);
v___x_1207_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1207_, 1);
v___x_1208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3));
v___x_1209_ = lean_array_to_list(v___y_1200_);
v___x_1210_ = l_String_intercalate(v___x_1208_, v___x_1209_);
v___x_1211_ = l_IO_FS_writeFile(v_fst_1187_, v___x_1210_);
lean_dec_ref(v___x_1210_);
lean_dec(v_fst_1187_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_dec_ref_known(v___x_1211_, 1);
v_a_1179_ = v___x_1198_;
goto v___jp_1178_;
}
else
{
return v___x_1211_;
}
}
else
{
lean_dec(v___y_1200_);
lean_dec(v_fst_1187_);
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1190_);
lean_dec(v_snd_1188_);
lean_dec(v_fst_1187_);
v_a_1287_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1196_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1196_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
v___jp_1178_:
{
size_t v___x_1180_; size_t v___x_1181_; 
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1175_, v___x_1180_);
v_i_1175_ = v___x_1181_;
v_b_1176_ = v_a_1179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1296_, lean_object* v_sz_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1297_);
lean_dec(v_sz_1297_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1296_, v_sz_boxed_1301_, v_i_boxed_1302_, v_b_1299_);
lean_dec_ref(v_as_1296_);
return v_res_1303_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1304_, lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
return v___x_1306_;
}
else
{
lean_object* v_key_1307_; lean_object* v_tail_1308_; uint8_t v___x_1309_; 
v_key_1307_ = lean_ctor_get(v_x_1305_, 0);
v_tail_1308_ = lean_ctor_get(v_x_1305_, 2);
v___x_1309_ = lean_string_dec_eq(v_key_1307_, v_a_1304_);
if (v___x_1309_ == 0)
{
v_x_1305_ = v_tail_1308_;
goto _start;
}
else
{
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_res_1313_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1311_, v_x_1312_);
lean_dec(v_x_1312_);
lean_dec_ref(v_a_1311_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1315_, lean_object* v_b_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
lean_dec(v_b_1316_);
lean_dec_ref(v_a_1315_);
return v_x_1317_;
}
else
{
lean_object* v_key_1318_; lean_object* v_value_1319_; lean_object* v_tail_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1332_; 
v_key_1318_ = lean_ctor_get(v_x_1317_, 0);
v_value_1319_ = lean_ctor_get(v_x_1317_, 1);
v_tail_1320_ = lean_ctor_get(v_x_1317_, 2);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1317_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1322_ = v_x_1317_;
v_isShared_1323_ = v_isSharedCheck_1332_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_tail_1320_);
lean_inc(v_value_1319_);
lean_inc(v_key_1318_);
lean_dec(v_x_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1332_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_string_dec_eq(v_key_1318_, v_a_1315_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1315_, v_b_1316_, v_tail_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 2, v___x_1325_);
v___x_1327_ = v___x_1322_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_value_1319_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v___x_1330_; 
lean_dec(v_value_1319_);
lean_dec(v_key_1318_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_b_1316_);
lean_ctor_set(v___x_1322_, 0, v_a_1315_);
v___x_1330_ = v___x_1322_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_b_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_tail_1320_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
if (lean_obj_tag(v_x_1334_) == 0)
{
return v_x_1333_;
}
else
{
lean_object* v_key_1335_; lean_object* v_value_1336_; lean_object* v_tail_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1360_; 
v_key_1335_ = lean_ctor_get(v_x_1334_, 0);
v_value_1336_ = lean_ctor_get(v_x_1334_, 1);
v_tail_1337_ = lean_ctor_get(v_x_1334_, 2);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_x_1334_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1339_ = v_x_1334_;
v_isShared_1340_ = v_isSharedCheck_1360_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_tail_1337_);
lean_inc(v_value_1336_);
lean_inc(v_key_1335_);
lean_dec(v_x_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1360_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v_fold_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1341_ = lean_array_get_size(v_x_1333_);
v___x_1342_ = lean_string_hash(v_key_1335_);
v___x_1343_ = 32ULL;
v___x_1344_ = lean_uint64_shift_right(v___x_1342_, v___x_1343_);
v_fold_1345_ = lean_uint64_xor(v___x_1342_, v___x_1344_);
v___x_1346_ = 16ULL;
v___x_1347_ = lean_uint64_shift_right(v_fold_1345_, v___x_1346_);
v___x_1348_ = lean_uint64_xor(v_fold_1345_, v___x_1347_);
v___x_1349_ = lean_uint64_to_usize(v___x_1348_);
v___x_1350_ = lean_usize_of_nat(v___x_1341_);
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_sub(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_usize_land(v___x_1349_, v___x_1352_);
v___x_1354_ = lean_array_uget_borrowed(v_x_1333_, v___x_1353_);
lean_inc(v___x_1354_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 2, v___x_1354_);
v___x_1356_ = v___x_1339_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_key_1335_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_value_1336_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_array_uset(v_x_1333_, v___x_1353_, v___x_1356_);
v_x_1333_ = v___x_1357_;
v_x_1334_ = v_tail_1337_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1361_, lean_object* v_source_1362_, lean_object* v_target_1363_){
_start:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_array_get_size(v_source_1362_);
v___x_1365_ = lean_nat_dec_lt(v_i_1361_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v_source_1362_);
lean_dec(v_i_1361_);
return v_target_1363_;
}
else
{
lean_object* v_es_1366_; lean_object* v___x_1367_; lean_object* v_source_1368_; lean_object* v_target_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_es_1366_ = lean_array_fget(v_source_1362_, v_i_1361_);
v___x_1367_ = lean_box(0);
v_source_1368_ = lean_array_fset(v_source_1362_, v_i_1361_, v___x_1367_);
v_target_1369_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1363_, v_es_1366_);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_i_1361_, v___x_1370_);
lean_dec(v_i_1361_);
v_i_1361_ = v___x_1371_;
v_source_1362_ = v_source_1368_;
v_target_1363_ = v_target_1369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_nbuckets_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1374_ = lean_array_get_size(v_data_1373_);
v___x_1375_ = lean_unsigned_to_nat(2u);
v_nbuckets_1376_ = lean_nat_mul(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_mk_array(v_nbuckets_1376_, v___x_1378_);
v___x_1380_ = lean_array_propagate_mark(v_data_1373_, v___x_1379_);
v___x_1381_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1377_, v_data_1373_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1382_, lean_object* v_a_1383_, lean_object* v_b_1384_){
_start:
{
lean_object* v_size_1385_; lean_object* v_buckets_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1429_; 
v_size_1385_ = lean_ctor_get(v_m_1382_, 0);
v_buckets_1386_ = lean_ctor_get(v_m_1382_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_m_1382_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1388_ = v_m_1382_;
v_isShared_1389_ = v_isSharedCheck_1429_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_buckets_1386_);
lean_inc(v_size_1385_);
lean_dec(v_m_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1429_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; uint64_t v___x_1391_; uint64_t v___x_1392_; uint64_t v___x_1393_; uint64_t v_fold_1394_; uint64_t v___x_1395_; uint64_t v___x_1396_; uint64_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v_bkt_1403_; uint8_t v___x_1404_; 
v___x_1390_ = lean_array_get_size(v_buckets_1386_);
v___x_1391_ = lean_string_hash(v_a_1383_);
v___x_1392_ = 32ULL;
v___x_1393_ = lean_uint64_shift_right(v___x_1391_, v___x_1392_);
v_fold_1394_ = lean_uint64_xor(v___x_1391_, v___x_1393_);
v___x_1395_ = 16ULL;
v___x_1396_ = lean_uint64_shift_right(v_fold_1394_, v___x_1395_);
v___x_1397_ = lean_uint64_xor(v_fold_1394_, v___x_1396_);
v___x_1398_ = lean_uint64_to_usize(v___x_1397_);
v___x_1399_ = lean_usize_of_nat(v___x_1390_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_sub(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_usize_land(v___x_1398_, v___x_1401_);
v_bkt_1403_ = lean_array_uget_borrowed(v_buckets_1386_, v___x_1402_);
v___x_1404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1383_, v_bkt_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v_size_x27_1406_; lean_object* v___x_1407_; lean_object* v_buckets_x27_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1405_ = lean_unsigned_to_nat(1u);
v_size_x27_1406_ = lean_nat_add(v_size_1385_, v___x_1405_);
lean_dec(v_size_1385_);
lean_inc(v_bkt_1403_);
v___x_1407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1407_, 0, v_a_1383_);
lean_ctor_set(v___x_1407_, 1, v_b_1384_);
lean_ctor_set(v___x_1407_, 2, v_bkt_1403_);
v_buckets_x27_1408_ = lean_array_uset(v_buckets_1386_, v___x_1402_, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(4u);
v___x_1410_ = lean_nat_mul(v_size_x27_1406_, v___x_1409_);
v___x_1411_ = lean_unsigned_to_nat(3u);
v___x_1412_ = lean_nat_div(v___x_1410_, v___x_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_array_get_size(v_buckets_x27_1408_);
v___x_1414_ = lean_nat_dec_le(v___x_1412_, v___x_1413_);
lean_dec(v___x_1412_);
if (v___x_1414_ == 0)
{
lean_object* v_val_1415_; lean_object* v___x_1417_; 
v_val_1415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1408_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_val_1415_);
lean_ctor_set(v___x_1388_, 0, v_size_x27_1406_);
v___x_1417_ = v___x_1388_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_size_x27_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_val_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
lean_object* v___x_1420_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_buckets_x27_1408_);
lean_ctor_set(v___x_1388_, 0, v_size_x27_1406_);
v___x_1420_ = v___x_1388_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_size_x27_1406_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_buckets_x27_1408_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v_buckets_x27_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_inc(v_bkt_1403_);
v___x_1422_ = lean_box(0);
v_buckets_x27_1423_ = lean_array_uset(v_buckets_1386_, v___x_1402_, v___x_1422_);
v___x_1424_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1383_, v_b_1384_, v_bkt_1403_);
v___x_1425_ = lean_array_uset(v_buckets_x27_1423_, v___x_1402_, v___x_1424_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1425_);
v___x_1427_ = v___x_1388_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_size_1385_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1430_, lean_object* v_fallback_1431_, lean_object* v_x_1432_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
lean_inc(v_fallback_1431_);
return v_fallback_1431_;
}
else
{
lean_object* v_key_1433_; lean_object* v_value_1434_; lean_object* v_tail_1435_; uint8_t v___x_1436_; 
v_key_1433_ = lean_ctor_get(v_x_1432_, 0);
v_value_1434_ = lean_ctor_get(v_x_1432_, 1);
v_tail_1435_ = lean_ctor_get(v_x_1432_, 2);
v___x_1436_ = lean_string_dec_eq(v_key_1433_, v_a_1430_);
if (v___x_1436_ == 0)
{
v_x_1432_ = v_tail_1435_;
goto _start;
}
else
{
lean_inc(v_value_1434_);
return v_value_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1438_, lean_object* v_fallback_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1438_, v_fallback_1439_, v_x_1440_);
lean_dec(v_x_1440_);
lean_dec(v_fallback_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1442_, lean_object* v_a_1443_, lean_object* v_fallback_1444_){
_start:
{
lean_object* v_buckets_1445_; lean_object* v___x_1446_; uint64_t v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v_fold_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_buckets_1445_ = lean_ctor_get(v_m_1442_, 1);
v___x_1446_ = lean_array_get_size(v_buckets_1445_);
v___x_1447_ = lean_string_hash(v_a_1443_);
v___x_1448_ = 32ULL;
v___x_1449_ = lean_uint64_shift_right(v___x_1447_, v___x_1448_);
v_fold_1450_ = lean_uint64_xor(v___x_1447_, v___x_1449_);
v___x_1451_ = 16ULL;
v___x_1452_ = lean_uint64_shift_right(v_fold_1450_, v___x_1451_);
v___x_1453_ = lean_uint64_xor(v_fold_1450_, v___x_1452_);
v___x_1454_ = lean_uint64_to_usize(v___x_1453_);
v___x_1455_ = lean_usize_of_nat(v___x_1446_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_sub(v___x_1455_, v___x_1456_);
v___x_1458_ = lean_usize_land(v___x_1454_, v___x_1457_);
v___x_1459_ = lean_array_uget_borrowed(v_buckets_1445_, v___x_1458_);
v___x_1460_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1443_, v_fallback_1444_, v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1461_, lean_object* v_a_1462_, lean_object* v_fallback_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1461_, v_a_1462_, v_fallback_1463_);
lean_dec(v_fallback_1463_);
lean_dec_ref(v_a_1462_);
lean_dec_ref(v_m_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_b_1470_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1470_);
return v___x_1473_;
}
else
{
lean_object* v_a_1474_; lean_object* v_file_1475_; lean_object* v_pos_1476_; lean_object* v_option_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1503_; 
v_a_1474_ = lean_array_uget_borrowed(v_as_1467_, v_i_1469_);
v_file_1475_ = lean_ctor_get(v_a_1474_, 0);
v_pos_1476_ = lean_ctor_get(v_a_1474_, 1);
lean_inc_ref(v_pos_1476_);
v_option_1477_ = lean_ctor_get(v_a_1474_, 2);
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1475_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_file_1475_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1470_, v_file_1475_, v___x_1479_);
lean_dec_ref_known(v___x_1479_, 2);
v_fst_1481_ = lean_ctor_get(v___x_1480_, 0);
v_snd_1482_ = lean_ctor_get(v___x_1480_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1484_ = v___x_1480_;
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_snd_1482_);
lean_inc(v_fst_1481_);
lean_dec(v___x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_line_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1501_; 
v_line_1486_ = lean_ctor_get(v_pos_1476_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_pos_1476_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_pos_1476_, 1);
lean_dec(v_unused_1502_);
v___x_1488_ = v_pos_1476_;
v_isShared_1489_ = v_isSharedCheck_1501_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_line_1486_);
lean_dec(v_pos_1476_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1501_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
lean_inc(v_option_1477_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_option_1477_);
lean_ctor_set(v___x_1484_, 0, v_line_1486_);
v___x_1491_ = v___x_1484_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_line_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_option_1477_);
v___x_1491_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_array_push(v_snd_1482_, v___x_1491_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v___x_1492_);
lean_ctor_set(v___x_1488_, 0, v_fst_1481_);
v___x_1494_ = v___x_1488_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_fst_1481_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; 
lean_inc_ref(v_file_1475_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1470_, v_file_1475_, v___x_1494_);
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1469_, v___x_1496_);
v_i_1469_ = v___x_1497_;
v_b_1470_ = v___x_1495_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1504_, lean_object* v_sz_1505_, lean_object* v_i_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_){
_start:
{
size_t v_sz_boxed_1509_; size_t v_i_boxed_1510_; lean_object* v_res_1511_; 
v_sz_boxed_1509_ = lean_unbox_usize(v_sz_1505_);
lean_dec(v_sz_1505_);
v_i_boxed_1510_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1504_, v_sz_boxed_1509_, v_i_boxed_1510_, v_b_1507_);
lean_dec_ref(v_as_1504_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_unsigned_to_nat(16u);
v___x_1514_ = lean_mk_array(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_byFile_1517_; 
v___x_1515_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1516_ = lean_unsigned_to_nat(0u);
v_byFile_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1517_, 0, v___x_1516_);
lean_ctor_set(v_byFile_1517_, 1, v___x_1515_);
return v_byFile_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_byFile_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v_byFile_1521_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1522_ = lean_array_size(v_records_1518_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1518_, v_sz_1522_, v___x_1523_, v_byFile_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___y_1527_; lean_object* v_size_1539_; lean_object* v_buckets_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_size_1539_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_size_1539_);
v_buckets_1540_ = lean_ctor_get(v_a_1525_, 1);
lean_inc_ref(v_buckets_1540_);
lean_dec(v_a_1525_);
v___x_1541_ = lean_mk_empty_array_with_capacity(v_size_1539_);
lean_dec(v_size_1539_);
v___x_1542_ = lean_array_get_size(v_buckets_1540_);
v___x_1543_ = lean_nat_dec_lt(v___x_1520_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_dec_ref(v_buckets_1540_);
v___y_1527_ = v___x_1541_;
goto v___jp_1526_;
}
else
{
size_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_usize_of_nat(v___x_1542_);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1540_, v___x_1523_, v___x_1544_, v___x_1541_);
lean_dec_ref(v_buckets_1540_);
v___y_1527_ = v___x_1545_;
goto v___jp_1526_;
}
v___jp_1526_:
{
lean_object* v___x_1528_; size_t v_sz_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_box(0);
v_sz_1529_ = lean_array_size(v___y_1527_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1527_, v_sz_1529_, v___x_1523_, v___x_1528_);
lean_dec_ref(v___y_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1530_, 0);
lean_dec(v_unused_1538_);
v___x_1532_ = v___x_1530_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v___x_1530_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1528_);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1528_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1524_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1524_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1554_);
lean_dec_ref(v_records_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1557_, lean_object* v_m_1558_, lean_object* v_a_1559_, lean_object* v_fallback_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1558_, v_a_1559_, v_fallback_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1562_, lean_object* v_m_1563_, lean_object* v_a_1564_, lean_object* v_fallback_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1562_, v_m_1563_, v_a_1564_, v_fallback_1565_);
lean_dec(v_fallback_1565_);
lean_dec_ref(v_a_1564_);
lean_dec_ref(v_m_1563_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1568_, v_a_1569_, v_b_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_a_1574_, lean_object* v_fallback_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1573_, v_a_1574_, v_fallback_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, lean_object* v_a_1579_, lean_object* v_fallback_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1577_, v_m_1578_, v_a_1579_, v_fallback_1580_);
lean_dec(v_fallback_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_m_1578_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1582_, lean_object* v_m_1583_, lean_object* v_a_1584_, lean_object* v_b_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1583_, v_a_1584_, v_b_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1587_, lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v_inst_1590_, lean_object* v_R_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1587_, v___x_1588_, v___x_1589_, v_a_1592_, v_b_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v_inst_1598_, lean_object* v_R_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1595_, v___x_1596_, v___x_1597_, v_inst_1598_, v_R_1599_, v_a_1600_, v_b_1601_);
lean_dec_ref(v___x_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v_n_1605_, lean_object* v_as_1606_, lean_object* v_lo_1607_, lean_object* v_hi_1608_, lean_object* v_w_1609_, lean_object* v_hlo_1610_, lean_object* v_hhi_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1603_, v___x_1604_, v_n_1605_, v_as_1606_, v_lo_1607_, v_hi_1608_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_n_1615_, lean_object* v_as_1616_, lean_object* v_lo_1617_, lean_object* v_hi_1618_, lean_object* v_w_1619_, lean_object* v_hlo_1620_, lean_object* v_hhi_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1613_, v___x_1614_, v_n_1615_, v_as_1616_, v_lo_1617_, v_hi_1618_, v_w_1619_, v_hlo_1620_, v_hhi_1621_);
lean_dec(v_hi_1618_);
lean_dec(v_n_1615_);
lean_dec(v___x_1614_);
lean_dec(v___x_1613_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_, lean_object* v_w_1627_, lean_object* v_hlo_1628_, lean_object* v_hhi_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1623_, v_as_1624_, v_lo_1625_, v_hi_1626_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1631_, lean_object* v_as_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_, lean_object* v_w_1635_, lean_object* v_hlo_1636_, lean_object* v_hhi_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1631_, v_as_1632_, v_lo_1633_, v_hi_1634_, v_w_1635_, v_hlo_1636_, v_hhi_1637_);
lean_dec(v_hi_1634_);
lean_dec(v_n_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_fallback_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1640_, v_fallback_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_fallback_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1644_, v_a_1645_, v_fallback_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec(v_fallback_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1649_, lean_object* v_a_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1650_, v_x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1653_, lean_object* v_a_1654_, lean_object* v_x_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1653_, v_a_1654_, v_x_1655_);
lean_dec(v_x_1655_);
lean_dec_ref(v_a_1654_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1658_, lean_object* v_data_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1662_, v_b_1663_, v_x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1666_, lean_object* v_a_1667_, lean_object* v_fallback_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1667_, v_fallback_1668_, v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1671_, lean_object* v_a_1672_, lean_object* v_fallback_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1671_, v_a_1672_, v_fallback_1673_, v_x_1674_);
lean_dec(v_x_1674_);
lean_dec(v_fallback_1673_);
lean_dec(v_a_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1676_, lean_object* v_a_1677_, lean_object* v_x_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1677_, v_x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1680_, lean_object* v_a_1681_, lean_object* v_x_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1680_, v_a_1681_, v_x_1682_);
lean_dec(v_x_1682_);
lean_dec(v_a_1681_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1685_, lean_object* v_data_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1689_, v_b_1690_, v_x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v_n_1695_, lean_object* v_lo_1696_, lean_object* v_hi_1697_, lean_object* v_hhi_1698_, lean_object* v_pivot_1699_, lean_object* v_as_1700_, lean_object* v_i_1701_, lean_object* v_k_1702_, lean_object* v_ilo_1703_, lean_object* v_ik_1704_, lean_object* v_w_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1693_, v___x_1694_, v_hi_1697_, v_pivot_1699_, v_as_1700_, v_i_1701_, v_k_1702_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v_n_1709_, lean_object* v_lo_1710_, lean_object* v_hi_1711_, lean_object* v_hhi_1712_, lean_object* v_pivot_1713_, lean_object* v_as_1714_, lean_object* v_i_1715_, lean_object* v_k_1716_, lean_object* v_ilo_1717_, lean_object* v_ik_1718_, lean_object* v_w_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1707_, v___x_1708_, v_n_1709_, v_lo_1710_, v_hi_1711_, v_hhi_1712_, v_pivot_1713_, v_as_1714_, v_i_1715_, v_k_1716_, v_ilo_1717_, v_ik_1718_, v_w_1719_);
lean_dec(v_hi_1711_);
lean_dec(v_lo_1710_);
lean_dec(v_n_1709_);
lean_dec(v___x_1708_);
lean_dec(v___x_1707_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1721_, lean_object* v_lo_1722_, lean_object* v_hi_1723_, lean_object* v_hhi_1724_, lean_object* v_pivot_1725_, lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_k_1728_, lean_object* v_ilo_1729_, lean_object* v_ik_1730_, lean_object* v_w_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1723_, v_pivot_1725_, v_as_1726_, v_i_1727_, v_k_1728_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1733_, lean_object* v_lo_1734_, lean_object* v_hi_1735_, lean_object* v_hhi_1736_, lean_object* v_pivot_1737_, lean_object* v_as_1738_, lean_object* v_i_1739_, lean_object* v_k_1740_, lean_object* v_ilo_1741_, lean_object* v_ik_1742_, lean_object* v_w_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1733_, v_lo_1734_, v_hi_1735_, v_hhi_1736_, v_pivot_1737_, v_as_1738_, v_i_1739_, v_k_1740_, v_ilo_1741_, v_ik_1742_, v_w_1743_);
lean_dec_ref(v_pivot_1737_);
lean_dec(v_hi_1735_);
lean_dec(v_lo_1734_);
lean_dec(v_n_1733_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1745_, lean_object* v_i_1746_, lean_object* v_source_1747_, lean_object* v_target_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1746_, v_source_1747_, v_target_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1750_, lean_object* v_i_1751_, lean_object* v_source_1752_, lean_object* v_target_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1751_, v_source_1752_, v_target_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1756_, v_x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1760_, v_x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v_env_1767_; lean_object* v___x_1768_; lean_object* v_env_1769_; lean_object* v___x_1770_; lean_object* v_toEnvExtension_1771_; lean_object* v_asyncMode_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1766_ = lean_st_ref_get(v___y_1764_);
v_env_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc_ref(v_env_1767_);
lean_dec(v___x_1766_);
v___x_1768_ = lean_st_ref_get(v___y_1764_);
v_env_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc_ref(v_env_1769_);
lean_dec(v___x_1768_);
v___x_1770_ = l_Lean_declRangeExt;
v_toEnvExtension_1771_ = lean_ctor_get(v___x_1770_, 0);
v_asyncMode_1772_ = lean_ctor_get(v_toEnvExtension_1771_, 2);
v___x_1773_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1774_ = 0;
lean_inc(v_declName_1763_);
v___x_1775_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1773_, v___x_1770_, v_env_1767_, v_declName_1763_, v_asyncMode_1772_, v___x_1774_);
if (lean_obj_tag(v___x_1775_) == 0)
{
uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = 1;
v___x_1777_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1773_, v___x_1770_, v_env_1769_, v_declName_1763_, v_asyncMode_1772_, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; 
lean_dec_ref(v_env_1769_);
lean_dec(v_declName_1763_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1775_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1780_, v___y_1781_);
lean_dec(v___y_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = lean_st_ref_get(v___y_1785_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Lean_isRecCore(v_env_1788_, v_declName_1784_);
v___x_1790_ = lean_box(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1792_, v___y_1793_);
lean_dec(v___y_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_ranges_1801_; lean_object* v___x_1807_; lean_object* v_env_1808_; lean_object* v___x_1809_; lean_object* v_a_1810_; uint8_t v___y_1816_; uint8_t v___x_1820_; 
v___x_1807_ = lean_st_ref_get(v___y_1798_);
v_env_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_ref_n(v_env_1808_, 2);
lean_dec(v___x_1807_);
lean_inc_n(v_declName_1796_, 2);
v___x_1809_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1796_, v___y_1798_);
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
v___x_1820_ = l_Lean_isAuxRecursor(v_env_1808_, v_declName_1796_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
lean_inc(v_declName_1796_);
v___x_1821_ = l_Lean_isNoConfusion(v_env_1808_, v_declName_1796_);
v___y_1816_ = v___x_1821_;
goto v___jp_1815_;
}
else
{
lean_dec_ref(v_env_1808_);
v___y_1816_ = v___x_1820_;
goto v___jp_1815_;
}
v___jp_1800_:
{
if (lean_obj_tag(v_ranges_1801_) == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = l_Lean_builtinDeclRanges;
v___x_1803_ = lean_st_ref_get(v___x_1802_);
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1803_, v_declName_1796_);
lean_dec(v_declName_1796_);
lean_dec(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_declName_1796_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_ranges_1801_);
return v___x_1806_;
}
}
v___jp_1811_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; 
v___x_1812_ = l_Lean_Name_getPrefix(v_declName_1796_);
v___x_1813_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1812_, v___y_1798_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v_ranges_1801_ = v_a_1814_;
goto v___jp_1800_;
}
v___jp_1815_:
{
if (v___y_1816_ == 0)
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_unbox(v_a_1810_);
lean_dec(v_a_1810_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v_a_1819_; 
lean_inc(v_declName_1796_);
v___x_1818_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1796_, v___y_1798_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v_ranges_1801_ = v_a_1819_;
goto v___jp_1800_;
}
else
{
goto v___jp_1811_;
}
}
else
{
lean_dec(v_a_1810_);
goto v___jp_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1827_, lean_object* v_site_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
if (lean_obj_tag(v_site_1828_) == 0)
{
lean_object* v_name_1832_; lean_object* v___x_1833_; 
v_name_1832_ = lean_ctor_get(v_site_1828_, 0);
lean_inc(v_name_1832_);
lean_dec_ref_known(v_site_1828_, 1);
v___x_1833_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1832_, v_a_1829_, v_a_1830_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1855_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1855_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1855_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
else
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1854_; 
v_val_1842_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1844_ = v_a_1834_;
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v_a_1834_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1854_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_range_1846_; lean_object* v_pos_1847_; lean_object* v___x_1849_; 
v_range_1846_ = lean_ctor_get(v_val_1842_, 0);
lean_inc_ref(v_range_1846_);
lean_dec(v_val_1842_);
v_pos_1847_ = lean_ctor_get(v_range_1846_, 0);
lean_inc_ref(v_pos_1847_);
lean_dec_ref(v_range_1846_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_pos_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_pos_1847_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1849_);
v___x_1851_ = v___x_1836_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1833_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1833_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_n_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1895_; 
v_n_1864_ = lean_ctor_get(v_site_1828_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_site_1828_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1866_ = v_site_1828_;
v_isShared_1867_ = v_isSharedCheck_1895_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_n_1864_);
lean_dec(v_site_1828_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1895_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v_env_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_st_ref_get(v_a_1830_);
v_env_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_env_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Lean_getVersoModuleDoc_x3f(v_env_1869_, v_failMod_1827_);
lean_dec_ref(v_env_1869_);
if (lean_obj_tag(v___x_1870_) == 1)
{
lean_object* v_val_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1890_; 
v_val_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1890_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_val_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1890_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_array_get_size(v_val_1871_);
v___x_1876_ = lean_nat_dec_lt(v_n_1864_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_del_object(v___x_1873_);
lean_dec(v_val_1871_);
lean_dec(v_n_1864_);
v___x_1877_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1877_);
v___x_1879_ = v___x_1866_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v_declarationRange_1882_; lean_object* v_pos_1883_; lean_object* v___x_1885_; 
v___x_1881_ = lean_array_fget(v_val_1871_, v_n_1864_);
lean_dec(v_n_1864_);
lean_dec(v_val_1871_);
v_declarationRange_1882_ = lean_ctor_get(v___x_1881_, 2);
lean_inc_ref(v_declarationRange_1882_);
lean_dec(v___x_1881_);
v_pos_1883_ = lean_ctor_get(v_declarationRange_1882_, 0);
lean_inc_ref(v_pos_1883_);
lean_dec_ref(v_declarationRange_1882_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v_pos_1883_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_pos_1883_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1885_);
v___x_1887_ = v___x_1866_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec(v___x_1870_);
lean_dec(v_n_1864_);
v___x_1891_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1891_);
v___x_1893_ = v___x_1866_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1896_, lean_object* v_site_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1896_, v_site_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_failMod_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1902_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1912_, v___y_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v_name_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_name_1926_ = lean_ctor_get(v_x_1925_, 0);
lean_inc(v_name_1926_);
lean_dec_ref_known(v_x_1925_, 1);
v___x_1927_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1928_ = 1;
v___x_1929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1926_, v___x_1928_);
v___x_1930_ = lean_string_append(v___x_1927_, v___x_1929_);
lean_dec_ref(v___x_1929_);
v___x_1931_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1932_ = lean_string_append(v___x_1930_, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v_n_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_n_1933_ = lean_ctor_get(v_x_1925_, 0);
lean_inc(v_n_1933_);
lean_dec_ref_known(v_x_1925_, 1);
v___x_1934_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_n_1933_, v___x_1935_);
lean_dec(v_n_1933_);
v___x_1937_ = l_Nat_reprFast(v___x_1936_);
v___x_1938_ = lean_string_append(v___x_1934_, v___x_1937_);
lean_dec_ref(v___x_1937_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v_env_1943_; lean_object* v___x_1944_; lean_object* v_toEnvExtension_1945_; lean_object* v_asyncMode_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_merged_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v___x_1942_ = lean_st_ref_get(v___y_1940_);
v_env_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_ref(v_env_1943_);
lean_dec(v___x_1942_);
v___x_1944_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1945_ = lean_ctor_get(v___x_1944_, 0);
v_asyncMode_1946_ = lean_ctor_get(v_toEnvExtension_1945_, 2);
v___x_1947_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1948_ = lean_box(0);
v___x_1949_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1947_, v___x_1944_, v_env_1943_, v_asyncMode_1946_, v___x_1948_);
v_merged_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v___x_1949_, 1);
lean_dec(v_unused_1959_);
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_merged_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_merged_1950_);
lean_ctor_set(v___x_1952_, 0, v_o_1939_);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_o_1939_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_merged_1950_);
v___x_1955_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; 
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1960_, v___y_1961_);
lean_dec(v___y_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1964_, v___y_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1974_, lean_object* v_opt_1975_){
_start:
{
lean_object* v_name_1976_; lean_object* v_defValue_1977_; lean_object* v_map_1978_; lean_object* v___x_1979_; 
v_name_1976_ = lean_ctor_get(v_opt_1975_, 0);
v_defValue_1977_ = lean_ctor_get(v_opt_1975_, 1);
v_map_1978_ = lean_ctor_get(v_opts_1974_, 0);
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1978_, v_name_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_unbox(v_defValue_1977_);
return v___x_1980_;
}
else
{
lean_object* v_val_1981_; 
v_val_1981_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_1981_);
lean_dec_ref_known(v___x_1979_, 1);
if (lean_obj_tag(v_val_1981_) == 1)
{
uint8_t v_v_1982_; 
v_v_1982_ = lean_ctor_get_uint8(v_val_1981_, 0);
lean_dec_ref_known(v_val_1981_, 0);
return v_v_1982_;
}
else
{
uint8_t v___x_1983_; 
lean_dec(v_val_1981_);
v___x_1983_ = lean_unbox(v_defValue_1977_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1984_, lean_object* v_opt_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1984_, v_opt_1985_);
lean_dec_ref(v_opt_1985_);
lean_dec_ref(v_opts_1984_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_opts_1988_, lean_object* v_opt_1989_){
_start:
{
lean_object* v_name_1990_; lean_object* v_defValue_1991_; lean_object* v_map_1992_; lean_object* v___x_1993_; 
v_name_1990_ = lean_ctor_get(v_opt_1989_, 0);
v_defValue_1991_ = lean_ctor_get(v_opt_1989_, 1);
v_map_1992_ = lean_ctor_get(v_opts_1988_, 0);
v___x_1993_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1992_, v_name_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_inc(v_defValue_1991_);
return v_defValue_1991_;
}
else
{
lean_object* v_val_1994_; 
v_val_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_val_1994_) == 3)
{
lean_object* v_v_1995_; 
v_v_1995_ = lean_ctor_get(v_val_1994_, 0);
lean_inc(v_v_1995_);
lean_dec_ref_known(v_val_1994_, 1);
return v_v_1995_;
}
else
{
lean_dec(v_val_1994_);
lean_inc(v_defValue_1991_);
return v_defValue_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_opts_1996_, lean_object* v_opt_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_opts_1996_, v_opt_1997_);
lean_dec_ref(v_opt_1997_);
lean_dec_ref(v_opts_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_options_2003_; lean_object* v___x_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v_options_2003_ = lean_ctor_get(v_c_1999_, 6);
lean_inc_ref(v_options_2003_);
lean_dec_ref(v_c_1999_);
v___x_2004_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_2003_, v___y_2001_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2009_ = l_Lean_linter_doc_deferred;
v___x_2010_ = l_Lean_Linter_getLinterValue(v___x_2009_, v_a_2005_);
lean_dec(v_a_2005_);
v___x_2011_ = lean_box(v___x_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2021_, lean_object* v_docCheckedModules_2022_, uint8_t v___y_2023_, lean_object* v_m_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2021_, v_m_2024_);
if (v___x_2025_ == 0)
{
return v___x_2025_;
}
else
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_NameSet_contains(v_docCheckedModules_2022_, v_m_2024_);
if (v___x_2026_ == 0)
{
return v___y_2023_;
}
else
{
uint8_t v___x_2027_; 
v___x_2027_ = 0;
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2028_, lean_object* v_docCheckedModules_2029_, lean_object* v___y_2030_, lean_object* v_m_2031_){
_start:
{
uint8_t v___y_7063__boxed_2032_; uint8_t v_res_2033_; lean_object* v_r_2034_; 
v___y_7063__boxed_2032_ = lean_unbox(v___y_2030_);
v_res_2033_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2028_, v_docCheckedModules_2029_, v___y_7063__boxed_2032_, v_m_2031_);
lean_dec(v_m_2031_);
lean_dec(v_docCheckedModules_2029_);
lean_dec(v_pkgRoot_2028_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(uint8_t v___x_2042_, lean_object* v_sp_2043_, lean_object* v_as_2044_, size_t v_sz_2045_, size_t v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_a_2052_; uint8_t v_unlocated_2056_; 
v_unlocated_2056_ = lean_usize_dec_lt(v_i_2046_, v_sz_2045_);
if (v_unlocated_2056_ == 0)
{
lean_object* v___x_2057_; 
lean_dec(v_sp_2043_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_b_2047_);
return v___x_2057_;
}
else
{
lean_object* v_a_2058_; lean_object* v_snd_2059_; lean_object* v_fst_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2189_; 
v_a_2058_ = lean_array_uget_borrowed(v_as_2044_, v_i_2046_);
v_snd_2059_ = lean_ctor_get(v_a_2058_, 1);
lean_inc(v_snd_2059_);
v_fst_2060_ = lean_ctor_get(v_snd_2059_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_snd_2059_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v_snd_2059_, 1);
lean_dec(v_unused_2190_);
v___x_2062_ = v_snd_2059_;
v_isShared_2063_ = v_isSharedCheck_2189_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_fst_2060_);
lean_dec(v_snd_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2189_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_fst_2064_; lean_object* v_site_2065_; lean_object* v___x_2066_; 
v_fst_2064_ = lean_ctor_get(v_a_2058_, 0);
v_site_2065_ = lean_ctor_get(v_fst_2060_, 0);
lean_inc_ref_n(v_site_2065_, 2);
lean_dec(v_fst_2060_);
v___x_2066_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2064_, v_site_2065_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
if (lean_obj_tag(v_a_2067_) == 0)
{
lean_object* v_fst_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2107_; 
v_fst_2068_ = lean_ctor_get(v_b_2047_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_b_2047_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_b_2047_, 1);
lean_dec(v_unused_2108_);
v___x_2070_ = v_b_2047_;
v_isShared_2071_ = v_isSharedCheck_2107_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_fst_2068_);
lean_dec(v_b_2047_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2107_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v_name_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2072_ = l_Lean_linter_doc_deferred;
v_name_2073_ = lean_ctor_get(v___x_2072_, 0);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__0));
v___x_2075_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2065_);
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
lean_dec_ref(v___x_2075_);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__1));
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
lean_inc(v_fst_2064_);
v___x_2079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2064_, v___x_2042_);
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
lean_inc(v_name_2073_);
v___x_2083_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2073_, v___x_2042_);
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
v___x_2087_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_dec_ref_known(v___x_2087_, 1);
lean_del_object(v___x_2062_);
v___x_2088_ = lean_box(v_unlocated_2056_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2088_);
v___x_2090_ = v___x_2070_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_fst_2068_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_a_2052_ = v___x_2090_;
goto v___jp_2051_;
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2106_; 
lean_del_object(v___x_2070_);
lean_dec(v_fst_2068_);
lean_dec(v_sp_2043_);
v_a_2092_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2094_ = v___x_2087_;
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_ref_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_ref_2096_ = lean_ctor_get(v___y_2048_, 2);
v___x_2097_ = lean_io_error_to_string(v_a_2092_);
v___x_2098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = l_Lean_MessageData_ofFormat(v___x_2098_);
lean_inc(v_ref_2096_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2099_);
lean_ctor_set(v___x_2062_, 0, v_ref_2096_);
v___x_2101_ = v___x_2062_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_ref_2096_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2101_);
v___x_2103_ = v___x_2094_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_site_2065_);
v_fst_2109_ = lean_ctor_get(v_b_2047_, 0);
v_snd_2110_ = lean_ctor_get(v_b_2047_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_b_2047_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2112_ = v_b_2047_;
v_isShared_2113_ = v_isSharedCheck_2180_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_inc(v_fst_2109_);
lean_dec(v_b_2047_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2180_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_val_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2179_; 
v_val_2114_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2116_ = v_a_2067_;
v_isShared_2117_ = v_isSharedCheck_2179_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_val_2114_);
lean_dec(v_a_2067_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2179_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2064_);
lean_inc(v_sp_2043_);
v___x_2119_ = l_Lean_SearchPath_findWithExt(v_sp_2043_, v___x_2118_, v_fst_2064_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
if (lean_obj_tag(v_a_2120_) == 0)
{
lean_object* v___x_2121_; lean_object* v_name_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_val_2114_);
lean_dec(v_snd_2110_);
v___x_2121_ = l_Lean_linter_doc_deferred;
v_name_2122_ = lean_ctor_get(v___x_2121_, 0);
v___x_2123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
lean_inc(v_fst_2064_);
v___x_2124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2064_, v___x_2042_);
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
lean_inc(v_name_2122_);
v___x_2128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2122_, v___x_2042_);
v___x_2129_ = lean_string_append(v___x_2127_, v___x_2128_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_2131_ = lean_string_append(v___x_2129_, v___x_2130_);
v___x_2132_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
lean_dec_ref_known(v___x_2132_, 1);
lean_del_object(v___x_2116_);
lean_del_object(v___x_2062_);
v___x_2133_ = lean_box(v_unlocated_2056_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2133_);
v___x_2135_ = v___x_2112_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_fst_2109_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v_a_2052_ = v___x_2135_;
goto v___jp_2051_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2112_);
lean_dec(v_fst_2109_);
lean_dec(v_sp_2043_);
v_a_2137_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2139_ = v___x_2132_;
v_isShared_2140_ = v_isSharedCheck_2153_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2153_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_ref_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v_ref_2141_ = lean_ctor_get(v___y_2048_, 2);
v___x_2142_ = lean_io_error_to_string(v_a_2137_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 3);
lean_ctor_set(v___x_2116_, 0, v___x_2142_);
v___x_2144_ = v___x_2116_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = l_Lean_MessageData_ofFormat(v___x_2144_);
lean_inc(v_ref_2141_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2145_);
lean_ctor_set(v___x_2062_, 0, v_ref_2141_);
v___x_2147_ = v___x_2062_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_ref_2141_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2147_);
v___x_2149_ = v___x_2139_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2155_; lean_object* v_name_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_del_object(v___x_2116_);
lean_del_object(v___x_2062_);
v_val_2154_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v_a_2120_, 1);
v___x_2155_ = l_Lean_linter_doc_deferred;
v_name_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_name_2156_);
v___x_2157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2157_, 0, v_val_2154_);
lean_ctor_set(v___x_2157_, 1, v_val_2114_);
lean_ctor_set(v___x_2157_, 2, v_name_2156_);
v___x_2158_ = lean_array_push(v_fst_2109_, v___x_2157_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2158_);
v___x_2160_ = v___x_2112_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_snd_2110_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
v_a_2052_ = v___x_2160_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_val_2114_);
lean_del_object(v___x_2112_);
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_dec(v_sp_2043_);
v_a_2162_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2164_ = v___x_2119_;
v_isShared_2165_ = v_isSharedCheck_2178_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2119_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2178_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_ref_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_ref_2166_ = lean_ctor_get(v___y_2048_, 2);
v___x_2167_ = lean_io_error_to_string(v_a_2162_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 3);
lean_ctor_set(v___x_2116_, 0, v___x_2167_);
v___x_2169_ = v___x_2116_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
lean_inc(v_ref_2166_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2170_);
lean_ctor_set(v___x_2062_, 0, v_ref_2166_);
v___x_2172_ = v___x_2062_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_ref_2166_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2172_);
v___x_2174_ = v___x_2164_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
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
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_site_2065_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_b_2047_);
lean_dec(v_sp_2043_);
v_a_2181_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2066_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2066_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
v___jp_2051_:
{
size_t v___x_2053_; size_t v___x_2054_; 
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2046_, v___x_2053_);
v_i_2046_ = v___x_2054_;
v_b_2047_ = v_a_2052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___boxed(lean_object* v___x_2191_, lean_object* v_sp_2192_, lean_object* v_as_2193_, lean_object* v_sz_2194_, lean_object* v_i_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_7087__boxed_2200_; size_t v_sz_boxed_2201_; size_t v_i_boxed_2202_; lean_object* v_res_2203_; 
v___x_7087__boxed_2200_ = lean_unbox(v___x_2191_);
v_sz_boxed_2201_ = lean_unbox_usize(v_sz_2194_);
lean_dec(v_sz_2194_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_7087__boxed_2200_, v_sp_2192_, v_as_2193_, v_sz_boxed_2201_, v_i_boxed_2202_, v_b_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_as_2193_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(lean_object* v_sp_2210_, uint8_t v___y_2211_, lean_object* v_as_2212_, size_t v_sz_2213_, size_t v_i_2214_, lean_object* v_b_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_a_2219_; uint8_t v___x_2223_; 
v___x_2223_ = lean_usize_dec_lt(v_i_2214_, v_sz_2213_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_dec(v_sp_2210_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2215_);
return v___x_2224_;
}
else
{
lean_object* v_a_2225_; lean_object* v_snd_2226_; lean_object* v_fst_2227_; lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2324_; 
v_a_2225_ = lean_array_uget_borrowed(v_as_2212_, v_i_2214_);
v_snd_2226_ = lean_ctor_get(v_a_2225_, 1);
lean_inc(v_snd_2226_);
v_fst_2227_ = lean_ctor_get(v_snd_2226_, 0);
lean_inc(v_fst_2227_);
v_fst_2228_ = lean_ctor_get(v_a_2225_, 0);
v_snd_2229_ = lean_ctor_get(v_snd_2226_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_snd_2226_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v_snd_2226_, 0);
lean_dec(v_unused_2325_);
v___x_2231_ = v_snd_2226_;
v_isShared_2232_ = v_isSharedCheck_2324_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_dec(v_snd_2226_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2324_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_site_2233_; lean_object* v_sourceString_2234_; lean_object* v___x_2235_; lean_object* v___y_2237_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_site_2233_ = lean_ctor_get(v_fst_2227_, 0);
lean_inc_ref(v_site_2233_);
v_sourceString_2234_ = lean_ctor_get(v_fst_2227_, 2);
lean_inc_ref(v_sourceString_2234_);
lean_dec(v_fst_2227_);
v___x_2235_ = lean_box(0);
v___x_2316_ = lean_string_utf8_byte_size(v_sourceString_2234_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_nat_dec_eq(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__4));
v___x_2320_ = lean_string_append(v___x_2319_, v_sourceString_2234_);
lean_dec_ref(v_sourceString_2234_);
v___x_2321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__5));
v___x_2322_ = lean_string_append(v___x_2320_, v___x_2321_);
v___y_2237_ = v___x_2322_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2323_; 
lean_dec_ref(v_sourceString_2234_);
v___x_2323_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2237_ = v___x_2323_;
goto v___jp_2236_;
}
v___jp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v_fst_2228_);
lean_inc(v_sp_2210_);
v___x_2239_ = l_Lean_SearchPath_findWithExt(v_sp_2210_, v___x_2238_, v_fst_2228_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
if (lean_obj_tag(v_a_2240_) == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2241_ = l_Lean_MessageData_toString(v_snd_2229_);
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__0));
lean_inc(v_fst_2228_);
v___x_2243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2228_, v___y_2211_);
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__1));
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
v___x_2247_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2233_);
v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = lean_string_append(v___x_2248_, v___y_2237_);
lean_dec_ref(v___y_2237_);
v___x_2250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2251_ = lean_string_append(v___x_2249_, v___x_2250_);
v___x_2252_ = lean_string_append(v___x_2251_, v___x_2241_);
lean_dec_ref(v___x_2241_);
v___x_2253_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_dec_ref_known(v___x_2253_, 1);
lean_del_object(v___x_2231_);
v_a_2219_ = v___x_2235_;
goto v___jp_2218_;
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_sp_2210_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2268_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2268_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_ref_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v_ref_2258_ = lean_ctor_get(v___y_2216_, 2);
v___x_2259_ = lean_io_error_to_string(v_a_2254_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_ofFormat(v___x_2260_);
lean_inc(v_ref_2258_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2261_);
lean_ctor_set(v___x_2231_, 0, v_ref_2258_);
v___x_2263_ = v___x_2231_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_ref_2258_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2263_);
v___x_2265_ = v___x_2256_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2300_; 
v_val_2269_ = lean_ctor_get(v_a_2240_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2271_ = v_a_2240_;
v_isShared_2272_ = v_isSharedCheck_2300_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_val_2269_);
lean_dec(v_a_2240_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2300_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2273_ = l_Lean_MessageData_toString(v_snd_2229_);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__3));
v___x_2275_ = lean_string_append(v_val_2269_, v___x_2274_);
v___x_2276_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2233_);
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_string_append(v___x_2277_, v___y_2237_);
lean_dec_ref(v___y_2237_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___closed__2));
v___x_2280_ = lean_string_append(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_string_append(v___x_2280_, v___x_2273_);
lean_dec_ref(v___x_2273_);
v___x_2282_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_dec_ref_known(v___x_2282_, 1);
lean_del_object(v___x_2271_);
lean_del_object(v___x_2231_);
v_a_2219_ = v___x_2235_;
goto v___jp_2218_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_sp_2210_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2299_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2299_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_ref_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v_ref_2287_ = lean_ctor_get(v___y_2216_, 2);
v___x_2288_ = lean_io_error_to_string(v_a_2283_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2288_);
v___x_2290_ = v___x_2271_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = l_Lean_MessageData_ofFormat(v___x_2290_);
lean_inc(v_ref_2287_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2291_);
lean_ctor_set(v___x_2231_, 0, v_ref_2287_);
v___x_2293_ = v___x_2231_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_ref_2287_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2295_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2293_);
v___x_2295_ = v___x_2285_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
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
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_site_2233_);
lean_dec(v_snd_2229_);
lean_dec(v_sp_2210_);
v_a_2301_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2303_ = v___x_2239_;
v_isShared_2304_ = v_isSharedCheck_2315_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2239_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2315_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_ref_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v_ref_2305_ = lean_ctor_get(v___y_2216_, 2);
v___x_2306_ = lean_io_error_to_string(v_a_2301_);
v___x_2307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
lean_inc(v_ref_2305_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2308_);
lean_ctor_set(v___x_2231_, 0, v_ref_2305_);
v___x_2310_ = v___x_2231_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_ref_2305_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2310_);
v___x_2312_ = v___x_2303_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
}
v___jp_2218_:
{
size_t v___x_2220_; size_t v___x_2221_; 
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_add(v_i_2214_, v___x_2220_);
v_i_2214_ = v___x_2221_;
v_b_2215_ = v_a_2219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg___boxed(lean_object* v_sp_2326_, lean_object* v___y_2327_, lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v___y_7379__boxed_2334_; size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v___y_7379__boxed_2334_ = lean_unbox(v___y_2327_);
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2326_, v___y_7379__boxed_2334_, v_as_2328_, v_sz_boxed_2335_, v_i_boxed_2336_, v_b_2331_, v___y_2332_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_as_2328_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2338_, lean_object* v_as_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_b_2342_){
_start:
{
lean_object* v_a_2345_; uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_lt(v_i_2341_, v_sz_2340_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_b_2342_);
return v___x_2350_;
}
else
{
lean_object* v_a_2351_; uint8_t v___x_2352_; 
v_a_2351_ = lean_array_uget_borrowed(v_as_2339_, v_i_2341_);
v___x_2352_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2338_, v_a_2351_);
if (v___x_2352_ == 0)
{
v_a_2345_ = v_b_2342_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2353_; 
lean_inc(v_a_2351_);
v___x_2353_ = l_Lean_NameSet_insert(v_b_2342_, v_a_2351_);
v_a_2345_ = v___x_2353_;
goto v___jp_2344_;
}
}
v___jp_2344_:
{
size_t v___x_2346_; size_t v___x_2347_; 
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_add(v_i_2341_, v___x_2346_);
v_i_2341_ = v___x_2347_;
v_b_2342_ = v_a_2345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_){
_start:
{
size_t v_sz_boxed_2360_; size_t v_i_boxed_2361_; lean_object* v_res_2362_; 
v_sz_boxed_2360_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2361_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2354_, v_as_2355_, v_sz_boxed_2360_, v_i_boxed_2361_, v_b_2358_);
lean_dec_ref(v_as_2355_);
lean_dec(v_pkgRoot_2354_);
return v_res_2362_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = lean_unsigned_to_nat(32u);
v___x_2370_ = lean_mk_empty_array_with_capacity(v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
size_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2372_ = ((size_t)5ULL);
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2374_ = lean_unsigned_to_nat(32u);
v___x_2375_ = lean_mk_empty_array_with_capacity(v___x_2374_);
v___x_2376_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2377_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2375_);
lean_ctor_set(v___x_2377_, 2, v___x_2373_);
lean_ctor_set(v___x_2377_, 3, v___x_2373_);
lean_ctor_set_usize(v___x_2377_, 4, v___x_2372_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = l_Lean_NameSet_empty;
v___x_2384_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_ctor_set(v___x_2385_, 2, v___x_2383_);
return v___x_2385_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = l_Lean_firstFrontendMacroScope;
v___x_2388_ = lean_nat_add(v___x_2387_, v___x_2386_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2399_; uint64_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2400_ = 0ULL;
v___x_2401_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint64(v___x_2401_, sizeof(void*)*1, v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v_unlocated_2404_; lean_object* v___x_2405_; 
v___x_2402_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2403_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8);
v_unlocated_2404_ = 1;
v___x_2405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2403_);
lean_ctor_set(v___x_2405_, 2, v___x_2402_);
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*3, v_unlocated_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = l_Lean_Options_empty;
v___x_2409_ = l_Lean_Core_getMaxHeartbeats(v___x_2408_);
return v___x_2409_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2410_ = l_Lean_diagnostics;
v___x_2411_ = l_Lean_Options_empty;
v___x_2412_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2413_, lean_object* v_linterOpts_2414_, lean_object* v_sp_2415_, lean_object* v_env_2416_, lean_object* v_pkgRoot_2417_, lean_object* v_docCheckedModules_2418_){
_start:
{
lean_object* v___y_2421_; lean_object* v_a_2422_; lean_object* v___y_2447_; uint8_t v___y_2448_; lean_object* v___y_2451_; lean_object* v_a_2455_; uint8_t v___y_2459_; lean_object* v_a_2460_; uint8_t v_lintOnly_2476_; uint8_t v_mode_2477_; lean_object* v___f_2478_; lean_object* v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2482_; uint8_t v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; uint8_t v___y_2486_; lean_object* v_fileName_2487_; lean_object* v_fileMap_2488_; lean_object* v_currNamespace_2489_; lean_object* v_openDecls_2490_; lean_object* v_initHeartbeats_2491_; lean_object* v_maxHeartbeats_2492_; lean_object* v_quotContext_2493_; lean_object* v_currMacroScope_2494_; lean_object* v_cancelTk_x3f_2495_; lean_object* v_inheritedTraceOptions_2496_; lean_object* v_currRecDepth_2497_; lean_object* v_ref_2498_; uint8_t v_suppressElabErrors_2499_; lean_object* v___y_2500_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; uint8_t v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___y_2562_; uint8_t v___y_2563_; uint8_t v___y_2584_; 
v_lintOnly_2476_ = lean_ctor_get_uint8(v_args_2413_, sizeof(void*)*4);
v_mode_2477_ = lean_ctor_get_uint8(v_args_2413_, sizeof(void*)*4 + 1);
v___f_2478_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2476_ == 0)
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = l_Lean_linter_doc_deferred;
v___x_2624_ = l_Lean_Linter_getLinterValue(v___x_2623_, v_linterOpts_2414_);
v___y_2584_ = v___x_2624_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2625_; lean_object* v_name_2626_; uint8_t v___x_2627_; 
v___x_2625_ = l_Lean_linter_doc_deferred;
v_name_2626_ = lean_ctor_get(v___x_2625_, 0);
v___x_2627_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2626_, v_linterOpts_2414_);
v___y_2584_ = v___x_2627_;
goto v___jp_2583_;
}
v___jp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; size_t v_sz_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2423_ = lean_st_ref_get(v___y_2421_);
lean_dec(v___y_2421_);
lean_dec(v___x_2423_);
v___x_2424_ = l_Lean_Environment_header(v_env_2416_);
lean_dec_ref(v_env_2416_);
v___x_2425_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2424_);
v_sz_2426_ = lean_array_size(v___x_2425_);
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2417_, v___x_2425_, v_sz_2426_, v___x_2427_, v_docCheckedModules_2418_);
lean_dec_ref(v___x_2425_);
lean_dec(v_pkgRoot_2417_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2422_);
lean_ctor_set(v___x_2433_, 1, v_a_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec_ref(v_a_2422_);
v_a_2438_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2428_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2428_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2449_, 0, v___y_2448_);
v___y_2421_ = v___y_2447_;
v_a_2422_ = v___x_2449_;
goto v___jp_2420_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2451_);
lean_ctor_set(v___x_2452_, 1, v_docCheckedModules_2418_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_mk_io_user_error(v_a_2455_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
v___jp_2458_:
{
if (lean_obj_tag(v_a_2460_) == 0)
{
lean_object* v_msg_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_msg_2461_ = lean_ctor_get(v_a_2460_, 1);
lean_inc_ref(v_msg_2461_);
lean_dec_ref_known(v_a_2460_, 2);
v___x_2462_ = l_Lean_MessageData_toString(v_msg_2461_);
v___x_2463_ = lean_mk_io_user_error(v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
else
{
lean_object* v_id_2465_; lean_object* v___x_2466_; 
v_id_2465_ = lean_ctor_get(v_a_2460_, 0);
lean_inc(v_id_2465_);
lean_dec_ref_known(v_a_2460_, 2);
v___x_2466_ = l_Lean_InternalExceptionId_getName(v_id_2465_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v_id_2465_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2469_ = l_Lean_Name_toString(v_a_2467_, v___y_2459_);
v___x_2470_ = lean_string_append(v___x_2468_, v___x_2469_);
lean_dec_ref(v___x_2469_);
v_a_2455_ = v___x_2470_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec_ref_known(v___x_2466_, 1);
v___x_2471_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2472_ = l_Nat_reprFast(v_id_2465_);
v___x_2473_ = lean_string_append(v___x_2471_, v___x_2472_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
v_a_2455_ = v___x_2475_;
goto v___jp_2454_;
}
}
}
v___jp_2479_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2501_ = l_Lean_maxRecDepth;
v___x_2502_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___y_2484_, v___x_2501_);
lean_inc_ref(v___y_2484_);
v___x_2503_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2503_, 0, v_fileName_2487_);
lean_ctor_set(v___x_2503_, 1, v_fileMap_2488_);
lean_ctor_set(v___x_2503_, 2, v___y_2484_);
lean_ctor_set(v___x_2503_, 3, v___x_2502_);
lean_ctor_set(v___x_2503_, 4, v_currNamespace_2489_);
lean_ctor_set(v___x_2503_, 5, v_openDecls_2490_);
lean_ctor_set(v___x_2503_, 6, v_initHeartbeats_2491_);
lean_ctor_set(v___x_2503_, 7, v_maxHeartbeats_2492_);
lean_ctor_set(v___x_2503_, 8, v_quotContext_2493_);
lean_ctor_set(v___x_2503_, 9, v_currMacroScope_2494_);
lean_ctor_set(v___x_2503_, 10, v_cancelTk_x3f_2495_);
lean_ctor_set(v___x_2503_, 11, v_inheritedTraceOptions_2496_);
v___x_2504_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v_currRecDepth_2497_);
lean_ctor_set(v___x_2504_, 2, v_ref_2498_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*3, v___y_2486_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*3 + 1, v_suppressElabErrors_2499_);
v___x_2505_ = l_Lean_Doc_DeferredCheck_run(v___y_2485_, v___f_2478_, v___x_2504_, v___y_2500_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; uint8_t v___x_2507_; uint8_t v___x_2508_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = 1;
v___x_2508_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2477_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; size_t v_sz_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v___y_2500_);
v___x_2509_ = lean_box(0);
v_sz_2510_ = lean_array_size(v_a_2506_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2415_, v___y_2483_, v_a_2506_, v_sz_2510_, v___x_2511_, v___x_2509_, v___x_2504_);
lean_dec_ref_known(v___x_2504_, 3);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
lean_dec_ref_known(v___x_2512_, 1);
v___x_2513_ = lean_array_get_size(v_a_2506_);
lean_dec(v_a_2506_);
v___x_2514_ = lean_nat_dec_eq(v___x_2513_, v___y_2480_);
lean_dec(v___y_2480_);
if (v___x_2514_ == 0)
{
v___y_2447_ = v___y_2481_;
v___y_2448_ = v___y_2483_;
goto v___jp_2446_;
}
else
{
v___y_2447_ = v___y_2481_;
v___y_2448_ = v___x_2508_;
goto v___jp_2446_;
}
}
else
{
lean_object* v_a_2515_; 
lean_dec(v_a_2506_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2418_);
lean_dec(v_pkgRoot_2417_);
lean_dec_ref(v_env_2416_);
v_a_2515_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2512_, 1);
v___y_2459_ = v___y_2483_;
v_a_2460_ = v_a_2515_;
goto v___jp_2458_;
}
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2516_ = lean_mk_empty_array_with_capacity(v___y_2480_);
lean_dec(v___y_2480_);
v___x_2517_ = lean_box(v___y_2482_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v_sz_2519_ = lean_array_size(v_a_2506_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5(v___x_2508_, v_sp_2415_, v_a_2506_, v_sz_2519_, v___x_2520_, v___x_2518_, v___x_2504_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref_known(v___x_2504_, 3);
lean_dec(v_a_2506_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v_fst_2523_; lean_object* v_snd_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v_fst_2523_ = lean_ctor_get(v_a_2522_, 0);
lean_inc(v_fst_2523_);
v_snd_2524_ = lean_ctor_get(v_a_2522_, 1);
lean_inc(v_snd_2524_);
lean_dec(v_a_2522_);
v___x_2525_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2525_, 0, v_fst_2523_);
v___x_2526_ = lean_unbox(v_snd_2524_);
lean_dec(v_snd_2524_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1, v___x_2526_);
v___y_2421_ = v___y_2481_;
v_a_2422_ = v___x_2525_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2527_; 
lean_dec(v___y_2481_);
lean_dec(v_docCheckedModules_2418_);
lean_dec(v_pkgRoot_2417_);
lean_dec_ref(v_env_2416_);
v_a_2527_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2521_, 1);
v___y_2459_ = v___y_2483_;
v_a_2460_ = v_a_2527_;
goto v___jp_2458_;
}
}
}
else
{
lean_object* v_a_2528_; 
lean_dec_ref_known(v___x_2504_, 3);
lean_dec(v___y_2500_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec(v_docCheckedModules_2418_);
lean_dec(v_pkgRoot_2417_);
lean_dec_ref(v_env_2416_);
lean_dec(v_sp_2415_);
v_a_2528_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2505_, 1);
v___y_2459_ = v___y_2483_;
v_a_2460_ = v_a_2528_;
goto v___jp_2458_;
}
}
v___jp_2529_:
{
lean_object* v_toCold_2539_; lean_object* v_currRecDepth_2540_; lean_object* v_ref_2541_; uint8_t v_suppressElabErrors_2542_; lean_object* v_fileName_2543_; lean_object* v_fileMap_2544_; lean_object* v_currNamespace_2545_; lean_object* v_openDecls_2546_; lean_object* v_initHeartbeats_2547_; lean_object* v_maxHeartbeats_2548_; lean_object* v_quotContext_2549_; lean_object* v_currMacroScope_2550_; lean_object* v_cancelTk_x3f_2551_; lean_object* v_inheritedTraceOptions_2552_; 
v_toCold_2539_ = lean_ctor_get(v___y_2537_, 0);
lean_inc_ref(v_toCold_2539_);
v_currRecDepth_2540_ = lean_ctor_get(v___y_2537_, 1);
lean_inc(v_currRecDepth_2540_);
v_ref_2541_ = lean_ctor_get(v___y_2537_, 2);
lean_inc(v_ref_2541_);
v_suppressElabErrors_2542_ = lean_ctor_get_uint8(v___y_2537_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_2537_);
v_fileName_2543_ = lean_ctor_get(v_toCold_2539_, 0);
lean_inc_ref(v_fileName_2543_);
v_fileMap_2544_ = lean_ctor_get(v_toCold_2539_, 1);
lean_inc_ref(v_fileMap_2544_);
v_currNamespace_2545_ = lean_ctor_get(v_toCold_2539_, 4);
lean_inc(v_currNamespace_2545_);
v_openDecls_2546_ = lean_ctor_get(v_toCold_2539_, 5);
lean_inc(v_openDecls_2546_);
v_initHeartbeats_2547_ = lean_ctor_get(v_toCold_2539_, 6);
lean_inc(v_initHeartbeats_2547_);
v_maxHeartbeats_2548_ = lean_ctor_get(v_toCold_2539_, 7);
lean_inc(v_maxHeartbeats_2548_);
v_quotContext_2549_ = lean_ctor_get(v_toCold_2539_, 8);
lean_inc(v_quotContext_2549_);
v_currMacroScope_2550_ = lean_ctor_get(v_toCold_2539_, 9);
lean_inc(v_currMacroScope_2550_);
v_cancelTk_x3f_2551_ = lean_ctor_get(v_toCold_2539_, 10);
lean_inc(v_cancelTk_x3f_2551_);
v_inheritedTraceOptions_2552_ = lean_ctor_get(v_toCold_2539_, 11);
lean_inc_ref(v_inheritedTraceOptions_2552_);
lean_dec_ref(v_toCold_2539_);
v___y_2480_ = v___y_2530_;
v___y_2481_ = v___y_2531_;
v___y_2482_ = v___y_2532_;
v___y_2483_ = v___y_2533_;
v___y_2484_ = v___y_2534_;
v___y_2485_ = v___y_2535_;
v___y_2486_ = v___y_2536_;
v_fileName_2487_ = v_fileName_2543_;
v_fileMap_2488_ = v_fileMap_2544_;
v_currNamespace_2489_ = v_currNamespace_2545_;
v_openDecls_2490_ = v_openDecls_2546_;
v_initHeartbeats_2491_ = v_initHeartbeats_2547_;
v_maxHeartbeats_2492_ = v_maxHeartbeats_2548_;
v_quotContext_2493_ = v_quotContext_2549_;
v_currMacroScope_2494_ = v_currMacroScope_2550_;
v_cancelTk_x3f_2495_ = v_cancelTk_x3f_2551_;
v_inheritedTraceOptions_2496_ = v_inheritedTraceOptions_2552_;
v_currRecDepth_2497_ = v_currRecDepth_2540_;
v_ref_2498_ = v_ref_2541_;
v_suppressElabErrors_2499_ = v_suppressElabErrors_2542_;
v___y_2500_ = v___y_2538_;
goto v___jp_2479_;
}
v___jp_2553_:
{
if (v___y_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v_env_2565_; lean_object* v_nextMacroScope_2566_; lean_object* v_ngen_2567_; lean_object* v_auxDeclNGen_2568_; lean_object* v_traceState_2569_; lean_object* v_messages_2570_; lean_object* v_infoState_2571_; lean_object* v_snapshotTasks_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2581_; 
v___x_2564_ = lean_st_ref_take(v___y_2555_);
v_env_2565_ = lean_ctor_get(v___x_2564_, 0);
v_nextMacroScope_2566_ = lean_ctor_get(v___x_2564_, 1);
v_ngen_2567_ = lean_ctor_get(v___x_2564_, 2);
v_auxDeclNGen_2568_ = lean_ctor_get(v___x_2564_, 3);
v_traceState_2569_ = lean_ctor_get(v___x_2564_, 4);
v_messages_2570_ = lean_ctor_get(v___x_2564_, 6);
v_infoState_2571_ = lean_ctor_get(v___x_2564_, 7);
v_snapshotTasks_2572_ = lean_ctor_get(v___x_2564_, 8);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2564_, 5);
lean_dec(v_unused_2582_);
v___x_2574_ = v___x_2564_;
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snapshotTasks_2572_);
lean_inc(v_infoState_2571_);
lean_inc(v_messages_2570_);
lean_inc(v_traceState_2569_);
lean_inc(v_auxDeclNGen_2568_);
lean_inc(v_ngen_2567_);
lean_inc(v_nextMacroScope_2566_);
lean_inc(v_env_2565_);
lean_dec(v___x_2564_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = l_Lean_Kernel_enableDiag(v_env_2565_, v___y_2562_);
lean_inc_ref(v___y_2559_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 5, v___y_2559_);
lean_ctor_set(v___x_2574_, 0, v___x_2576_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_nextMacroScope_2566_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_ngen_2567_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_auxDeclNGen_2568_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_traceState_2569_);
lean_ctor_set(v_reuseFailAlloc_2580_, 5, v___y_2559_);
lean_ctor_set(v_reuseFailAlloc_2580_, 6, v_messages_2570_);
lean_ctor_set(v_reuseFailAlloc_2580_, 7, v_infoState_2571_);
lean_ctor_set(v_reuseFailAlloc_2580_, 8, v_snapshotTasks_2572_);
v___x_2578_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_st_ref_put(v___y_2555_, v___x_2578_);
lean_inc(v___y_2555_);
v___y_2530_ = v___y_2554_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v___y_2556_;
v___y_2534_ = v___y_2560_;
v___y_2535_ = v___y_2561_;
v___y_2536_ = v___y_2562_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2555_;
goto v___jp_2529_;
}
}
}
else
{
lean_inc(v___y_2555_);
v___y_2530_ = v___y_2554_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v___y_2556_;
v___y_2534_ = v___y_2560_;
v___y_2535_ = v___y_2561_;
v___y_2536_ = v___y_2562_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2555_;
goto v___jp_2529_;
}
}
v___jp_2583_:
{
if (v___y_2584_ == 0)
{
uint8_t v___x_2585_; uint8_t v___x_2586_; 
lean_dec(v_pkgRoot_2417_);
lean_dec_ref(v_env_2416_);
lean_dec(v_sp_2415_);
v___x_2585_ = 1;
v___x_2586_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2477_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2587_, 0, v___x_2586_);
v___y_2451_ = v___x_2587_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2589_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*1, v___y_2584_);
v___y_2451_ = v___x_2589_;
goto v___jp_2450_;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_env_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; uint8_t v___x_2621_; uint8_t v___x_2622_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_2592_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_2593_ = lean_io_get_num_heartbeats();
v___x_2594_ = l_Lean_firstFrontendMacroScope;
v___x_2595_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_2596_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_box(0);
v___x_2599_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_2600_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2601_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2602_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
lean_inc_ref(v_env_2416_);
v___x_2603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2603_, 0, v_env_2416_);
lean_ctor_set(v___x_2603_, 1, v___x_2595_);
lean_ctor_set(v___x_2603_, 2, v___x_2596_);
lean_ctor_set(v___x_2603_, 3, v___x_2599_);
lean_ctor_set(v___x_2603_, 4, v___x_2600_);
lean_ctor_set(v___x_2603_, 5, v___x_2591_);
lean_ctor_set(v___x_2603_, 6, v___x_2592_);
lean_ctor_set(v___x_2603_, 7, v___x_2601_);
lean_ctor_set(v___x_2603_, 8, v___x_2602_);
v___x_2604_ = lean_st_mk_ref(v___x_2603_);
v___x_2605_ = l_Lean_inheritedTraceOptions;
v___x_2606_ = lean_st_ref_get(v___x_2605_);
v___x_2607_ = lean_st_ref_get(v___x_2604_);
v___x_2608_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2609_ = l_Lean_instInhabitedFileMap_default;
v___x_2610_ = l_Lean_Options_empty;
v___x_2611_ = lean_unsigned_to_nat(1000u);
v___x_2612_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_box(0);
v___x_2615_ = 0;
lean_inc(v___x_2606_);
lean_inc(v___x_2593_);
v___x_2616_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2608_);
lean_ctor_set(v___x_2616_, 1, v___x_2609_);
lean_ctor_set(v___x_2616_, 2, v___x_2610_);
lean_ctor_set(v___x_2616_, 3, v___x_2611_);
lean_ctor_set(v___x_2616_, 4, v___x_2597_);
lean_ctor_set(v___x_2616_, 5, v___x_2598_);
lean_ctor_set(v___x_2616_, 6, v___x_2593_);
lean_ctor_set(v___x_2616_, 7, v___x_2612_);
lean_ctor_set(v___x_2616_, 8, v___x_2597_);
lean_ctor_set(v___x_2616_, 9, v___x_2594_);
lean_ctor_set(v___x_2616_, 10, v___x_2613_);
lean_ctor_set(v___x_2616_, 11, v___x_2606_);
v___x_2617_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2590_);
lean_ctor_set(v___x_2617_, 2, v___x_2614_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3, v___x_2615_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 1, v___x_2615_);
v_env_2618_ = lean_ctor_get(v___x_2607_, 0);
lean_inc_ref(v_env_2618_);
lean_dec(v___x_2607_);
v___x_2619_ = lean_box(v___y_2584_);
lean_inc(v_docCheckedModules_2418_);
lean_inc(v_pkgRoot_2417_);
v___f_2620_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2620_, 0, v_pkgRoot_2417_);
lean_closure_set(v___f_2620_, 1, v_docCheckedModules_2418_);
lean_closure_set(v___f_2620_, 2, v___x_2619_);
v___x_2621_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_2622_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2618_);
lean_dec_ref(v_env_2618_);
if (v___x_2621_ == 0)
{
if (v___x_2622_ == 0)
{
lean_dec_ref_known(v___x_2617_, 3);
lean_inc(v___x_2604_);
v___y_2480_ = v___x_2590_;
v___y_2481_ = v___x_2604_;
v___y_2482_ = v___x_2615_;
v___y_2483_ = v___y_2584_;
v___y_2484_ = v___x_2610_;
v___y_2485_ = v___f_2620_;
v___y_2486_ = v___x_2621_;
v_fileName_2487_ = v___x_2608_;
v_fileMap_2488_ = v___x_2609_;
v_currNamespace_2489_ = v___x_2597_;
v_openDecls_2490_ = v___x_2598_;
v_initHeartbeats_2491_ = v___x_2593_;
v_maxHeartbeats_2492_ = v___x_2612_;
v_quotContext_2493_ = v___x_2597_;
v_currMacroScope_2494_ = v___x_2594_;
v_cancelTk_x3f_2495_ = v___x_2613_;
v_inheritedTraceOptions_2496_ = v___x_2606_;
v_currRecDepth_2497_ = v___x_2590_;
v_ref_2498_ = v___x_2614_;
v_suppressElabErrors_2499_ = v___x_2615_;
v___y_2500_ = v___x_2604_;
goto v___jp_2479_;
}
else
{
lean_dec(v___x_2606_);
lean_dec(v___x_2593_);
v___y_2554_ = v___x_2590_;
v___y_2555_ = v___x_2604_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___x_2615_;
v___y_2558_ = v___x_2617_;
v___y_2559_ = v___x_2591_;
v___y_2560_ = v___x_2610_;
v___y_2561_ = v___f_2620_;
v___y_2562_ = v___x_2621_;
v___y_2563_ = v___x_2621_;
goto v___jp_2553_;
}
}
else
{
lean_dec(v___x_2606_);
lean_dec(v___x_2593_);
v___y_2554_ = v___x_2590_;
v___y_2555_ = v___x_2604_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___x_2615_;
v___y_2558_ = v___x_2617_;
v___y_2559_ = v___x_2591_;
v___y_2560_ = v___x_2610_;
v___y_2561_ = v___f_2620_;
v___y_2562_ = v___x_2621_;
v___y_2563_ = v___x_2622_;
goto v___jp_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2628_, lean_object* v_linterOpts_2629_, lean_object* v_sp_2630_, lean_object* v_env_2631_, lean_object* v_pkgRoot_2632_, lean_object* v_docCheckedModules_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2628_, v_linterOpts_2629_, v_sp_2630_, v_env_2631_, v_pkgRoot_2632_, v_docCheckedModules_2633_);
lean_dec_ref(v_linterOpts_2629_);
lean_dec_ref(v_args_2628_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(lean_object* v_sp_2636_, uint8_t v___y_2637_, lean_object* v_as_2638_, size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___redArg(v_sp_2636_, v___y_2637_, v_as_2638_, v_sz_2639_, v_i_2640_, v_b_2641_, v___y_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v_sp_2646_, lean_object* v___y_2647_, lean_object* v_as_2648_, lean_object* v_sz_2649_, lean_object* v_i_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___y_8112__boxed_2655_; size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v___y_8112__boxed_2655_ = lean_unbox(v___y_2647_);
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2649_);
lean_dec(v_sz_2649_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2650_);
lean_dec(v_i_2650_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v_sp_2646_, v___y_8112__boxed_2655_, v_as_2648_, v_sz_boxed_2656_, v_i_boxed_2657_, v_b_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v_as_2648_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2659_, lean_object* v_as_2660_, size_t v_i_2661_, size_t v_stop_2662_, lean_object* v_b_2663_){
_start:
{
lean_object* v___y_2665_; uint8_t v___x_2669_; 
v___x_2669_ = lean_usize_dec_eq(v_i_2661_, v_stop_2662_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v_linter_2671_; uint8_t v___x_2672_; 
v___x_2670_ = lean_array_uget_borrowed(v_as_2660_, v_i_2661_);
v_linter_2671_ = lean_ctor_get(v___x_2670_, 0);
v___x_2672_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2671_, v_linterOpts_2659_);
if (v___x_2672_ == 0)
{
v___y_2665_ = v_b_2663_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2673_; 
lean_inc(v___x_2670_);
v___x_2673_ = lean_array_push(v_b_2663_, v___x_2670_);
v___y_2665_ = v___x_2673_;
goto v___jp_2664_;
}
}
else
{
return v_b_2663_;
}
v___jp_2664_:
{
size_t v___x_2666_; size_t v___x_2667_; 
v___x_2666_ = ((size_t)1ULL);
v___x_2667_ = lean_usize_add(v_i_2661_, v___x_2666_);
v_i_2661_ = v___x_2667_;
v_b_2663_ = v___y_2665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2674_, lean_object* v_as_2675_, lean_object* v_i_2676_, lean_object* v_stop_2677_, lean_object* v_b_2678_){
_start:
{
size_t v_i_boxed_2679_; size_t v_stop_boxed_2680_; lean_object* v_res_2681_; 
v_i_boxed_2679_ = lean_unbox_usize(v_i_2676_);
lean_dec(v_i_2676_);
v_stop_boxed_2680_ = lean_unbox_usize(v_stop_2677_);
lean_dec(v_stop_2677_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2674_, v_as_2675_, v_i_boxed_2679_, v_stop_boxed_2680_, v_b_2678_);
lean_dec_ref(v_as_2675_);
lean_dec_ref(v_linterOpts_2674_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2684_, lean_object* v_as_2685_, size_t v_i_2686_, size_t v_stop_2687_, lean_object* v_b_2688_){
_start:
{
lean_object* v___y_2690_; uint8_t v___x_2694_; 
v___x_2694_ = lean_usize_dec_eq(v_i_2686_, v_stop_2687_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v_fst_2696_; lean_object* v_snd_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2721_; 
v___x_2695_ = lean_array_uget(v_as_2685_, v_i_2686_);
v_fst_2696_ = lean_ctor_get(v___x_2695_, 0);
v_snd_2697_ = lean_ctor_get(v___x_2695_, 1);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2699_ = v___x_2695_;
v_isShared_2700_ = v_isSharedCheck_2721_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_snd_2697_);
lean_inc(v_fst_2696_);
lean_dec(v___x_2695_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2721_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___y_2702_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = lean_array_get_size(v_snd_2697_);
v___x_2712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2713_ = lean_nat_dec_lt(v___x_2710_, v___x_2711_);
if (v___x_2713_ == 0)
{
lean_dec(v_snd_2697_);
v___y_2702_ = v___x_2712_;
goto v___jp_2701_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_nat_dec_le(v___x_2711_, v___x_2711_);
if (v___x_2714_ == 0)
{
if (v___x_2713_ == 0)
{
lean_dec(v_snd_2697_);
v___y_2702_ = v___x_2712_;
goto v___jp_2701_;
}
else
{
size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = ((size_t)0ULL);
v___x_2716_ = lean_usize_of_nat(v___x_2711_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2684_, v_snd_2697_, v___x_2715_, v___x_2716_, v___x_2712_);
lean_dec(v_snd_2697_);
v___y_2702_ = v___x_2717_;
goto v___jp_2701_;
}
}
else
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)0ULL);
v___x_2719_ = lean_usize_of_nat(v___x_2711_);
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2684_, v_snd_2697_, v___x_2718_, v___x_2719_, v___x_2712_);
lean_dec(v_snd_2697_);
v___y_2702_ = v___x_2720_;
goto v___jp_2701_;
}
}
v___jp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2703_ = lean_array_get_size(v___y_2702_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_nat_dec_eq(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2707_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___y_2702_);
v___x_2707_ = v___x_2699_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_fst_2696_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___y_2702_);
v___x_2707_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_array_push(v_b_2688_, v___x_2707_);
v___y_2690_ = v___x_2708_;
goto v___jp_2689_;
}
}
else
{
lean_dec_ref(v___y_2702_);
lean_del_object(v___x_2699_);
lean_dec(v_fst_2696_);
v___y_2690_ = v_b_2688_;
goto v___jp_2689_;
}
}
}
}
else
{
return v_b_2688_;
}
v___jp_2689_:
{
size_t v___x_2691_; size_t v___x_2692_; 
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2686_, v___x_2691_);
v_i_2686_ = v___x_2692_;
v_b_2688_ = v___y_2690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2722_, lean_object* v_as_2723_, lean_object* v_i_2724_, lean_object* v_stop_2725_, lean_object* v_b_2726_){
_start:
{
size_t v_i_boxed_2727_; size_t v_stop_boxed_2728_; lean_object* v_res_2729_; 
v_i_boxed_2727_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_stop_boxed_2728_ = lean_unbox_usize(v_stop_2725_);
lean_dec(v_stop_2725_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2722_, v_as_2723_, v_i_boxed_2727_, v_stop_boxed_2728_, v_b_2726_);
lean_dec_ref(v_as_2723_);
lean_dec_ref(v_linterOpts_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2730_, lean_object* v_as_2731_, lean_object* v_start_2732_, lean_object* v_stop_2733_){
_start:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2735_ = lean_nat_dec_lt(v_start_2732_, v_stop_2733_);
if (v___x_2735_ == 0)
{
return v___x_2734_;
}
else
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = lean_array_get_size(v_as_2731_);
v___x_2737_ = lean_nat_dec_le(v_stop_2733_, v___x_2736_);
if (v___x_2737_ == 0)
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_nat_dec_lt(v_start_2732_, v___x_2736_);
if (v___x_2738_ == 0)
{
return v___x_2734_;
}
else
{
size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_usize_of_nat(v_start_2732_);
v___x_2740_ = lean_usize_of_nat(v___x_2736_);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2730_, v_as_2731_, v___x_2739_, v___x_2740_, v___x_2734_);
return v___x_2741_;
}
}
else
{
size_t v___x_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = lean_usize_of_nat(v_start_2732_);
v___x_2743_ = lean_usize_of_nat(v_stop_2733_);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2730_, v_as_2731_, v___x_2742_, v___x_2743_, v___x_2734_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2745_, lean_object* v_as_2746_, lean_object* v_start_2747_, lean_object* v_stop_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2745_, v_as_2746_, v_start_2747_, v_stop_2748_);
lean_dec(v_stop_2748_);
lean_dec(v_start_2747_);
lean_dec_ref(v_as_2746_);
lean_dec_ref(v_linterOpts_2745_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2750_, lean_object* v_init_2751_, lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
lean_object* v_k_2754_; lean_object* v_v_2755_; lean_object* v_l_2756_; lean_object* v_r_2757_; lean_object* v___x_2758_; lean_object* v_a_2759_; lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2774_; 
v_k_2754_ = lean_ctor_get(v_x_2752_, 1);
lean_inc(v_k_2754_);
v_v_2755_ = lean_ctor_get(v_x_2752_, 2);
lean_inc(v_v_2755_);
v_l_2756_ = lean_ctor_get(v_x_2752_, 3);
lean_inc(v_l_2756_);
v_r_2757_ = lean_ctor_get(v_x_2752_, 4);
lean_inc(v_r_2757_);
lean_dec_ref_known(v_x_2752_, 5);
lean_inc(v_fst_2750_);
v___x_2758_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2750_, v_init_2751_, v_l_2756_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v_a_2760_ = lean_ctor_get(v_a_2759_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2762_ = v_a_2759_;
v_isShared_2763_ = v_isSharedCheck_2774_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v_a_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2774_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v_anyUnlocated_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v_anyUnlocated_2764_ = 1;
v___x_2765_ = l_Lean_Name_toString(v_k_2754_, v_anyUnlocated_2764_);
lean_inc(v_fst_2750_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 0);
lean_ctor_set(v___x_2762_, 0, v_fst_2750_);
v___x_2767_ = v___x_2762_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_fst_2750_);
v___x_2767_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
double v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2768_ = lean_float_of_nat(v_v_2755_);
v___x_2769_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2765_);
lean_ctor_set(v___x_2770_, 1, v___x_2767_);
lean_ctor_set(v___x_2770_, 2, v___x_2769_);
v___x_2771_ = lean_array_push(v_a_2760_, v___x_2770_);
v_init_2751_ = v___x_2771_;
v_x_2752_ = v_r_2757_;
goto _start;
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec(v_fst_2750_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_init_2751_);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2777_, lean_object* v_init_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2777_, v_init_2778_, v_x_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2782_, lean_object* v_k_2783_, lean_object* v_fallback_2784_){
_start:
{
if (lean_obj_tag(v_t_2782_) == 0)
{
lean_object* v_k_2785_; lean_object* v_v_2786_; lean_object* v_l_2787_; lean_object* v_r_2788_; uint8_t v___x_2789_; 
v_k_2785_ = lean_ctor_get(v_t_2782_, 1);
v_v_2786_ = lean_ctor_get(v_t_2782_, 2);
v_l_2787_ = lean_ctor_get(v_t_2782_, 3);
v_r_2788_ = lean_ctor_get(v_t_2782_, 4);
v___x_2789_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2783_, v_k_2785_);
switch(v___x_2789_)
{
case 0:
{
v_t_2782_ = v_l_2787_;
goto _start;
}
case 1:
{
lean_inc(v_v_2786_);
return v_v_2786_;
}
default: 
{
v_t_2782_ = v_r_2788_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2784_);
return v_fallback_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2792_, lean_object* v_k_2793_, lean_object* v_fallback_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2792_, v_k_2793_, v_fallback_2794_);
lean_dec(v_fallback_2794_);
lean_dec(v_k_2793_);
lean_dec(v_t_2792_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2796_, size_t v_i_2797_, size_t v_stop_2798_, lean_object* v_b_2799_){
_start:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_eq(v_i_2797_, v_stop_2798_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v_linter_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; 
v___x_2801_ = lean_array_uget_borrowed(v_as_2796_, v_i_2797_);
v_linter_2802_ = lean_ctor_get(v___x_2801_, 0);
v___x_2803_ = lean_unsigned_to_nat(0u);
v___x_2804_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2799_, v_linter_2802_, v___x_2803_);
v___x_2805_ = lean_unsigned_to_nat(1u);
v___x_2806_ = lean_nat_add(v___x_2804_, v___x_2805_);
lean_dec(v___x_2804_);
lean_inc(v_linter_2802_);
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2802_, v___x_2806_, v_b_2799_);
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2797_, v___x_2808_);
v_i_2797_ = v___x_2809_;
v_b_2799_ = v___x_2807_;
goto _start;
}
else
{
return v_b_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2811_, lean_object* v_i_2812_, lean_object* v_stop_2813_, lean_object* v_b_2814_){
_start:
{
size_t v_i_boxed_2815_; size_t v_stop_boxed_2816_; lean_object* v_res_2817_; 
v_i_boxed_2815_ = lean_unbox_usize(v_i_2812_);
lean_dec(v_i_2812_);
v_stop_boxed_2816_ = lean_unbox_usize(v_stop_2813_);
lean_dec(v_stop_2813_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2811_, v_i_boxed_2815_, v_stop_boxed_2816_, v_b_2814_);
lean_dec_ref(v_as_2811_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2818_, size_t v_sz_2819_, size_t v_i_2820_, lean_object* v_b_2821_){
_start:
{
lean_object* v_a_2824_; uint8_t v___x_2828_; 
v___x_2828_ = lean_usize_dec_lt(v_i_2820_, v_sz_2819_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v_b_2821_);
return v___x_2829_;
}
else
{
lean_object* v_a_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___y_2834_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_a_2830_ = lean_array_uget_borrowed(v_as_2818_, v_i_2820_);
v_fst_2831_ = lean_ctor_get(v_a_2830_, 0);
v_snd_2832_ = lean_ctor_get(v_a_2830_, 1);
v___x_2856_ = lean_box(1);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_array_get_size(v_snd_2832_);
v___x_2859_ = lean_nat_dec_lt(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
v___y_2834_ = v___x_2856_;
goto v___jp_2833_;
}
else
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_nat_dec_le(v___x_2858_, v___x_2858_);
if (v___x_2860_ == 0)
{
if (v___x_2859_ == 0)
{
v___y_2834_ = v___x_2856_;
goto v___jp_2833_;
}
else
{
size_t v___x_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = lean_usize_of_nat(v___x_2858_);
v___x_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2832_, v___x_2861_, v___x_2862_, v___x_2856_);
v___y_2834_ = v___x_2863_;
goto v___jp_2833_;
}
}
else
{
size_t v___x_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = lean_usize_of_nat(v___x_2858_);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2832_, v___x_2864_, v___x_2865_, v___x_2856_);
v___y_2834_ = v___x_2866_;
goto v___jp_2833_;
}
}
v___jp_2833_:
{
lean_object* v___x_2835_; 
lean_inc(v_fst_2831_);
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2831_, v_b_2821_, v___y_2834_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v_a_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v_a_2837_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_a_2837_);
lean_dec(v_a_2836_);
v_a_2824_ = v_a_2837_;
goto v___jp_2823_;
}
else
{
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2847_; 
v_a_2838_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2840_ = v___x_2835_;
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2835_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
if (lean_obj_tag(v_a_2838_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; 
v_a_2842_ = lean_ctor_get(v_a_2838_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v_a_2838_, 1);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 0);
lean_ctor_set(v___x_2840_, 0, v_a_2842_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
lean_object* v_a_2846_; 
lean_del_object(v___x_2840_);
v_a_2846_ = lean_ctor_get(v_a_2838_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v_a_2838_, 1);
v_a_2824_ = v_a_2846_;
goto v___jp_2823_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_a_2848_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2835_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2835_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
}
v___jp_2823_:
{
size_t v___x_2825_; size_t v___x_2826_; 
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_add(v_i_2820_, v___x_2825_);
v_i_2820_ = v___x_2826_;
v_b_2821_ = v_a_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2867_, lean_object* v_sz_2868_, lean_object* v_i_2869_, lean_object* v_b_2870_, lean_object* v___y_2871_){
_start:
{
size_t v_sz_boxed_2872_; size_t v_i_boxed_2873_; lean_object* v_res_2874_; 
v_sz_boxed_2872_ = lean_unbox_usize(v_sz_2868_);
lean_dec(v_sz_2868_);
v_i_boxed_2873_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2867_, v_sz_boxed_2872_, v_i_boxed_2873_, v_b_2870_);
lean_dec_ref(v_as_2867_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2878_, lean_object* v_as_2879_, size_t v_sz_2880_, size_t v_i_2881_, lean_object* v_b_2882_){
_start:
{
lean_object* v_a_2885_; uint8_t v_anyUnlocated_2889_; 
v_anyUnlocated_2889_ = lean_usize_dec_lt(v_i_2881_, v_sz_2880_);
if (v_anyUnlocated_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v_fst_2878_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_b_2882_);
return v___x_2890_;
}
else
{
lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2929_; 
v_fst_2891_ = lean_ctor_get(v_b_2882_, 0);
v_snd_2892_ = lean_ctor_get(v_b_2882_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_b_2882_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2894_ = v_b_2882_;
v_isShared_2895_ = v_isSharedCheck_2929_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snd_2892_);
lean_inc(v_fst_2891_);
lean_dec(v_b_2882_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2929_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_a_2896_; lean_object* v_position_x3f_2897_; 
v_a_2896_ = lean_array_uget_borrowed(v_as_2879_, v_i_2881_);
v_position_x3f_2897_ = lean_ctor_get(v_a_2896_, 2);
if (lean_obj_tag(v_position_x3f_2897_) == 0)
{
lean_object* v_linter_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec(v_snd_2892_);
v_linter_2898_ = lean_ctor_get(v_a_2896_, 0);
v___x_2899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2898_);
v___x_2900_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2898_, v_anyUnlocated_2889_);
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
lean_inc(v_fst_2878_);
v___x_2904_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2878_, v_anyUnlocated_2889_);
v___x_2905_ = lean_string_append(v___x_2903_, v___x_2904_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
v___x_2908_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec_ref_known(v___x_2908_, 1);
v___x_2909_ = lean_box(v_anyUnlocated_2889_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 1, v___x_2909_);
v___x_2911_ = v___x_2894_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_fst_2891_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v_a_2885_ = v___x_2911_;
goto v___jp_2884_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_del_object(v___x_2894_);
lean_dec(v_fst_2891_);
lean_dec(v_fst_2878_);
v_a_2913_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2908_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2908_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_linter_2921_; lean_object* v_file_2922_; lean_object* v_val_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v_linter_2921_ = lean_ctor_get(v_a_2896_, 0);
v_file_2922_ = lean_ctor_get(v_a_2896_, 3);
v_val_2923_ = lean_ctor_get(v_position_x3f_2897_, 0);
lean_inc(v_linter_2921_);
lean_inc(v_val_2923_);
lean_inc_ref(v_file_2922_);
v___x_2924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2924_, 0, v_file_2922_);
lean_ctor_set(v___x_2924_, 1, v_val_2923_);
lean_ctor_set(v___x_2924_, 2, v_linter_2921_);
v___x_2925_ = lean_array_push(v_fst_2891_, v___x_2924_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2925_);
v___x_2927_ = v___x_2894_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_snd_2892_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
v_a_2885_ = v___x_2927_;
goto v___jp_2884_;
}
}
}
}
v___jp_2884_:
{
size_t v___x_2886_; size_t v___x_2887_; 
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2881_, v___x_2886_);
v_i_2881_ = v___x_2887_;
v_b_2882_ = v_a_2885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2930_, lean_object* v_as_2931_, lean_object* v_sz_2932_, lean_object* v_i_2933_, lean_object* v_b_2934_, lean_object* v___y_2935_){
_start:
{
size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2932_);
lean_dec(v_sz_2932_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2933_);
lean_dec(v_i_2933_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2930_, v_as_2931_, v_sz_boxed_2936_, v_i_boxed_2937_, v_b_2934_);
lean_dec_ref(v_as_2931_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2939_, size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_b_2942_){
_start:
{
uint8_t v___x_2944_; 
v___x_2944_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_b_2942_);
return v___x_2945_;
}
else
{
lean_object* v_a_2946_; lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v_fst_2949_; lean_object* v_snd_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2973_; 
v_a_2946_ = lean_array_uget_borrowed(v_as_2939_, v_i_2941_);
v_fst_2947_ = lean_ctor_get(v_a_2946_, 0);
v_snd_2948_ = lean_ctor_get(v_a_2946_, 1);
v_fst_2949_ = lean_ctor_get(v_b_2942_, 0);
v_snd_2950_ = lean_ctor_get(v_b_2942_, 1);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_b_2942_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2952_ = v_b_2942_;
v_isShared_2953_ = v_isSharedCheck_2973_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_snd_2950_);
lean_inc(v_fst_2949_);
lean_dec(v_b_2942_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2973_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_snd_2950_);
v___x_2955_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
size_t v_sz_2956_; size_t v___x_2957_; lean_object* v___x_2958_; 
v_sz_2956_ = lean_array_size(v_snd_2948_);
v___x_2957_ = ((size_t)0ULL);
lean_inc(v_fst_2947_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2947_, v_snd_2948_, v_sz_2956_, v___x_2957_, v___x_2955_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2971_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_fst_2960_ = lean_ctor_get(v_a_2959_, 0);
v_snd_2961_ = lean_ctor_get(v_a_2959_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2959_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2963_ = v_a_2959_;
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snd_2961_);
lean_inc(v_fst_2960_);
lean_dec(v_a_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_fst_2960_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_snd_2961_);
v___x_2966_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
size_t v___x_2967_; size_t v___x_2968_; 
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_add(v_i_2941_, v___x_2967_);
v_i_2941_ = v___x_2968_;
v_b_2942_ = v___x_2966_;
goto _start;
}
}
}
else
{
return v___x_2958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2974_, lean_object* v_sz_2975_, lean_object* v_i_2976_, lean_object* v_b_2977_, lean_object* v___y_2978_){
_start:
{
size_t v_sz_boxed_2979_; size_t v_i_boxed_2980_; lean_object* v_res_2981_; 
v_sz_boxed_2979_ = lean_unbox_usize(v_sz_2975_);
lean_dec(v_sz_2975_);
v_i_boxed_2980_ = lean_unbox_usize(v_i_2976_);
lean_dec(v_i_2976_);
v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2974_, v_sz_boxed_2979_, v_i_boxed_2980_, v_b_2977_);
lean_dec_ref(v_as_2974_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2982_, size_t v_sz_2983_, size_t v_i_2984_, lean_object* v_b_2985_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_lt(v_i_2984_, v_sz_2983_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_b_2985_);
return v___x_2988_;
}
else
{
lean_object* v_a_2989_; lean_object* v_message_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2989_ = lean_array_uget_borrowed(v_as_2982_, v_i_2984_);
v_message_2990_ = lean_ctor_get(v_a_2989_, 1);
v___x_2991_ = 0;
lean_inc_ref(v_message_2990_);
v___x_2992_ = l_Lean_SerialMessage_toString(v_message_2990_, v___x_2991_);
v___x_2993_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2994_; size_t v___x_2995_; size_t v___x_2996_; 
lean_dec_ref_known(v___x_2993_, 1);
v___x_2994_ = lean_box(0);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2984_, v___x_2995_);
v_i_2984_ = v___x_2996_;
v_b_2985_ = v___x_2994_;
goto _start;
}
else
{
return v___x_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2998_, lean_object* v_sz_2999_, lean_object* v_i_3000_, lean_object* v_b_3001_, lean_object* v___y_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2999_);
lean_dec(v_sz_2999_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2998_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_3001_);
lean_dec_ref(v_as_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_3008_, size_t v_sz_3009_, size_t v_i_3010_, lean_object* v_b_3011_){
_start:
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_usize_dec_lt(v_i_3010_, v_sz_3009_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_b_3011_);
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v_fst_3016_; lean_object* v_snd_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3015_ = lean_array_uget_borrowed(v_as_3008_, v_i_3010_);
v_fst_3016_ = lean_ctor_get(v_a_3015_, 0);
v_snd_3017_ = lean_ctor_get(v_a_3015_, 1);
v___x_3018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3016_);
v___x_3019_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3016_, v___x_3013_);
v___x_3020_ = lean_string_append(v___x_3018_, v___x_3019_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3022_ = lean_string_append(v___x_3020_, v___x_3021_);
v___x_3023_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; size_t v_sz_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = lean_box(0);
v_sz_3025_ = lean_array_size(v_snd_3017_);
v___x_3026_ = ((size_t)0ULL);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3017_, v_sz_3025_, v___x_3026_, v___x_3024_);
if (lean_obj_tag(v___x_3027_) == 0)
{
size_t v___x_3028_; size_t v___x_3029_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3010_, v___x_3028_);
v_i_3010_ = v___x_3029_;
v_b_3011_ = v___x_3024_;
goto _start;
}
else
{
return v___x_3027_;
}
}
else
{
return v___x_3023_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3031_, lean_object* v_sz_3032_, lean_object* v_i_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_){
_start:
{
size_t v_sz_boxed_3036_; size_t v_i_boxed_3037_; lean_object* v_res_3038_; 
v_sz_boxed_3036_ = lean_unbox_usize(v_sz_3032_);
lean_dec(v_sz_3032_);
v_i_boxed_3037_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3031_, v_sz_boxed_3036_, v_i_boxed_3037_, v_b_3034_);
lean_dec_ref(v_as_3031_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3043_, lean_object* v_linterOpts_3044_, lean_object* v_env_3045_, lean_object* v_mod_3046_){
_start:
{
uint8_t v_lintOnly_3048_; uint8_t v_mode_3049_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3120_; lean_object* v___x_3126_; lean_object* v_textGroups_3127_; 
v_lintOnly_3048_ = lean_ctor_get_uint8(v_args_3043_, sizeof(void*)*4);
v_mode_3049_ = lean_ctor_get_uint8(v_args_3043_, sizeof(void*)*4 + 1);
v___x_3126_ = l_Lean_Name_getRoot(v_mod_3046_);
v_textGroups_3127_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3045_, v___x_3126_);
lean_dec(v___x_3126_);
if (v_lintOnly_3048_ == 0)
{
v___y_3120_ = v_textGroups_3127_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_array_get_size(v_textGroups_3127_);
v___x_3130_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3044_, v_textGroups_3127_, v___x_3128_, v___x_3129_);
lean_dec_ref(v_textGroups_3127_);
v___y_3120_ = v___x_3130_;
goto v___jp_3119_;
}
v___jp_3050_:
{
switch(v_mode_3049_)
{
case 0:
{
lean_object* v___x_3053_; size_t v_sz_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = lean_box(0);
v_sz_3054_ = lean_array_size(v___y_3051_);
v___x_3055_ = ((size_t)0ULL);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3051_, v_sz_3054_, v___x_3055_, v___x_3053_);
lean_dec_ref(v___y_3051_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3065_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3060_, 0, v___y_3052_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3056_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
case 1:
{
lean_object* v___x_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3074_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3075_ = lean_array_size(v___y_3051_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3051_, v_sz_3075_, v___x_3076_, v___x_3074_);
lean_dec_ref(v___y_3051_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3089_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v_fst_3082_; lean_object* v_snd_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; lean_object* v___x_3087_; 
v_fst_3082_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_fst_3082_);
v_snd_3083_ = lean_ctor_get(v_a_3078_, 1);
lean_inc(v_snd_3083_);
lean_dec(v_a_3078_);
v___x_3084_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3084_, 0, v_fst_3082_);
v___x_3085_ = lean_unbox(v_snd_3083_);
lean_dec(v_snd_3083_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*1, v___x_3085_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3084_);
v___x_3087_ = v___x_3080_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3084_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
v_a_3090_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3077_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3077_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v_codeQualityEntries_3098_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3099_ = lean_array_size(v___y_3051_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3051_, v_sz_3099_, v___x_3100_, v_codeQualityEntries_3098_);
lean_dec_ref(v___y_3051_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3110_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3102_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3106_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
v_a_3111_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3101_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3101_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3121_ = lean_array_get_size(v___y_3120_);
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = lean_nat_dec_eq(v___x_3121_, v___x_3122_);
if (v___x_3123_ == 0)
{
uint8_t v___x_3124_; 
v___x_3124_ = 1;
v___y_3051_ = v___y_3120_;
v___y_3052_ = v___x_3124_;
goto v___jp_3050_;
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = 0;
v___y_3051_ = v___y_3120_;
v___y_3052_ = v___x_3125_;
goto v___jp_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3131_, lean_object* v_linterOpts_3132_, lean_object* v_env_3133_, lean_object* v_mod_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3131_, v_linterOpts_3132_, v_env_3133_, v_mod_3134_);
lean_dec(v_mod_3134_);
lean_dec_ref(v_env_3133_);
lean_dec_ref(v_linterOpts_3132_);
lean_dec_ref(v_args_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3137_, lean_object* v_t_3138_, lean_object* v_k_3139_, lean_object* v_fallback_3140_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3138_, v_k_3139_, v_fallback_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3142_, lean_object* v_t_3143_, lean_object* v_k_3144_, lean_object* v_fallback_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3142_, v_t_3143_, v_k_3144_, v_fallback_3145_);
lean_dec(v_fallback_3145_);
lean_dec(v_k_3144_);
lean_dec(v_t_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3147_, lean_object* v_____r_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3152_, 0, v___y_3147_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3154_, lean_object* v_____r_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v___y_15651__boxed_3159_; lean_object* v_res_3160_; 
v___y_15651__boxed_3159_ = lean_unbox(v___y_3154_);
v_res_3160_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_15651__boxed_3159_, v_____r_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
return v_res_3160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
lean_ctor_set(v___x_3166_, 2, v___x_3165_);
lean_ctor_set(v___x_3166_, 3, v___x_3165_);
lean_ctor_set(v___x_3166_, 4, v___x_3164_);
lean_ctor_set(v___x_3166_, 5, v___x_3164_);
lean_ctor_set(v___x_3166_, 6, v___x_3164_);
lean_ctor_set(v___x_3166_, 7, v___x_3164_);
lean_ctor_set(v___x_3166_, 8, v___x_3164_);
lean_ctor_set(v___x_3166_, 9, v___x_3164_);
lean_ctor_set(v___x_3166_, 10, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_unsigned_to_nat(32u);
v___x_3168_ = lean_mk_empty_array_with_capacity(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
size_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3170_ = ((size_t)5ULL);
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_unsigned_to_nat(32u);
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_3172_);
v___x_3174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3175_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
lean_ctor_set(v___x_3175_, 2, v___x_3171_);
lean_ctor_set(v___x_3175_, 3, v___x_3171_);
lean_ctor_set_usize(v___x_3175_, 4, v___x_3170_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = lean_box(1);
v___x_3177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
lean_ctor_set(v___x_3179_, 2, v___x_3176_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; lean_object* v_toCold_3185_; lean_object* v_env_3186_; lean_object* v_options_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3184_ = lean_st_ref_get(v___y_3182_);
v_toCold_3185_ = lean_ctor_get(v___y_3181_, 0);
v_env_3186_ = lean_ctor_get(v___x_3184_, 0);
lean_inc_ref(v_env_3186_);
lean_dec(v___x_3184_);
v_options_3187_ = lean_ctor_get(v_toCold_3185_, 2);
v___x_3188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
lean_inc_ref(v_options_3187_);
v___x_3190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3190_, 0, v_env_3186_);
lean_ctor_set(v___x_3190_, 1, v___x_3188_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
lean_ctor_set(v___x_3190_, 3, v_options_3187_);
v___x_3191_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v_msgData_3180_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_ref_3202_; lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3212_; 
v_ref_3202_ = lean_ctor_get(v___y_3199_, 2);
v___x_3203_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3198_, v___y_3199_, v___y_3200_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3212_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_inc(v_ref_3202_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_ref_3202_);
lean_ctor_set(v___x_3208_, 1, v_a_3204_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set_tag(v___x_3206_, 1);
lean_ctor_set(v___x_3206_, 0, v___x_3208_);
v___x_3210_ = v___x_3206_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3218_, lean_object* v_msg_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_toCold_3223_; lean_object* v_currRecDepth_3224_; lean_object* v_ref_3225_; uint8_t v_diag_3226_; uint8_t v_suppressElabErrors_3227_; lean_object* v_ref_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_toCold_3223_ = lean_ctor_get(v___y_3220_, 0);
v_currRecDepth_3224_ = lean_ctor_get(v___y_3220_, 1);
v_ref_3225_ = lean_ctor_get(v___y_3220_, 2);
v_diag_3226_ = lean_ctor_get_uint8(v___y_3220_, sizeof(void*)*3);
v_suppressElabErrors_3227_ = lean_ctor_get_uint8(v___y_3220_, sizeof(void*)*3 + 1);
v_ref_3228_ = l_Lean_replaceRef(v_ref_3218_, v_ref_3225_);
lean_inc(v_currRecDepth_3224_);
lean_inc_ref(v_toCold_3223_);
v___x_3229_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3229_, 0, v_toCold_3223_);
lean_ctor_set(v___x_3229_, 1, v_currRecDepth_3224_);
lean_ctor_set(v___x_3229_, 2, v_ref_3228_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*3, v_diag_3226_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*3 + 1, v_suppressElabErrors_3227_);
v___x_3230_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3219_, v___x_3229_, v___y_3221_);
lean_dec_ref_known(v___x_3229_, 3);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3231_, lean_object* v_msg_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3231_, v_msg_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v_ref_3231_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3239_ = l_Lean_stringToMessageData(v___x_3238_);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3242_ = l_Lean_stringToMessageData(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3248_ = l_Lean_stringToMessageData(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3258_, lean_object* v_declHint_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; lean_object* v_env_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_st_ref_get(v___y_3260_);
v_env_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc_ref(v_env_3263_);
lean_dec(v___x_3262_);
v___x_3264_ = l_Lean_Name_isAnonymous(v_declHint_3259_);
if (v___x_3264_ == 0)
{
uint8_t v_isExporting_3265_; 
v_isExporting_3265_ = lean_ctor_get_uint8(v_env_3263_, sizeof(void*)*8);
if (v_isExporting_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_dec_ref(v_env_3263_);
lean_dec(v_declHint_3259_);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_msg_3258_);
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
lean_inc_ref(v_env_3263_);
v___x_3267_ = l_Lean_Environment_setExporting(v_env_3263_, v___x_3264_);
lean_inc(v_declHint_3259_);
lean_inc_ref(v___x_3267_);
v___x_3268_ = l_Lean_Environment_contains(v___x_3267_, v_declHint_3259_, v_isExporting_3265_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
lean_dec_ref(v___x_3267_);
lean_dec_ref(v_env_3263_);
lean_dec(v_declHint_3259_);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_msg_3258_);
return v___x_3269_;
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_c_3275_; lean_object* v___x_3276_; 
v___x_3270_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3271_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__5);
v___x_3272_ = l_Lean_Options_empty;
v___x_3273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3267_);
lean_ctor_set(v___x_3273_, 1, v___x_3270_);
lean_ctor_set(v___x_3273_, 2, v___x_3271_);
lean_ctor_set(v___x_3273_, 3, v___x_3272_);
lean_inc(v_declHint_3259_);
v___x_3274_ = l_Lean_MessageData_ofConstName(v_declHint_3259_, v___x_3264_);
v_c_3275_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3275_, 0, v___x_3273_);
lean_ctor_set(v_c_3275_, 1, v___x_3274_);
v___x_3276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3263_, v_declHint_3259_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec_ref(v_env_3263_);
lean_dec(v_declHint_3259_);
v___x_3277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
lean_ctor_set(v___x_3278_, 1, v_c_3275_);
v___x_3279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_MessageData_note(v___x_3280_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v_msg_3258_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
else
{
lean_object* v_val_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3319_; 
v_val_3284_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3286_ = v___x_3276_;
v_isShared_3287_ = v_isSharedCheck_3319_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_val_3284_);
lean_dec(v___x_3276_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3319_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v_mod_3291_; uint8_t v___x_3292_; 
v___x_3288_ = lean_box(0);
v___x_3289_ = l_Lean_Environment_header(v_env_3263_);
lean_dec_ref(v_env_3263_);
v___x_3290_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3289_);
v_mod_3291_ = lean_array_get(v___x_3288_, v___x_3290_, v_val_3284_);
lean_dec(v_val_3284_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = l_Lean_isPrivateName(v_declHint_3259_);
lean_dec(v_declHint_3259_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_c_3275_);
v___x_3295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_MessageData_ofName(v_mod_3291_);
v___x_3298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_MessageData_note(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_msg_3258_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3302_);
v___x_3304_ = v___x_3286_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v_c_3275_);
v___x_3308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_ofName(v_mod_3291_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = l_Lean_MessageData_note(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v_msg_3258_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3315_);
v___x_3317_ = v___x_3286_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3320_; 
lean_dec_ref(v_env_3263_);
lean_dec(v_declHint_3259_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_msg_3258_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3321_, lean_object* v_declHint_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3321_, v_declHint_3322_, v___y_3323_);
lean_dec(v___y_3323_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3326_, lean_object* v_declHint_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3341_; 
v___x_3331_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3326_, v_declHint_3327_, v___y_3329_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3341_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3341_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3336_ = l_Lean_unknownIdentifierMessageTag;
v___x_3337_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v_a_3332_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3337_);
v___x_3339_ = v___x_3334_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3342_, lean_object* v_declHint_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3342_, v_declHint_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3348_, lean_object* v_msg_3349_, lean_object* v_declHint_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v_a_3355_; lean_object* v___x_3356_; 
v___x_3354_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3349_, v_declHint_3350_, v___y_3351_, v___y_3352_);
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3354_);
v___x_3356_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3348_, v_a_3355_, v___y_3351_, v___y_3352_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3357_, lean_object* v_msg_3358_, lean_object* v_declHint_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3357_, v_msg_3358_, v_declHint_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v_ref_3357_);
return v_res_3363_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3369_, lean_object* v_constName_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3374_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3375_ = 0;
lean_inc(v_constName_3370_);
v___x_3376_ = l_Lean_MessageData_ofConstName(v_constName_3370_, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3374_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
v___x_3380_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3369_, v___x_3379_, v_constName_3370_, v___y_3371_, v___y_3372_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3381_, lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3381_, v_constName_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v_ref_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_ref_3391_; lean_object* v___x_3392_; 
v_ref_3391_ = lean_ctor_get(v___y_3388_, 2);
v___x_3392_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3391_, v_constName_3387_, v___y_3388_, v___y_3389_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; lean_object* v_env_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3402_ = lean_st_ref_get(v___y_3400_);
v_env_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc_ref(v_env_3403_);
lean_dec(v___x_3402_);
v___x_3404_ = 0;
lean_inc(v_constName_3398_);
v___x_3405_ = l_Lean_Environment_find_x3f(v_env_3403_, v_constName_3398_, v___x_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3398_, v___y_3399_, v___y_3400_);
return v___x_3406_;
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_constName_3398_);
v_val_3407_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3405_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_val_3407_);
lean_dec(v___x_3405_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set_tag(v___x_3409_, 0);
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_val_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___x_3424_; 
lean_inc(v_declName_3420_);
v___x_3424_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3451_; 
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v___x_3424_, 0);
lean_dec(v_unused_3452_);
v___x_3426_ = v___x_3424_;
v_isShared_3427_ = v_isSharedCheck_3451_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v___x_3424_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3451_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v_env_3429_; lean_object* v___x_3430_; 
v___x_3428_ = lean_st_ref_get(v___y_3422_);
v_env_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc_ref(v_env_3429_);
lean_dec(v___x_3428_);
v___x_3430_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3429_, v_declName_3420_);
lean_dec(v_declName_3420_);
lean_dec_ref(v_env_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = lean_box(0);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3431_);
v___x_3433_ = v___x_3426_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
else
{
lean_object* v_val_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3450_; 
v_val_3435_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3437_ = v___x_3430_;
v_isShared_3438_ = v_isSharedCheck_3450_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_val_3435_);
lean_dec(v___x_3430_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3450_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v_env_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3439_ = lean_st_ref_get(v___y_3422_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_ref(v_env_3440_);
lean_dec(v___x_3439_);
v___x_3441_ = lean_box(0);
v___x_3442_ = l_Lean_Environment_allImportedModuleNames(v_env_3440_);
lean_dec_ref(v_env_3440_);
v___x_3443_ = lean_array_get(v___x_3441_, v___x_3442_, v_val_3435_);
lean_dec(v_val_3435_);
lean_dec_ref(v___x_3442_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3443_);
v___x_3445_ = v___x_3437_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3445_);
v___x_3447_ = v___x_3426_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v_declName_3420_);
v_a_3453_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3424_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3424_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3467_, lean_object* v_sp_3468_, lean_object* v___x_3469_, lean_object* v_as_3470_, size_t v_sz_3471_, size_t v_i_3472_, lean_object* v_b_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_a_3478_; uint8_t v___x_3482_; 
v___x_3482_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_b_3473_);
return v___x_3483_;
}
else
{
lean_object* v_a_3484_; lean_object* v_fst_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3620_; 
v_a_3484_ = lean_array_uget(v_as_3470_, v_i_3472_);
v_fst_3485_ = lean_ctor_get(v_a_3484_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_a_3484_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_a_3484_, 1);
lean_dec(v_unused_3621_);
v___x_3487_ = v_a_3484_;
v_isShared_3488_ = v_isSharedCheck_3620_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_fst_3485_);
lean_dec(v_a_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3620_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; 
lean_inc(v_fst_3485_);
v___x_3489_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3485_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_object* v_fst_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3525_; 
v_fst_3491_ = lean_ctor_get(v_b_3473_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_b_3473_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v_b_3473_, 1);
lean_dec(v_unused_3526_);
v___x_3493_ = v_b_3473_;
v_isShared_3494_ = v_isSharedCheck_3525_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_fst_3491_);
lean_dec(v_b_3473_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3525_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_optName_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_optName_3495_ = lean_ctor_get(v_fst_3467_, 1);
v___x_3496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3485_, v___x_3482_);
v___x_3498_ = lean_string_append(v___x_3496_, v___x_3497_);
lean_dec_ref(v___x_3497_);
v___x_3499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__2));
v___x_3500_ = lean_string_append(v___x_3498_, v___x_3499_);
lean_inc(v_optName_3495_);
v___x_3501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3495_, v___x_3482_);
v___x_3502_ = lean_string_append(v___x_3500_, v___x_3501_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
v___x_3505_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3504_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec_ref_known(v___x_3505_, 1);
lean_del_object(v___x_3487_);
v___x_3506_ = lean_box(v___x_3482_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v___x_3506_);
v___x_3508_ = v___x_3493_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_fst_3491_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
v_a_3478_ = v___x_3508_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3524_; 
lean_del_object(v___x_3493_);
lean_dec(v_fst_3491_);
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v_a_3510_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3512_ = v___x_3505_;
v_isShared_3513_ = v_isSharedCheck_3524_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3505_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3524_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_ref_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v_ref_3514_ = lean_ctor_get(v___y_3474_, 2);
v___x_3515_ = lean_io_error_to_string(v_a_3510_);
v___x_3516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = l_Lean_MessageData_ofFormat(v___x_3516_);
lean_inc(v_ref_3514_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3517_);
lean_ctor_set(v___x_3487_, 0, v_ref_3514_);
v___x_3519_ = v___x_3487_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_ref_3514_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3519_);
v___x_3521_ = v___x_3512_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
else
{
lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3611_; 
v_fst_3527_ = lean_ctor_get(v_b_3473_, 0);
v_snd_3528_ = lean_ctor_get(v_b_3473_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_b_3473_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3530_ = v_b_3473_;
v_isShared_3531_ = v_isSharedCheck_3611_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_snd_3528_);
lean_inc(v_fst_3527_);
lean_dec(v_b_3473_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3611_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_val_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3610_; 
v_val_3532_ = lean_ctor_get(v_a_3490_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3534_ = v_a_3490_;
v_isShared_3535_ = v_isSharedCheck_3610_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_val_3532_);
lean_dec(v_a_3490_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3610_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3485_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___y_3539_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
if (lean_obj_tag(v_a_3537_) == 0)
{
lean_inc(v___x_3469_);
v___y_3539_ = v___x_3469_;
goto v___jp_3538_;
}
else
{
lean_object* v_val_3601_; 
v_val_3601_ = lean_ctor_get(v_a_3537_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v_a_3537_, 1);
v___y_3539_ = v_val_3601_;
goto v___jp_3538_;
}
v___jp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__4));
lean_inc(v___y_3539_);
lean_inc(v_sp_3468_);
v___x_3541_ = l_Lean_SearchPath_findWithExt(v_sp_3468_, v___x_3540_, v___y_3539_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
if (lean_obj_tag(v_a_3542_) == 0)
{
lean_object* v_optName_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec(v_val_3532_);
lean_dec(v_snd_3528_);
v_optName_3543_ = lean_ctor_get(v_fst_3467_, 1);
v___x_3544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__5));
v___x_3545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3539_, v___x_3482_);
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__6));
v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
lean_inc(v_optName_3543_);
v___x_3549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3543_, v___x_3482_);
v___x_3550_ = lean_string_append(v___x_3548_, v___x_3549_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__5___closed__3));
v___x_3552_ = lean_string_append(v___x_3550_, v___x_3551_);
v___x_3553_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3552_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec_ref_known(v___x_3553_, 1);
lean_del_object(v___x_3534_);
lean_del_object(v___x_3487_);
v___x_3554_ = lean_box(v___x_3482_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v___x_3554_);
v___x_3556_ = v___x_3530_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_fst_3527_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
v_a_3478_ = v___x_3556_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3530_);
lean_dec(v_fst_3527_);
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v_a_3558_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3560_ = v___x_3553_;
v_isShared_3561_ = v_isSharedCheck_3574_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3553_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3574_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_ref_3562_; lean_object* v___x_3563_; lean_object* v___x_3565_; 
v_ref_3562_ = lean_ctor_get(v___y_3474_, 2);
v___x_3563_ = lean_io_error_to_string(v_a_3558_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 3);
lean_ctor_set(v___x_3534_, 0, v___x_3563_);
v___x_3565_ = v___x_3534_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = l_Lean_MessageData_ofFormat(v___x_3565_);
lean_inc(v_ref_3562_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3566_);
lean_ctor_set(v___x_3487_, 0, v_ref_3562_);
v___x_3568_ = v___x_3487_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_ref_3562_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3570_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3568_);
v___x_3570_ = v___x_3560_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
else
{
lean_object* v_range_3575_; lean_object* v_val_3576_; lean_object* v_pos_3577_; lean_object* v_optName_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
lean_dec(v___y_3539_);
lean_del_object(v___x_3534_);
lean_del_object(v___x_3487_);
v_range_3575_ = lean_ctor_get(v_val_3532_, 0);
lean_inc_ref(v_range_3575_);
lean_dec(v_val_3532_);
v_val_3576_ = lean_ctor_get(v_a_3542_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v_a_3542_, 1);
v_pos_3577_ = lean_ctor_get(v_range_3575_, 0);
lean_inc_ref(v_pos_3577_);
lean_dec_ref(v_range_3575_);
v_optName_3578_ = lean_ctor_get(v_fst_3467_, 1);
lean_inc(v_optName_3578_);
v___x_3579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3579_, 0, v_val_3576_);
lean_ctor_set(v___x_3579_, 1, v_pos_3577_);
lean_ctor_set(v___x_3579_, 2, v_optName_3578_);
v___x_3580_ = lean_array_push(v_fst_3527_, v___x_3579_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3580_);
v___x_3582_ = v___x_3530_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_snd_3528_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
v_a_3478_ = v___x_3582_;
goto v___jp_3477_;
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3600_; 
lean_dec(v___y_3539_);
lean_dec(v_val_3532_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v_a_3584_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3586_ = v___x_3541_;
v_isShared_3587_ = v_isSharedCheck_3600_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3541_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3600_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_ref_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v_ref_3588_ = lean_ctor_get(v___y_3474_, 2);
v___x_3589_ = lean_io_error_to_string(v_a_3584_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 3);
lean_ctor_set(v___x_3534_, 0, v___x_3589_);
v___x_3591_ = v___x_3534_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = l_Lean_MessageData_ofFormat(v___x_3591_);
lean_inc(v_ref_3588_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3592_);
lean_ctor_set(v___x_3487_, 0, v_ref_3588_);
v___x_3594_ = v___x_3487_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_ref_3588_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3594_);
v___x_3596_ = v___x_3586_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_del_object(v___x_3534_);
lean_dec(v_val_3532_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_del_object(v___x_3487_);
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v_a_3602_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3536_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3536_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3487_);
lean_dec(v_fst_3485_);
lean_dec_ref(v_b_3473_);
lean_dec(v___x_3469_);
lean_dec(v_sp_3468_);
lean_dec_ref(v_fst_3467_);
v_a_3612_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3489_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3489_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
v___jp_3477_:
{
size_t v___x_3479_; size_t v___x_3480_; 
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3472_, v___x_3479_);
v_i_3472_ = v___x_3480_;
v_b_3473_ = v_a_3478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3622_, lean_object* v_sp_3623_, lean_object* v___x_3624_, lean_object* v_as_3625_, lean_object* v_sz_3626_, lean_object* v_i_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
size_t v_sz_boxed_3632_; size_t v_i_boxed_3633_; lean_object* v_res_3634_; 
v_sz_boxed_3632_ = lean_unbox_usize(v_sz_3626_);
lean_dec(v_sz_3626_);
v_i_boxed_3633_ = lean_unbox_usize(v_i_3627_);
lean_dec(v_i_3627_);
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3622_, v_sp_3623_, v___x_3624_, v_as_3625_, v_sz_boxed_3632_, v_i_boxed_3633_, v_b_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_as_3625_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
if (lean_obj_tag(v_x_3636_) == 0)
{
return v_x_3635_;
}
else
{
lean_object* v_key_3637_; lean_object* v_value_3638_; lean_object* v_tail_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v_key_3637_ = lean_ctor_get(v_x_3636_, 0);
v_value_3638_ = lean_ctor_get(v_x_3636_, 1);
v_tail_3639_ = lean_ctor_get(v_x_3636_, 2);
lean_inc(v_value_3638_);
lean_inc(v_key_3637_);
v___x_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3640_, 0, v_key_3637_);
lean_ctor_set(v___x_3640_, 1, v_value_3638_);
v___x_3641_ = lean_array_push(v_x_3635_, v___x_3640_);
v_x_3635_ = v___x_3641_;
v_x_3636_ = v_tail_3639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3643_, v_x_3644_);
lean_dec(v_x_3644_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3646_, size_t v_i_3647_, size_t v_stop_3648_, lean_object* v_b_3649_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_usize_dec_eq(v_i_3647_, v_stop_3648_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; size_t v___x_3653_; size_t v___x_3654_; 
v___x_3651_ = lean_array_uget_borrowed(v_as_3646_, v_i_3647_);
v___x_3652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3649_, v___x_3651_);
v___x_3653_ = ((size_t)1ULL);
v___x_3654_ = lean_usize_add(v_i_3647_, v___x_3653_);
v_i_3647_ = v___x_3654_;
v_b_3649_ = v___x_3652_;
goto _start;
}
else
{
return v_b_3649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3656_, lean_object* v_i_3657_, lean_object* v_stop_3658_, lean_object* v_b_3659_){
_start:
{
size_t v_i_boxed_3660_; size_t v_stop_boxed_3661_; lean_object* v_res_3662_; 
v_i_boxed_3660_ = lean_unbox_usize(v_i_3657_);
lean_dec(v_i_3657_);
v_stop_boxed_3661_ = lean_unbox_usize(v_stop_3658_);
lean_dec(v_stop_3658_);
v_res_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3656_, v_i_boxed_3660_, v_stop_boxed_3661_, v_b_3659_);
lean_dec_ref(v_as_3656_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3663_, lean_object* v___x_3664_, lean_object* v_as_3665_, size_t v_sz_3666_, size_t v_i_3667_, lean_object* v_b_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v___x_3672_; 
v___x_3672_ = lean_usize_dec_lt(v_i_3667_, v_sz_3666_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; 
lean_dec(v___x_3664_);
lean_dec(v_sp_3663_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_b_3668_);
return v___x_3673_;
}
else
{
lean_object* v_a_3674_; lean_object* v_fst_3675_; lean_object* v_snd_3676_; lean_object* v_fst_3677_; lean_object* v_snd_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3712_; 
v_a_3674_ = lean_array_uget_borrowed(v_as_3665_, v_i_3667_);
v_fst_3675_ = lean_ctor_get(v_a_3674_, 0);
v_snd_3676_ = lean_ctor_get(v_a_3674_, 1);
v_fst_3677_ = lean_ctor_get(v_b_3668_, 0);
v_snd_3678_ = lean_ctor_get(v_b_3668_, 1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_b_3668_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3680_ = v_b_3668_;
v_isShared_3681_ = v_isSharedCheck_3712_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_snd_3678_);
lean_inc(v_fst_3677_);
lean_dec(v_b_3668_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3712_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___y_3683_; lean_object* v_size_3703_; lean_object* v_buckets_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_size_3703_ = lean_ctor_get(v_snd_3676_, 0);
v_buckets_3704_ = lean_ctor_get(v_snd_3676_, 1);
v___x_3705_ = lean_mk_empty_array_with_capacity(v_size_3703_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = lean_array_get_size(v_buckets_3704_);
v___x_3708_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
v___y_3683_ = v___x_3705_;
goto v___jp_3682_;
}
else
{
size_t v___x_3709_; size_t v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = ((size_t)0ULL);
v___x_3710_ = lean_usize_of_nat(v___x_3707_);
v___x_3711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3704_, v___x_3709_, v___x_3710_, v___x_3705_);
v___y_3683_ = v___x_3711_;
goto v___jp_3682_;
}
v___jp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3681_ == 0)
{
v___x_3685_ = v___x_3680_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_fst_3677_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_snd_3678_);
v___x_3685_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
size_t v_sz_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v_sz_3686_ = lean_array_size(v___y_3683_);
v___x_3687_ = ((size_t)0ULL);
lean_inc(v___x_3664_);
lean_inc(v_sp_3663_);
lean_inc(v_fst_3675_);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3675_, v_sp_3663_, v___x_3664_, v___y_3683_, v_sz_3686_, v___x_3687_, v___x_3685_, v___y_3669_, v___y_3670_);
lean_dec_ref(v___y_3683_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v_fst_3690_; lean_object* v_snd_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3701_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v_fst_3690_ = lean_ctor_get(v_a_3689_, 0);
v_snd_3691_ = lean_ctor_get(v_a_3689_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_a_3689_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3693_ = v_a_3689_;
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_snd_3691_);
lean_inc(v_fst_3690_);
lean_dec(v_a_3689_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_fst_3690_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_snd_3691_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
size_t v___x_3697_; size_t v___x_3698_; 
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = lean_usize_add(v_i_3667_, v___x_3697_);
v_i_3667_ = v___x_3698_;
v_b_3668_ = v___x_3696_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3664_);
lean_dec(v_sp_3663_);
return v___x_3688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3713_, lean_object* v___x_3714_, lean_object* v_as_3715_, lean_object* v_sz_3716_, lean_object* v_i_3717_, lean_object* v_b_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
size_t v_sz_boxed_3722_; size_t v_i_boxed_3723_; lean_object* v_res_3724_; 
v_sz_boxed_3722_ = lean_unbox_usize(v_sz_3716_);
lean_dec(v_sz_3716_);
v_i_boxed_3723_ = lean_unbox_usize(v_i_3717_);
lean_dec(v_i_3717_);
v_res_3724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3713_, v___x_3714_, v_as_3715_, v_sz_boxed_3722_, v_i_boxed_3723_, v_b_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v_as_3715_);
return v_res_3724_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3725_, lean_object* v_as_3726_, size_t v_i_3727_, size_t v_stop_3728_){
_start:
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_usize_dec_eq(v_i_3727_, v_stop_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; lean_object* v_snd_3731_; lean_object* v_size_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v___x_3730_ = lean_array_uget_borrowed(v_as_3726_, v_i_3727_);
v_snd_3731_ = lean_ctor_get(v___x_3730_, 1);
v_size_3732_ = lean_ctor_get(v_snd_3731_, 0);
v___x_3733_ = 1;
v___x_3734_ = lean_unsigned_to_nat(0u);
v___x_3735_ = lean_nat_dec_eq(v_size_3732_, v___x_3734_);
if (v___x_3735_ == 0)
{
return v___x_3733_;
}
else
{
if (v___y_3725_ == 0)
{
size_t v___x_3736_; size_t v___x_3737_; 
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3727_, v___x_3736_);
v_i_3727_ = v___x_3737_;
goto _start;
}
else
{
return v___x_3733_;
}
}
}
else
{
uint8_t v___x_3739_; 
v___x_3739_ = 0;
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3740_, lean_object* v_as_3741_, lean_object* v_i_3742_, lean_object* v_stop_3743_){
_start:
{
uint8_t v___y_16635__boxed_3744_; size_t v_i_boxed_3745_; size_t v_stop_boxed_3746_; uint8_t v_res_3747_; lean_object* v_r_3748_; 
v___y_16635__boxed_3744_ = lean_unbox(v___y_3740_);
v_i_boxed_3745_ = lean_unbox_usize(v_i_3742_);
lean_dec(v_i_3742_);
v_stop_boxed_3746_ = lean_unbox_usize(v_stop_3743_);
lean_dec(v_stop_3743_);
v_res_3747_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_16635__boxed_3744_, v_as_3741_, v_i_boxed_3745_, v_stop_boxed_3746_);
lean_dec_ref(v_as_3741_);
v_r_3748_ = lean_box(v_res_3747_);
return v_r_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3749_, lean_object* v_v_3750_, lean_object* v_t_3751_){
_start:
{
lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; 
if (lean_obj_tag(v_t_3751_) == 0)
{
lean_object* v_size_3766_; lean_object* v_k_3767_; lean_object* v_v_3768_; lean_object* v_l_3769_; lean_object* v_r_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_4030_; 
v_size_3766_ = lean_ctor_get(v_t_3751_, 0);
v_k_3767_ = lean_ctor_get(v_t_3751_, 1);
v_v_3768_ = lean_ctor_get(v_t_3751_, 2);
v_l_3769_ = lean_ctor_get(v_t_3751_, 3);
v_r_3770_ = lean_ctor_get(v_t_3751_, 4);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_t_3751_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_3772_ = v_t_3751_;
v_isShared_3773_ = v_isSharedCheck_4030_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_r_3770_);
lean_inc(v_l_3769_);
lean_inc(v_v_3768_);
lean_inc(v_k_3767_);
lean_inc(v_size_3766_);
lean_dec(v_t_3751_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_4030_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; uint8_t v___y_3824_; lean_object* v_fst_4024_; lean_object* v_snd_4025_; lean_object* v_fst_4026_; lean_object* v_snd_4027_; uint8_t v___x_4028_; 
v_fst_4024_ = lean_ctor_get(v_k_3749_, 0);
v_snd_4025_ = lean_ctor_get(v_k_3749_, 1);
v_fst_4026_ = lean_ctor_get(v_k_3767_, 0);
v_snd_4027_ = lean_ctor_get(v_k_3767_, 1);
v___x_4028_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4024_, v_fst_4026_);
if (v___x_4028_ == 1)
{
uint8_t v___x_4029_; 
v___x_4029_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4025_, v_snd_4027_);
v___y_3824_ = v___x_4029_;
goto v___jp_3823_;
}
else
{
v___y_3824_ = v___x_4028_;
goto v___jp_3823_;
}
v___jp_3774_:
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_nat_add(v___y_3778_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec(v___y_3778_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 3, v___y_3779_);
lean_ctor_set(v___x_3772_, 0, v___x_3782_);
v___x_3784_ = v___x_3772_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v___y_3779_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_r_3770_);
v___x_3784_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3785_, 0, v___y_3777_);
lean_ctor_set(v___x_3785_, 1, v___y_3776_);
lean_ctor_set(v___x_3785_, 2, v___y_3775_);
lean_ctor_set(v___x_3785_, 3, v___y_3780_);
lean_ctor_set(v___x_3785_, 4, v___x_3784_);
return v___x_3785_;
}
}
v___jp_3787_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = lean_nat_add(v___y_3793_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec(v___y_3793_);
v___x_3801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v___y_3791_);
lean_ctor_set(v___x_3801_, 2, v___y_3795_);
lean_ctor_set(v___x_3801_, 3, v___y_3797_);
lean_ctor_set(v___x_3801_, 4, v___y_3789_);
v___x_3802_ = lean_nat_add(v___y_3798_, v___y_3790_);
lean_dec(v___y_3790_);
if (lean_obj_tag(v___y_3796_) == 0)
{
lean_object* v_size_3803_; 
v_size_3803_ = lean_ctor_get(v___y_3796_, 0);
lean_inc(v_size_3803_);
v___y_3775_ = v___y_3788_;
v___y_3776_ = v___y_3792_;
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___x_3802_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___x_3801_;
v___y_3781_ = v_size_3803_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_unsigned_to_nat(0u);
v___y_3775_ = v___y_3788_;
v___y_3776_ = v___y_3792_;
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___x_3802_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___x_3801_;
v___y_3781_ = v___x_3804_;
goto v___jp_3774_;
}
}
v___jp_3805_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_nat_add(v___y_3812_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec(v___y_3812_);
v___x_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set(v___x_3819_, 1, v_k_3767_);
lean_ctor_set(v___x_3819_, 2, v_v_3768_);
lean_ctor_set(v___x_3819_, 3, v_l_3769_);
lean_ctor_set(v___x_3819_, 4, v___y_3809_);
v___x_3820_ = lean_nat_add(v___y_3813_, v___y_3807_);
lean_dec(v___y_3807_);
if (lean_obj_tag(v___y_3806_) == 0)
{
lean_object* v_size_3821_; 
v_size_3821_ = lean_ctor_get(v___y_3806_, 0);
lean_inc(v_size_3821_);
v___y_3753_ = v___y_3806_;
v___y_3754_ = v___y_3808_;
v___y_3755_ = v___x_3819_;
v___y_3756_ = v___y_3811_;
v___y_3757_ = v___y_3810_;
v___y_3758_ = v___x_3820_;
v___y_3759_ = v___y_3814_;
v___y_3760_ = v___y_3815_;
v___y_3761_ = v___y_3816_;
v___y_3762_ = v_size_3821_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_unsigned_to_nat(0u);
v___y_3753_ = v___y_3806_;
v___y_3754_ = v___y_3808_;
v___y_3755_ = v___x_3819_;
v___y_3756_ = v___y_3811_;
v___y_3757_ = v___y_3810_;
v___y_3758_ = v___x_3820_;
v___y_3759_ = v___y_3814_;
v___y_3760_ = v___y_3815_;
v___y_3761_ = v___y_3816_;
v___y_3762_ = v___x_3822_;
goto v___jp_3752_;
}
}
v___jp_3823_:
{
switch(v___y_3824_)
{
case 0:
{
lean_object* v_impl_3825_; lean_object* v___x_3826_; 
lean_dec(v_size_3766_);
v_impl_3825_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3749_, v_v_3750_, v_l_3769_);
v___x_3826_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3770_) == 0)
{
lean_object* v_size_3827_; lean_object* v_size_3828_; lean_object* v_k_3829_; lean_object* v_v_3830_; lean_object* v_l_3831_; lean_object* v_r_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_size_3827_ = lean_ctor_get(v_r_3770_, 0);
v_size_3828_ = lean_ctor_get(v_impl_3825_, 0);
lean_inc(v_size_3828_);
v_k_3829_ = lean_ctor_get(v_impl_3825_, 1);
lean_inc(v_k_3829_);
v_v_3830_ = lean_ctor_get(v_impl_3825_, 2);
lean_inc(v_v_3830_);
v_l_3831_ = lean_ctor_get(v_impl_3825_, 3);
lean_inc(v_l_3831_);
v_r_3832_ = lean_ctor_get(v_impl_3825_, 4);
lean_inc(v_r_3832_);
v___x_3833_ = lean_unsigned_to_nat(3u);
v___x_3834_ = lean_nat_mul(v___x_3833_, v_size_3827_);
v___x_3835_ = lean_nat_dec_lt(v___x_3834_, v_size_3828_);
lean_dec(v___x_3834_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec(v_r_3832_);
lean_dec(v_l_3831_);
lean_dec(v_v_3830_);
lean_dec(v_k_3829_);
lean_del_object(v___x_3772_);
v___x_3836_ = lean_nat_add(v___x_3826_, v_size_3828_);
lean_dec(v_size_3828_);
v___x_3837_ = lean_nat_add(v___x_3836_, v_size_3827_);
lean_dec(v___x_3836_);
v___x_3838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v_k_3767_);
lean_ctor_set(v___x_3838_, 2, v_v_3768_);
lean_ctor_set(v___x_3838_, 3, v_impl_3825_);
lean_ctor_set(v___x_3838_, 4, v_r_3770_);
return v___x_3838_;
}
else
{
lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3875_; 
v_isSharedCheck_3875_ = !lean_is_exclusive(v_impl_3825_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3876_ = lean_ctor_get(v_impl_3825_, 4);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_impl_3825_, 3);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_impl_3825_, 2);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_impl_3825_, 1);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_impl_3825_, 0);
lean_dec(v_unused_3880_);
v___x_3840_ = v_impl_3825_;
v_isShared_3841_ = v_isSharedCheck_3875_;
goto v_resetjp_3839_;
}
else
{
lean_dec(v_impl_3825_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3875_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_size_3842_; lean_object* v_size_3843_; lean_object* v_k_3844_; lean_object* v_v_3845_; lean_object* v_l_3846_; lean_object* v_r_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v_size_3842_ = lean_ctor_get(v_l_3831_, 0);
v_size_3843_ = lean_ctor_get(v_r_3832_, 0);
v_k_3844_ = lean_ctor_get(v_r_3832_, 1);
v_v_3845_ = lean_ctor_get(v_r_3832_, 2);
v_l_3846_ = lean_ctor_get(v_r_3832_, 3);
v_r_3847_ = lean_ctor_get(v_r_3832_, 4);
v___x_3848_ = lean_unsigned_to_nat(2u);
v___x_3849_ = lean_nat_mul(v___x_3848_, v_size_3842_);
v___x_3850_ = lean_nat_dec_lt(v_size_3843_, v___x_3849_);
lean_dec(v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v_r_3847_);
lean_inc(v_l_3846_);
lean_inc(v_v_3845_);
lean_inc(v_k_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_r_3832_);
v___x_3851_ = lean_nat_add(v___x_3826_, v_size_3828_);
lean_dec(v_size_3828_);
v___x_3852_ = lean_nat_add(v___x_3851_, v_size_3827_);
lean_dec(v___x_3851_);
v___x_3853_ = lean_nat_add(v___x_3826_, v_size_3842_);
if (lean_obj_tag(v_l_3846_) == 0)
{
lean_object* v_size_3854_; 
v_size_3854_ = lean_ctor_get(v_l_3846_, 0);
lean_inc(v_size_3854_);
lean_inc(v_size_3827_);
v___y_3788_ = v_v_3845_;
v___y_3789_ = v_l_3846_;
v___y_3790_ = v_size_3827_;
v___y_3791_ = v_k_3829_;
v___y_3792_ = v_k_3844_;
v___y_3793_ = v___x_3853_;
v___y_3794_ = v___x_3852_;
v___y_3795_ = v_v_3830_;
v___y_3796_ = v_r_3847_;
v___y_3797_ = v_l_3831_;
v___y_3798_ = v___x_3826_;
v___y_3799_ = v_size_3854_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3827_);
v___y_3788_ = v_v_3845_;
v___y_3789_ = v_l_3846_;
v___y_3790_ = v_size_3827_;
v___y_3791_ = v_k_3829_;
v___y_3792_ = v_k_3844_;
v___y_3793_ = v___x_3853_;
v___y_3794_ = v___x_3852_;
v___y_3795_ = v_v_3830_;
v___y_3796_ = v_r_3847_;
v___y_3797_ = v_l_3831_;
v___y_3798_ = v___x_3826_;
v___y_3799_ = v___x_3855_;
goto v___jp_3787_;
}
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_del_object(v___x_3772_);
v___x_3856_ = lean_nat_add(v___x_3826_, v_size_3828_);
lean_dec(v_size_3828_);
v___x_3857_ = lean_nat_add(v___x_3856_, v_size_3827_);
lean_dec(v___x_3856_);
v___x_3858_ = lean_nat_add(v___x_3826_, v_size_3827_);
v___x_3859_ = lean_nat_add(v___x_3858_, v_size_3843_);
lean_dec(v___x_3858_);
lean_inc_ref(v_r_3770_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 4, v_r_3770_);
lean_ctor_set(v___x_3840_, 3, v_r_3832_);
lean_ctor_set(v___x_3840_, 2, v_v_3768_);
lean_ctor_set(v___x_3840_, 1, v_k_3767_);
lean_ctor_set(v___x_3840_, 0, v___x_3859_);
v___x_3861_ = v___x_3840_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_r_3832_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v_r_3770_);
v___x_3861_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
v_isSharedCheck_3868_ = !lean_is_exclusive(v_r_3770_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; 
v_unused_3869_ = lean_ctor_get(v_r_3770_, 4);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_r_3770_, 3);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_r_3770_, 2);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_r_3770_, 1);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_r_3770_, 0);
lean_dec(v_unused_3873_);
v___x_3863_ = v_r_3770_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v_r_3770_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 4, v___x_3861_);
lean_ctor_set(v___x_3863_, 3, v_l_3831_);
lean_ctor_set(v___x_3863_, 2, v_v_3830_);
lean_ctor_set(v___x_3863_, 1, v_k_3829_);
lean_ctor_set(v___x_3863_, 0, v___x_3857_);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_k_3829_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_v_3830_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_l_3831_);
lean_ctor_set(v_reuseFailAlloc_3867_, 4, v___x_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3881_; 
lean_del_object(v___x_3772_);
v_l_3881_ = lean_ctor_get(v_impl_3825_, 3);
lean_inc(v_l_3881_);
if (lean_obj_tag(v_l_3881_) == 0)
{
lean_object* v_r_3882_; lean_object* v_k_3883_; lean_object* v_v_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3893_; 
v_r_3882_ = lean_ctor_get(v_impl_3825_, 4);
v_k_3883_ = lean_ctor_get(v_impl_3825_, 1);
v_v_3884_ = lean_ctor_get(v_impl_3825_, 2);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_impl_3825_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3894_ = lean_ctor_get(v_impl_3825_, 3);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3825_, 0);
lean_dec(v_unused_3895_);
v___x_3886_ = v_impl_3825_;
v_isShared_3887_ = v_isSharedCheck_3893_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_r_3882_);
lean_inc(v_v_3884_);
lean_inc(v_k_3883_);
lean_dec(v_impl_3825_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3893_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3888_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3882_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 3, v_r_3882_);
lean_ctor_set(v___x_3886_, 2, v_v_3768_);
lean_ctor_set(v___x_3886_, 1, v_k_3767_);
lean_ctor_set(v___x_3886_, 0, v___x_3826_);
v___x_3890_ = v___x_3886_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_r_3882_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_r_3882_);
v___x_3890_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3888_);
lean_ctor_set(v___x_3891_, 1, v_k_3883_);
lean_ctor_set(v___x_3891_, 2, v_v_3884_);
lean_ctor_set(v___x_3891_, 3, v_l_3881_);
lean_ctor_set(v___x_3891_, 4, v___x_3890_);
return v___x_3891_;
}
}
}
else
{
lean_object* v_r_3896_; 
v_r_3896_ = lean_ctor_get(v_impl_3825_, 4);
lean_inc(v_r_3896_);
if (lean_obj_tag(v_r_3896_) == 0)
{
lean_object* v_k_3897_; lean_object* v_v_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3919_; 
v_k_3897_ = lean_ctor_get(v_impl_3825_, 1);
v_v_3898_ = lean_ctor_get(v_impl_3825_, 2);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_impl_3825_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; 
v_unused_3920_ = lean_ctor_get(v_impl_3825_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_impl_3825_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_impl_3825_, 0);
lean_dec(v_unused_3922_);
v___x_3900_ = v_impl_3825_;
v_isShared_3901_ = v_isSharedCheck_3919_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_v_3898_);
lean_inc(v_k_3897_);
lean_dec(v_impl_3825_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3919_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_k_3902_; lean_object* v_v_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3915_; 
v_k_3902_ = lean_ctor_get(v_r_3896_, 1);
v_v_3903_ = lean_ctor_get(v_r_3896_, 2);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_r_3896_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; 
v_unused_3916_ = lean_ctor_get(v_r_3896_, 4);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_r_3896_, 3);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_r_3896_, 0);
lean_dec(v_unused_3918_);
v___x_3905_ = v_r_3896_;
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_v_3903_);
lean_inc(v_k_3902_);
lean_dec(v_r_3896_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_unsigned_to_nat(3u);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 4, v_l_3881_);
lean_ctor_set(v___x_3905_, 3, v_l_3881_);
lean_ctor_set(v___x_3905_, 2, v_v_3898_);
lean_ctor_set(v___x_3905_, 1, v_k_3897_);
lean_ctor_set(v___x_3905_, 0, v___x_3826_);
v___x_3909_ = v___x_3905_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3914_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3914_, 3, v_l_3881_);
lean_ctor_set(v_reuseFailAlloc_3914_, 4, v_l_3881_);
v___x_3909_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3911_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v_l_3881_);
lean_ctor_set(v___x_3900_, 2, v_v_3768_);
lean_ctor_set(v___x_3900_, 1, v_k_3767_);
lean_ctor_set(v___x_3900_, 0, v___x_3826_);
v___x_3911_ = v___x_3900_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3913_, 3, v_l_3881_);
lean_ctor_set(v_reuseFailAlloc_3913_, 4, v_l_3881_);
v___x_3911_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3907_);
lean_ctor_set(v___x_3912_, 1, v_k_3902_);
lean_ctor_set(v___x_3912_, 2, v_v_3903_);
lean_ctor_set(v___x_3912_, 3, v___x_3909_);
lean_ctor_set(v___x_3912_, 4, v___x_3911_);
return v___x_3912_;
}
}
}
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_unsigned_to_nat(2u);
v___x_3924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_k_3767_);
lean_ctor_set(v___x_3924_, 2, v_v_3768_);
lean_ctor_set(v___x_3924_, 3, v_impl_3825_);
lean_ctor_set(v___x_3924_, 4, v_r_3896_);
return v___x_3924_;
}
}
}
}
case 1:
{
lean_object* v___x_3925_; 
lean_del_object(v___x_3772_);
lean_dec(v_v_3768_);
lean_dec(v_k_3767_);
v___x_3925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3925_, 0, v_size_3766_);
lean_ctor_set(v___x_3925_, 1, v_k_3749_);
lean_ctor_set(v___x_3925_, 2, v_v_3750_);
lean_ctor_set(v___x_3925_, 3, v_l_3769_);
lean_ctor_set(v___x_3925_, 4, v_r_3770_);
return v___x_3925_;
}
default: 
{
lean_object* v_impl_3926_; lean_object* v___x_3927_; 
lean_del_object(v___x_3772_);
lean_dec(v_size_3766_);
v_impl_3926_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3749_, v_v_3750_, v_r_3770_);
v___x_3927_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3769_) == 0)
{
lean_object* v_size_3928_; lean_object* v_size_3929_; lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v_l_3932_; lean_object* v_r_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_size_3928_ = lean_ctor_get(v_l_3769_, 0);
v_size_3929_ = lean_ctor_get(v_impl_3926_, 0);
lean_inc(v_size_3929_);
v_k_3930_ = lean_ctor_get(v_impl_3926_, 1);
lean_inc(v_k_3930_);
v_v_3931_ = lean_ctor_get(v_impl_3926_, 2);
lean_inc(v_v_3931_);
v_l_3932_ = lean_ctor_get(v_impl_3926_, 3);
lean_inc(v_l_3932_);
v_r_3933_ = lean_ctor_get(v_impl_3926_, 4);
lean_inc(v_r_3933_);
v___x_3934_ = lean_unsigned_to_nat(3u);
v___x_3935_ = lean_nat_mul(v___x_3934_, v_size_3928_);
v___x_3936_ = lean_nat_dec_lt(v___x_3935_, v_size_3929_);
lean_dec(v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec(v_r_3933_);
lean_dec(v_l_3932_);
lean_dec(v_v_3931_);
lean_dec(v_k_3930_);
v___x_3937_ = lean_nat_add(v___x_3927_, v_size_3928_);
v___x_3938_ = lean_nat_add(v___x_3937_, v_size_3929_);
lean_dec(v_size_3929_);
lean_dec(v___x_3937_);
v___x_3939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
lean_ctor_set(v___x_3939_, 1, v_k_3767_);
lean_ctor_set(v___x_3939_, 2, v_v_3768_);
lean_ctor_set(v___x_3939_, 3, v_l_3769_);
lean_ctor_set(v___x_3939_, 4, v_impl_3926_);
return v___x_3939_;
}
else
{
lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3974_; 
v_isSharedCheck_3974_ = !lean_is_exclusive(v_impl_3926_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; 
v_unused_3975_ = lean_ctor_get(v_impl_3926_, 4);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_impl_3926_, 3);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_impl_3926_, 2);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_impl_3926_, 1);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_impl_3926_, 0);
lean_dec(v_unused_3979_);
v___x_3941_ = v_impl_3926_;
v_isShared_3942_ = v_isSharedCheck_3974_;
goto v_resetjp_3940_;
}
else
{
lean_dec(v_impl_3926_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3974_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_size_3943_; lean_object* v_k_3944_; lean_object* v_v_3945_; lean_object* v_l_3946_; lean_object* v_r_3947_; lean_object* v_size_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v_size_3943_ = lean_ctor_get(v_l_3932_, 0);
v_k_3944_ = lean_ctor_get(v_l_3932_, 1);
v_v_3945_ = lean_ctor_get(v_l_3932_, 2);
v_l_3946_ = lean_ctor_get(v_l_3932_, 3);
v_r_3947_ = lean_ctor_get(v_l_3932_, 4);
v_size_3948_ = lean_ctor_get(v_r_3933_, 0);
v___x_3949_ = lean_unsigned_to_nat(2u);
v___x_3950_ = lean_nat_mul(v___x_3949_, v_size_3948_);
v___x_3951_ = lean_nat_dec_lt(v_size_3943_, v___x_3950_);
lean_dec(v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
lean_inc(v_size_3948_);
lean_inc(v_r_3947_);
lean_inc(v_l_3946_);
lean_inc(v_v_3945_);
lean_inc(v_k_3944_);
lean_del_object(v___x_3941_);
lean_dec(v_l_3932_);
v___x_3952_ = lean_nat_add(v___x_3927_, v_size_3928_);
v___x_3953_ = lean_nat_add(v___x_3952_, v_size_3929_);
lean_dec(v_size_3929_);
if (lean_obj_tag(v_l_3946_) == 0)
{
lean_object* v_size_3954_; 
v_size_3954_ = lean_ctor_get(v_l_3946_, 0);
lean_inc(v_size_3954_);
v___y_3806_ = v_r_3947_;
v___y_3807_ = v_size_3948_;
v___y_3808_ = v_k_3944_;
v___y_3809_ = v_l_3946_;
v___y_3810_ = v_k_3930_;
v___y_3811_ = v___x_3953_;
v___y_3812_ = v___x_3952_;
v___y_3813_ = v___x_3927_;
v___y_3814_ = v_v_3945_;
v___y_3815_ = v_v_3931_;
v___y_3816_ = v_r_3933_;
v___y_3817_ = v_size_3954_;
goto v___jp_3805_;
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_unsigned_to_nat(0u);
v___y_3806_ = v_r_3947_;
v___y_3807_ = v_size_3948_;
v___y_3808_ = v_k_3944_;
v___y_3809_ = v_l_3946_;
v___y_3810_ = v_k_3930_;
v___y_3811_ = v___x_3953_;
v___y_3812_ = v___x_3952_;
v___y_3813_ = v___x_3927_;
v___y_3814_ = v_v_3945_;
v___y_3815_ = v_v_3931_;
v___y_3816_ = v_r_3933_;
v___y_3817_ = v___x_3955_;
goto v___jp_3805_;
}
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3956_ = lean_nat_add(v___x_3927_, v_size_3928_);
v___x_3957_ = lean_nat_add(v___x_3956_, v_size_3929_);
lean_dec(v_size_3929_);
v___x_3958_ = lean_nat_add(v___x_3956_, v_size_3943_);
lean_dec(v___x_3956_);
lean_inc_ref(v_l_3769_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 4, v_l_3932_);
lean_ctor_set(v___x_3941_, 3, v_l_3769_);
lean_ctor_set(v___x_3941_, 2, v_v_3768_);
lean_ctor_set(v___x_3941_, 1, v_k_3767_);
lean_ctor_set(v___x_3941_, 0, v___x_3958_);
v___x_3960_ = v___x_3941_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v_l_3769_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v_l_3932_);
v___x_3960_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
v_isSharedCheck_3967_ = !lean_is_exclusive(v_l_3769_);
if (v_isSharedCheck_3967_ == 0)
{
lean_object* v_unused_3968_; lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; 
v_unused_3968_ = lean_ctor_get(v_l_3769_, 4);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_l_3769_, 3);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_l_3769_, 2);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_l_3769_, 1);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_l_3769_, 0);
lean_dec(v_unused_3972_);
v___x_3962_ = v_l_3769_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_dec(v_l_3769_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 4, v_r_3933_);
lean_ctor_set(v___x_3962_, 3, v___x_3960_);
lean_ctor_set(v___x_3962_, 2, v_v_3931_);
lean_ctor_set(v___x_3962_, 1, v_k_3930_);
lean_ctor_set(v___x_3962_, 0, v___x_3957_);
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3966_, 4, v_r_3933_);
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
}
}
else
{
lean_object* v_l_3980_; 
v_l_3980_ = lean_ctor_get(v_impl_3926_, 3);
lean_inc(v_l_3980_);
if (lean_obj_tag(v_l_3980_) == 0)
{
lean_object* v_r_3981_; lean_object* v_k_3982_; lean_object* v_v_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4004_; 
v_r_3981_ = lean_ctor_get(v_impl_3926_, 4);
v_k_3982_ = lean_ctor_get(v_impl_3926_, 1);
v_v_3983_ = lean_ctor_get(v_impl_3926_, 2);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_impl_3926_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4005_ = lean_ctor_get(v_impl_3926_, 3);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_impl_3926_, 0);
lean_dec(v_unused_4006_);
v___x_3985_ = v_impl_3926_;
v_isShared_3986_ = v_isSharedCheck_4004_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_r_3981_);
lean_inc(v_v_3983_);
lean_inc(v_k_3982_);
lean_dec(v_impl_3926_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4004_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v_k_3987_; lean_object* v_v_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4000_; 
v_k_3987_ = lean_ctor_get(v_l_3980_, 1);
v_v_3988_ = lean_ctor_get(v_l_3980_, 2);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_l_3980_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; 
v_unused_4001_ = lean_ctor_get(v_l_3980_, 4);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_l_3980_, 3);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_l_3980_, 0);
lean_dec(v_unused_4003_);
v___x_3990_ = v_l_3980_;
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_v_3988_);
lean_inc(v_k_3987_);
lean_dec(v_l_3980_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3992_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3981_, 2);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 4, v_r_3981_);
lean_ctor_set(v___x_3990_, 3, v_r_3981_);
lean_ctor_set(v___x_3990_, 2, v_v_3768_);
lean_ctor_set(v___x_3990_, 1, v_k_3767_);
lean_ctor_set(v___x_3990_, 0, v___x_3927_);
v___x_3994_ = v___x_3990_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v_r_3981_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v_r_3981_);
v___x_3994_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
lean_inc(v_r_3981_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 3, v_r_3981_);
lean_ctor_set(v___x_3985_, 0, v___x_3927_);
v___x_3996_ = v___x_3985_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_k_3982_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_v_3983_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_r_3981_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v_r_3981_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3992_);
lean_ctor_set(v___x_3997_, 1, v_k_3987_);
lean_ctor_set(v___x_3997_, 2, v_v_3988_);
lean_ctor_set(v___x_3997_, 3, v___x_3994_);
lean_ctor_set(v___x_3997_, 4, v___x_3996_);
return v___x_3997_;
}
}
}
}
}
else
{
lean_object* v_r_4007_; 
v_r_4007_ = lean_ctor_get(v_impl_3926_, 4);
lean_inc(v_r_4007_);
if (lean_obj_tag(v_r_4007_) == 0)
{
lean_object* v_k_4008_; lean_object* v_v_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4018_; 
v_k_4008_ = lean_ctor_get(v_impl_3926_, 1);
v_v_4009_ = lean_ctor_get(v_impl_3926_, 2);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_impl_3926_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; lean_object* v_unused_4020_; lean_object* v_unused_4021_; 
v_unused_4019_ = lean_ctor_get(v_impl_3926_, 4);
lean_dec(v_unused_4019_);
v_unused_4020_ = lean_ctor_get(v_impl_3926_, 3);
lean_dec(v_unused_4020_);
v_unused_4021_ = lean_ctor_get(v_impl_3926_, 0);
lean_dec(v_unused_4021_);
v___x_4011_ = v_impl_3926_;
v_isShared_4012_ = v_isSharedCheck_4018_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_v_4009_);
lean_inc(v_k_4008_);
lean_dec(v_impl_3926_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4018_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4013_ = lean_unsigned_to_nat(3u);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 4, v_l_3980_);
lean_ctor_set(v___x_4011_, 2, v_v_3768_);
lean_ctor_set(v___x_4011_, 1, v_k_3767_);
lean_ctor_set(v___x_4011_, 0, v___x_3927_);
v___x_4015_ = v___x_4011_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v_l_3980_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v_l_3980_);
v___x_4015_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4013_);
lean_ctor_set(v___x_4016_, 1, v_k_4008_);
lean_ctor_set(v___x_4016_, 2, v_v_4009_);
lean_ctor_set(v___x_4016_, 3, v___x_4015_);
lean_ctor_set(v___x_4016_, 4, v_r_4007_);
return v___x_4016_;
}
}
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = lean_unsigned_to_nat(2u);
v___x_4023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
lean_ctor_set(v___x_4023_, 1, v_k_3767_);
lean_ctor_set(v___x_4023_, 2, v_v_3768_);
lean_ctor_set(v___x_4023_, 3, v_r_4007_);
lean_ctor_set(v___x_4023_, 4, v_impl_3926_);
return v___x_4023_;
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
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_unsigned_to_nat(1u);
v___x_4032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
lean_ctor_set(v___x_4032_, 1, v_k_3749_);
lean_ctor_set(v___x_4032_, 2, v_v_3750_);
lean_ctor_set(v___x_4032_, 3, v_t_3751_);
lean_ctor_set(v___x_4032_, 4, v_t_3751_);
return v___x_4032_;
}
v___jp_3752_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = lean_nat_add(v___y_3758_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec(v___y_3758_);
v___x_3764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v___y_3757_);
lean_ctor_set(v___x_3764_, 2, v___y_3760_);
lean_ctor_set(v___x_3764_, 3, v___y_3753_);
lean_ctor_set(v___x_3764_, 4, v___y_3761_);
v___x_3765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3765_, 0, v___y_3756_);
lean_ctor_set(v___x_3765_, 1, v___y_3754_);
lean_ctor_set(v___x_3765_, 2, v___y_3759_);
lean_ctor_set(v___x_3765_, 3, v___y_3755_);
lean_ctor_set(v___x_3765_, 4, v___x_3764_);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4033_, lean_object* v_k_4034_, lean_object* v_fallback_4035_){
_start:
{
if (lean_obj_tag(v_t_4033_) == 0)
{
lean_object* v_k_4036_; lean_object* v_v_4037_; lean_object* v_l_4038_; lean_object* v_r_4039_; uint8_t v___y_4041_; lean_object* v_fst_4044_; lean_object* v_snd_4045_; lean_object* v_fst_4046_; lean_object* v_snd_4047_; uint8_t v___x_4048_; 
v_k_4036_ = lean_ctor_get(v_t_4033_, 1);
v_v_4037_ = lean_ctor_get(v_t_4033_, 2);
v_l_4038_ = lean_ctor_get(v_t_4033_, 3);
v_r_4039_ = lean_ctor_get(v_t_4033_, 4);
v_fst_4044_ = lean_ctor_get(v_k_4034_, 0);
v_snd_4045_ = lean_ctor_get(v_k_4034_, 1);
v_fst_4046_ = lean_ctor_get(v_k_4036_, 0);
v_snd_4047_ = lean_ctor_get(v_k_4036_, 1);
v___x_4048_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4044_, v_fst_4046_);
if (v___x_4048_ == 1)
{
uint8_t v___x_4049_; 
v___x_4049_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4045_, v_snd_4047_);
v___y_4041_ = v___x_4049_;
goto v___jp_4040_;
}
else
{
v___y_4041_ = v___x_4048_;
goto v___jp_4040_;
}
v___jp_4040_:
{
switch(v___y_4041_)
{
case 0:
{
v_t_4033_ = v_l_4038_;
goto _start;
}
case 1:
{
lean_inc(v_v_4037_);
return v_v_4037_;
}
default: 
{
v_t_4033_ = v_r_4039_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4035_);
return v_fallback_4035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4050_, lean_object* v_k_4051_, lean_object* v_fallback_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4050_, v_k_4051_, v_fallback_4052_);
lean_dec(v_fallback_4052_);
lean_dec_ref(v_k_4051_);
lean_dec(v_t_4050_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4054_, lean_object* v_as_4055_, size_t v_sz_4056_, size_t v_i_4057_, lean_object* v_b_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v___x_4062_; 
v___x_4062_ = lean_usize_dec_lt(v_i_4057_, v_sz_4056_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec(v___x_4054_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_b_4058_);
return v___x_4063_;
}
else
{
lean_object* v_a_4064_; lean_object* v_fst_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4093_; 
v_a_4064_ = lean_array_uget(v_as_4055_, v_i_4057_);
v_fst_4065_ = lean_ctor_get(v_a_4064_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_a_4064_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_a_4064_, 1);
lean_dec(v_unused_4094_);
v___x_4067_ = v_a_4064_;
v_isShared_4068_ = v_isSharedCheck_4093_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_fst_4065_);
lean_dec(v_a_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4093_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; 
lean_inc(v_fst_4065_);
v___x_4069_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4065_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; lean_object* v___y_4073_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_a_4070_) == 0)
{
lean_inc(v___x_4054_);
v___y_4073_ = v___x_4054_;
goto v___jp_4072_;
}
else
{
lean_object* v_val_4084_; 
v_val_4084_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_val_4084_);
lean_dec_ref_known(v_a_4070_, 1);
v___y_4073_ = v_val_4084_;
goto v___jp_4072_;
}
v___jp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 1, v_fst_4065_);
lean_ctor_set(v___x_4067_, 0, v___y_4073_);
v___x_4075_ = v___x_4067_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___y_4073_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_fst_4065_);
v___x_4075_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; size_t v___x_4080_; size_t v___x_4081_; 
v___x_4076_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4058_, v___x_4075_, v___x_4071_);
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_add(v___x_4076_, v___x_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4075_, v___x_4078_, v_b_4058_);
v___x_4080_ = ((size_t)1ULL);
v___x_4081_ = lean_usize_add(v_i_4057_, v___x_4080_);
v_i_4057_ = v___x_4081_;
v_b_4058_ = v___x_4079_;
goto _start;
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_del_object(v___x_4067_);
lean_dec(v_fst_4065_);
lean_dec(v_b_4058_);
lean_dec(v___x_4054_);
v_a_4085_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4069_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4069_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4095_, lean_object* v_as_4096_, lean_object* v_sz_4097_, lean_object* v_i_4098_, lean_object* v_b_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
size_t v_sz_boxed_4103_; size_t v_i_boxed_4104_; lean_object* v_res_4105_; 
v_sz_boxed_4103_ = lean_unbox_usize(v_sz_4097_);
lean_dec(v_sz_4097_);
v_i_boxed_4104_ = lean_unbox_usize(v_i_4098_);
lean_dec(v_i_4098_);
v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4095_, v_as_4096_, v_sz_boxed_4103_, v_i_boxed_4104_, v_b_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec_ref(v_as_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4106_, lean_object* v_init_4107_, lean_object* v_x_4108_){
_start:
{
if (lean_obj_tag(v_x_4108_) == 0)
{
lean_object* v_k_4110_; lean_object* v_v_4111_; lean_object* v_l_4112_; lean_object* v_r_4113_; lean_object* v___x_4114_; lean_object* v_a_4115_; lean_object* v_a_4116_; lean_object* v_fst_4117_; lean_object* v_snd_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4133_; 
v_k_4110_ = lean_ctor_get(v_x_4108_, 1);
lean_inc(v_k_4110_);
v_v_4111_ = lean_ctor_get(v_x_4108_, 2);
lean_inc(v_v_4111_);
v_l_4112_ = lean_ctor_get(v_x_4108_, 3);
lean_inc(v_l_4112_);
v_r_4113_ = lean_ctor_get(v_x_4108_, 4);
lean_inc(v_r_4113_);
lean_dec_ref_known(v_x_4108_, 5);
lean_inc_ref(v_fst_4106_);
v___x_4114_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4106_, v_init_4107_, v_l_4112_);
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref(v___x_4114_);
v_a_4116_ = lean_ctor_get(v_a_4115_, 0);
lean_inc(v_a_4116_);
lean_dec(v_a_4115_);
v_fst_4117_ = lean_ctor_get(v_k_4110_, 0);
v_snd_4118_ = lean_ctor_get(v_k_4110_, 1);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_k_4110_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4120_ = v_k_4110_;
v_isShared_4121_ = v_isSharedCheck_4133_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_snd_4118_);
lean_inc(v_fst_4117_);
lean_dec(v_k_4110_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4133_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v_optName_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v_optName_4122_ = lean_ctor_get(v_fst_4106_, 1);
v___x_4123_ = 1;
lean_inc(v_optName_4122_);
v___x_4124_ = l_Lean_Name_toString(v_optName_4122_, v___x_4123_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set_tag(v___x_4120_, 1);
v___x_4126_ = v___x_4120_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fst_4117_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_snd_4118_);
v___x_4126_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
double v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4127_ = lean_float_of_nat(v_v_4111_);
v___x_4128_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4128_, 0, v___x_4127_);
v___x_4129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4124_);
lean_ctor_set(v___x_4129_, 1, v___x_4126_);
lean_ctor_set(v___x_4129_, 2, v___x_4128_);
v___x_4130_ = lean_array_push(v_a_4116_, v___x_4129_);
v_init_4107_ = v___x_4130_;
v_x_4108_ = v_r_4113_;
goto _start;
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v_fst_4106_);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_init_4107_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4136_, lean_object* v_init_4137_, lean_object* v_x_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4136_, v_init_4137_, v_x_4138_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4141_, lean_object* v_as_4142_, size_t v_sz_4143_, size_t v_i_4144_, lean_object* v_b_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_a_4150_; uint8_t v___x_4154_; 
v___x_4154_ = lean_usize_dec_lt(v_i_4144_, v_sz_4143_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
lean_dec(v___x_4141_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_b_4145_);
return v___x_4155_;
}
else
{
lean_object* v_a_4156_; lean_object* v_snd_4157_; lean_object* v_fst_4158_; lean_object* v_size_4159_; lean_object* v_buckets_4160_; lean_object* v___x_4161_; lean_object* v___y_4163_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v_a_4156_ = lean_array_uget_borrowed(v_as_4142_, v_i_4144_);
v_snd_4157_ = lean_ctor_get(v_a_4156_, 1);
v_fst_4158_ = lean_ctor_get(v_a_4156_, 0);
v_size_4159_ = lean_ctor_get(v_snd_4157_, 0);
v_buckets_4160_ = lean_ctor_get(v_snd_4157_, 1);
v___x_4161_ = lean_box(1);
v___x_4197_ = lean_mk_empty_array_with_capacity(v_size_4159_);
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = lean_array_get_size(v_buckets_4160_);
v___x_4200_ = lean_nat_dec_lt(v___x_4198_, v___x_4199_);
if (v___x_4200_ == 0)
{
v___y_4163_ = v___x_4197_;
goto v___jp_4162_;
}
else
{
size_t v___x_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v___x_4201_ = ((size_t)0ULL);
v___x_4202_ = lean_usize_of_nat(v___x_4199_);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4160_, v___x_4201_, v___x_4202_, v___x_4197_);
v___y_4163_ = v___x_4203_;
goto v___jp_4162_;
}
v___jp_4162_:
{
size_t v_sz_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v_sz_4164_ = lean_array_size(v___y_4163_);
v___x_4165_ = ((size_t)0ULL);
lean_inc(v___x_4141_);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4141_, v___y_4163_, v_sz_4164_, v___x_4165_, v___x_4161_, v___y_4146_, v___y_4147_);
lean_dec_ref(v___y_4163_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
lean_inc(v_fst_4158_);
v___x_4168_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4158_, v_b_4145_, v_a_4167_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v_a_4170_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v_a_4170_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_a_4170_);
lean_dec(v_a_4169_);
v_a_4150_ = v_a_4170_;
goto v___jp_4149_;
}
else
{
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4180_; 
v_a_4171_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4173_ = v___x_4168_;
v_isShared_4174_ = v_isSharedCheck_4180_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4168_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4180_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
if (lean_obj_tag(v_a_4171_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; 
lean_dec(v___x_4141_);
v_a_4175_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v_a_4171_, 1);
if (v_isShared_4174_ == 0)
{
lean_ctor_set_tag(v___x_4173_, 0);
lean_ctor_set(v___x_4173_, 0, v_a_4175_);
v___x_4177_ = v___x_4173_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
lean_object* v_a_4179_; 
lean_del_object(v___x_4173_);
v_a_4179_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v_a_4171_, 1);
v_a_4150_ = v_a_4179_;
goto v___jp_4149_;
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v___x_4141_);
v_a_4181_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4168_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4168_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v_b_4145_);
lean_dec(v___x_4141_);
v_a_4189_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4166_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4166_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
v___jp_4149_:
{
size_t v___x_4151_; size_t v___x_4152_; 
v___x_4151_ = ((size_t)1ULL);
v___x_4152_ = lean_usize_add(v_i_4144_, v___x_4151_);
v_i_4144_ = v___x_4152_;
v_b_4145_ = v_a_4150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4204_, lean_object* v_as_4205_, lean_object* v_sz_4206_, lean_object* v_i_4207_, lean_object* v_b_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
size_t v_sz_boxed_4212_; size_t v_i_boxed_4213_; lean_object* v_res_4214_; 
v_sz_boxed_4212_ = lean_unbox_usize(v_sz_4206_);
lean_dec(v_sz_4206_);
v_i_boxed_4213_ = lean_unbox_usize(v_i_4207_);
lean_dec(v_i_4207_);
v_res_4214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4204_, v_as_4205_, v_sz_boxed_4212_, v_i_boxed_4213_, v_b_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec_ref(v_as_4205_);
return v_res_4214_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4221_ = l_Lean_maxRecDepth;
v___x_4222_ = l_Lean_Options_empty;
v___x_4223_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v___x_4222_, v___x_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4224_, lean_object* v_linterOpts_4225_, lean_object* v_sp_4226_, lean_object* v_env_4227_, lean_object* v_mod_4228_){
_start:
{
lean_object* v_msg_4231_; lean_object* v_a_4236_; lean_object* v_a_4240_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v_a_4271_; lean_object* v___y_4275_; uint8_t v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; uint8_t v___y_4283_; lean_object* v___y_4284_; uint8_t v___y_4285_; lean_object* v___y_4355_; lean_object* v___y_4356_; uint8_t v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; uint8_t v___y_4360_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_env_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; uint8_t v___x_4379_; lean_object* v___y_4381_; lean_object* v___y_4382_; uint8_t v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___x_4410_; uint8_t v___x_4411_; lean_object* v_fileName_4413_; lean_object* v_fileMap_4414_; lean_object* v_currNamespace_4415_; lean_object* v_openDecls_4416_; lean_object* v_initHeartbeats_4417_; lean_object* v_maxHeartbeats_4418_; lean_object* v_quotContext_4419_; lean_object* v_currMacroScope_4420_; lean_object* v_cancelTk_x3f_4421_; lean_object* v_inheritedTraceOptions_4422_; lean_object* v_currRecDepth_4423_; lean_object* v_ref_4424_; uint8_t v_suppressElabErrors_4425_; lean_object* v___y_4426_; uint8_t v___y_4443_; uint8_t v___x_4463_; 
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4256_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4257_ = lean_io_get_num_heartbeats();
v___x_4258_ = l_Lean_firstFrontendMacroScope;
v___x_4259_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4260_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4261_ = lean_box(0);
v___x_4262_ = lean_box(0);
v___x_4263_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4264_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4265_ = 1;
v___x_4266_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4267_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4268_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4268_, 0, v_env_4227_);
lean_ctor_set(v___x_4268_, 1, v___x_4259_);
lean_ctor_set(v___x_4268_, 2, v___x_4260_);
lean_ctor_set(v___x_4268_, 3, v___x_4263_);
lean_ctor_set(v___x_4268_, 4, v___x_4264_);
lean_ctor_set(v___x_4268_, 5, v___x_4255_);
lean_ctor_set(v___x_4268_, 6, v___x_4256_);
lean_ctor_set(v___x_4268_, 7, v___x_4266_);
lean_ctor_set(v___x_4268_, 8, v___x_4267_);
v___x_4269_ = lean_st_mk_ref(v___x_4268_);
v___x_4369_ = l_Lean_inheritedTraceOptions;
v___x_4370_ = lean_st_ref_get(v___x_4369_);
v___x_4371_ = lean_st_ref_get(v___x_4269_);
v_env_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc_ref(v_env_4372_);
lean_dec(v___x_4371_);
v___x_4373_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4374_ = l_Lean_instInhabitedFileMap_default;
v___x_4375_ = l_Lean_Options_empty;
v___x_4376_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4377_ = lean_box(0);
v___x_4378_ = lean_box(0);
v___x_4379_ = 0;
v___x_4410_ = l_Lean_Name_getRoot(v_mod_4228_);
v___x_4411_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4463_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4372_);
lean_dec_ref(v_env_4372_);
if (v___x_4411_ == 0)
{
if (v___x_4463_ == 0)
{
lean_inc(v___x_4269_);
v_fileName_4413_ = v___x_4373_;
v_fileMap_4414_ = v___x_4374_;
v_currNamespace_4415_ = v___x_4261_;
v_openDecls_4416_ = v___x_4262_;
v_initHeartbeats_4417_ = v___x_4257_;
v_maxHeartbeats_4418_ = v___x_4376_;
v_quotContext_4419_ = v___x_4261_;
v_currMacroScope_4420_ = v___x_4258_;
v_cancelTk_x3f_4421_ = v___x_4377_;
v_inheritedTraceOptions_4422_ = v___x_4370_;
v_currRecDepth_4423_ = v___x_4254_;
v_ref_4424_ = v___x_4378_;
v_suppressElabErrors_4425_ = v___x_4379_;
v___y_4426_ = v___x_4269_;
goto v___jp_4412_;
}
else
{
v___y_4443_ = v___x_4411_;
goto v___jp_4442_;
}
}
else
{
v___y_4443_ = v___x_4463_;
goto v___jp_4442_;
}
v___jp_4230_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = l_Lean_MessageData_toString(v_msg_4231_);
v___x_4233_ = lean_mk_io_user_error(v___x_4232_);
v___x_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
return v___x_4234_;
}
v___jp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_mk_io_user_error(v_a_4236_);
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
v___jp_4239_:
{
if (lean_obj_tag(v_a_4240_) == 0)
{
lean_object* v_msg_4241_; 
v_msg_4241_ = lean_ctor_get(v_a_4240_, 1);
lean_inc_ref(v_msg_4241_);
lean_dec_ref_known(v_a_4240_, 2);
v_msg_4231_ = v_msg_4241_;
goto v___jp_4230_;
}
else
{
lean_object* v_id_4242_; lean_object* v___x_4243_; 
v_id_4242_ = lean_ctor_get(v_a_4240_, 0);
lean_inc(v_id_4242_);
lean_dec_ref_known(v_a_4240_, 2);
v___x_4243_ = l_Lean_InternalExceptionId_getName(v_id_4242_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
lean_dec(v_id_4242_);
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v___x_4245_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4246_ = 1;
v___x_4247_ = l_Lean_Name_toString(v_a_4244_, v___x_4246_);
v___x_4248_ = lean_string_append(v___x_4245_, v___x_4247_);
lean_dec_ref(v___x_4247_);
v_a_4236_ = v___x_4248_;
goto v___jp_4235_;
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec_ref_known(v___x_4243_, 1);
v___x_4249_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4250_ = l_Nat_reprFast(v_id_4242_);
v___x_4251_ = lean_string_append(v___x_4249_, v___x_4250_);
lean_dec_ref(v___x_4250_);
v___x_4252_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4253_ = lean_string_append(v___x_4251_, v___x_4252_);
v_a_4236_ = v___x_4253_;
goto v___jp_4235_;
}
}
}
v___jp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_st_ref_get(v___x_4269_);
lean_dec(v___x_4269_);
lean_dec(v___x_4272_);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_a_4271_);
return v___x_4273_;
}
v___jp_4274_:
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___y_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___y_4275_);
v_a_4271_ = v_a_4276_;
goto v___jp_4270_;
}
v___jp_4277_:
{
switch(v___y_4283_)
{
case 0:
{
lean_dec(v_sp_4226_);
if (v___y_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4279_);
v___x_4286_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4228_, v___x_4265_);
v___x_4288_ = lean_string_append(v___x_4286_, v___x_4287_);
lean_dec_ref(v___x_4287_);
v___x_4289_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4290_ = lean_string_append(v___x_4288_, v___x_4289_);
v___x_4291_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4290_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4285_, v_a_4292_, v___y_4284_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4284_);
v___y_4275_ = v___x_4293_;
goto v___jp_4274_;
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4303_; 
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4281_);
lean_dec(v___x_4269_);
v_a_4294_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4296_ = v___x_4291_;
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4291_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4303_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4298_ = lean_io_error_to_string(v_a_4294_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 3);
lean_ctor_set(v___x_4296_, 0, v___x_4298_);
v___x_4300_ = v___x_4296_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_MessageData_ofFormat(v___x_4300_);
v_msg_4231_ = v___x_4301_;
goto v___jp_4230_;
}
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4304_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4228_, v___y_4285_);
v___x_4306_ = lean_string_append(v___x_4304_, v___x_4305_);
lean_dec_ref(v___x_4305_);
v___x_4307_ = lean_array_get_size(v___y_4282_);
lean_dec_ref(v___y_4282_);
v___x_4308_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4280_, v___y_4279_, v___x_4265_, v___x_4306_, v___x_4307_, v___x_4265_, v___y_4284_, v___y_4281_);
lean_dec_ref(v___y_4279_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v___x_4310_ = l_Lean_MessageData_toString(v_a_4309_);
v___x_4311_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4310_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4285_, v_a_4312_, v___y_4284_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4284_);
v___y_4275_ = v___x_4313_;
goto v___jp_4274_;
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4281_);
lean_dec(v___x_4269_);
v_a_4314_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4316_ = v___x_4311_;
v_isShared_4317_ = v_isSharedCheck_4323_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4311_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4323_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v___x_4320_; 
v___x_4318_ = lean_io_error_to_string(v_a_4314_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 3);
lean_ctor_set(v___x_4316_, 0, v___x_4318_);
v___x_4320_ = v___x_4316_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_MessageData_ofFormat(v___x_4320_);
v_msg_4231_ = v___x_4321_;
goto v___jp_4230_;
}
}
}
}
else
{
lean_object* v_a_4324_; 
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4281_);
lean_dec(v___x_4269_);
v_a_4324_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4308_, 1);
v_a_4240_ = v_a_4324_;
goto v___jp_4239_;
}
}
}
case 1:
{
lean_object* v___x_4325_; lean_object* v_env_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; size_t v_sz_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4279_);
lean_dec(v_mod_4228_);
v___x_4325_ = lean_st_ref_get(v___y_4281_);
v_env_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_ref(v_env_4326_);
lean_dec(v___x_4325_);
v___x_4327_ = l_Lean_Environment_mainModule(v_env_4326_);
lean_dec_ref(v_env_4326_);
v___x_4328_ = lean_box(v___y_4278_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4267_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v_sz_4330_ = lean_array_size(v___y_4280_);
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4226_, v___x_4327_, v___y_4280_, v_sz_4330_, v___x_4331_, v___x_4329_, v___y_4284_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4280_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v_fst_4334_; lean_object* v_snd_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
v_fst_4334_ = lean_ctor_get(v_a_4333_, 0);
lean_inc(v_fst_4334_);
v_snd_4335_ = lean_ctor_get(v_a_4333_, 1);
lean_inc(v_snd_4335_);
lean_dec(v_a_4333_);
v___x_4336_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4336_, 0, v_fst_4334_);
v___x_4337_ = lean_unbox(v_snd_4335_);
lean_dec(v_snd_4335_);
lean_ctor_set_uint8(v___x_4336_, sizeof(void*)*1, v___x_4337_);
v_a_4271_ = v___x_4336_;
goto v___jp_4270_;
}
else
{
lean_object* v_a_4338_; 
lean_dec(v___x_4269_);
v_a_4338_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4332_, 1);
v_a_4240_ = v_a_4338_;
goto v___jp_4239_;
}
}
default: 
{
lean_object* v___x_4339_; lean_object* v_env_4340_; lean_object* v___x_4341_; size_t v_sz_4342_; size_t v___x_4343_; lean_object* v___x_4344_; 
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4279_);
lean_dec(v_mod_4228_);
lean_dec(v_sp_4226_);
v___x_4339_ = lean_st_ref_get(v___y_4281_);
v_env_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc_ref(v_env_4340_);
lean_dec(v___x_4339_);
v___x_4341_ = l_Lean_Environment_mainModule(v_env_4340_);
lean_dec_ref(v_env_4340_);
v_sz_4342_ = lean_array_size(v___y_4280_);
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4341_, v___y_4280_, v_sz_4342_, v___x_4343_, v___x_4267_, v___y_4284_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4280_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4344_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4344_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set_tag(v___x_4347_, 2);
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
v_a_4271_ = v___x_4350_;
goto v___jp_4270_;
}
}
}
else
{
lean_object* v_a_4353_; 
lean_dec(v___x_4269_);
v_a_4353_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4344_, 1);
v_a_4240_ = v_a_4353_;
goto v___jp_4239_;
}
}
}
}
v___jp_4354_:
{
lean_object* v___x_4361_; 
lean_inc_ref(v___y_4358_);
v___x_4361_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4355_, v___y_4358_, v___y_4359_, v___y_4356_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___x_4363_ = lean_array_get_size(v_a_4362_);
v___x_4364_ = lean_nat_dec_lt(v___x_4254_, v___x_4363_);
if (v___x_4364_ == 0)
{
v___y_4278_ = v___y_4360_;
v___y_4279_ = v___y_4355_;
v___y_4280_ = v_a_4362_;
v___y_4281_ = v___y_4356_;
v___y_4282_ = v___y_4358_;
v___y_4283_ = v___y_4357_;
v___y_4284_ = v___y_4359_;
v___y_4285_ = v___x_4364_;
goto v___jp_4277_;
}
else
{
if (v___x_4364_ == 0)
{
v___y_4278_ = v___y_4360_;
v___y_4279_ = v___y_4355_;
v___y_4280_ = v_a_4362_;
v___y_4281_ = v___y_4356_;
v___y_4282_ = v___y_4358_;
v___y_4283_ = v___y_4357_;
v___y_4284_ = v___y_4359_;
v___y_4285_ = v___x_4364_;
goto v___jp_4277_;
}
else
{
size_t v___x_4365_; size_t v___x_4366_; uint8_t v___x_4367_; 
v___x_4365_ = ((size_t)0ULL);
v___x_4366_ = lean_usize_of_nat(v___x_4363_);
v___x_4367_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4360_, v_a_4362_, v___x_4365_, v___x_4366_);
v___y_4278_ = v___y_4360_;
v___y_4279_ = v___y_4355_;
v___y_4280_ = v_a_4362_;
v___y_4281_ = v___y_4356_;
v___y_4282_ = v___y_4358_;
v___y_4283_ = v___y_4357_;
v___y_4284_ = v___y_4359_;
v___y_4285_ = v___x_4367_;
goto v___jp_4277_;
}
}
}
else
{
lean_object* v_a_4368_; 
lean_dec_ref(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___x_4269_);
lean_dec(v_mod_4228_);
lean_dec(v_sp_4226_);
v_a_4368_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4361_, 1);
v_a_4240_ = v_a_4368_;
goto v___jp_4239_;
}
}
v___jp_4380_:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4385_, v___y_4384_, v___y_4382_);
lean_dec(v___y_4385_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
v___x_4388_ = lean_array_get_size(v_a_4387_);
v___x_4389_ = lean_nat_dec_eq(v___x_4388_, v___x_4254_);
if (v___x_4389_ == 0)
{
v___y_4355_ = v___y_4381_;
v___y_4356_ = v___y_4382_;
v___y_4357_ = v___y_4383_;
v___y_4358_ = v_a_4387_;
v___y_4359_ = v___y_4384_;
v___y_4360_ = v___x_4389_;
goto v___jp_4354_;
}
else
{
uint8_t v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = 0;
v___x_4391_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4383_, v___x_4390_);
if (v___x_4391_ == 0)
{
v___y_4355_ = v___y_4381_;
v___y_4356_ = v___y_4382_;
v___y_4357_ = v___y_4383_;
v___y_4358_ = v_a_4387_;
v___y_4359_ = v___y_4384_;
v___y_4360_ = v___x_4391_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_dec(v_a_4387_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v_sp_4226_);
v___x_4392_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4228_, v___x_4391_);
v___x_4394_ = lean_string_append(v___x_4392_, v___x_4393_);
lean_dec_ref(v___x_4393_);
v___x_4395_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4396_ = lean_string_append(v___x_4394_, v___x_4395_);
v___x_4397_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4396_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v___x_4398_; 
lean_dec_ref_known(v___x_4397_, 1);
v___x_4398_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4271_ = v___x_4398_;
goto v___jp_4270_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v___x_4269_);
v_a_4399_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4401_ = v___x_4397_;
v_isShared_4402_ = v_isSharedCheck_4408_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4397_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4408_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4403_ = lean_io_error_to_string(v_a_4399_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 3);
lean_ctor_set(v___x_4401_, 0, v___x_4403_);
v___x_4405_ = v___x_4401_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_MessageData_ofFormat(v___x_4405_);
v_msg_4231_ = v___x_4406_;
goto v___jp_4230_;
}
}
}
}
}
}
else
{
lean_object* v_a_4409_; 
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___x_4269_);
lean_dec(v_mod_4228_);
lean_dec(v_sp_4226_);
v_a_4409_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4386_, 1);
v_a_4240_ = v_a_4409_;
goto v___jp_4239_;
}
}
v___jp_4412_:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4410_, v___y_4426_);
lean_dec(v___x_4410_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4440_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4430_ = v___x_4427_;
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4440_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
uint8_t v_lintOnly_4432_; uint8_t v_mode_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_lintOnly_4432_ = lean_ctor_get_uint8(v_args_4224_, sizeof(void*)*4);
v_mode_4433_ = lean_ctor_get_uint8(v_args_4224_, sizeof(void*)*4 + 1);
v___x_4434_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4420_);
lean_inc(v_quotContext_4419_);
lean_inc(v_maxHeartbeats_4418_);
lean_inc(v_openDecls_4416_);
lean_inc(v_currNamespace_4415_);
lean_inc_ref(v_fileMap_4414_);
lean_inc_ref(v_fileName_4413_);
v___x_4435_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4435_, 0, v_fileName_4413_);
lean_ctor_set(v___x_4435_, 1, v_fileMap_4414_);
lean_ctor_set(v___x_4435_, 2, v___x_4375_);
lean_ctor_set(v___x_4435_, 3, v___x_4434_);
lean_ctor_set(v___x_4435_, 4, v_currNamespace_4415_);
lean_ctor_set(v___x_4435_, 5, v_openDecls_4416_);
lean_ctor_set(v___x_4435_, 6, v_initHeartbeats_4417_);
lean_ctor_set(v___x_4435_, 7, v_maxHeartbeats_4418_);
lean_ctor_set(v___x_4435_, 8, v_quotContext_4419_);
lean_ctor_set(v___x_4435_, 9, v_currMacroScope_4420_);
lean_ctor_set(v___x_4435_, 10, v_cancelTk_x3f_4421_);
lean_ctor_set(v___x_4435_, 11, v_inheritedTraceOptions_4422_);
lean_inc(v_ref_4424_);
v___x_4436_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
lean_ctor_set(v___x_4436_, 1, v_currRecDepth_4423_);
lean_ctor_set(v___x_4436_, 2, v_ref_4424_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*3, v___x_4411_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*3 + 1, v_suppressElabErrors_4425_);
if (v_lintOnly_4432_ == 0)
{
lean_del_object(v___x_4430_);
lean_dec_ref(v_linterOpts_4225_);
v___y_4381_ = v_a_4428_;
v___y_4382_ = v___y_4426_;
v___y_4383_ = v_mode_4433_;
v___y_4384_ = v___x_4436_;
v___y_4385_ = v___x_4377_;
goto v___jp_4380_;
}
else
{
lean_object* v___x_4438_; 
if (v_isShared_4431_ == 0)
{
lean_ctor_set_tag(v___x_4430_, 1);
lean_ctor_set(v___x_4430_, 0, v_linterOpts_4225_);
v___x_4438_ = v___x_4430_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_linterOpts_4225_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
v___y_4381_ = v_a_4428_;
v___y_4382_ = v___y_4426_;
v___y_4383_ = v_mode_4433_;
v___y_4384_ = v___x_4436_;
v___y_4385_ = v___x_4438_;
goto v___jp_4380_;
}
}
}
}
else
{
lean_object* v_a_4441_; 
lean_dec(v___y_4426_);
lean_dec(v_currRecDepth_4423_);
lean_dec_ref(v_inheritedTraceOptions_4422_);
lean_dec(v_cancelTk_x3f_4421_);
lean_dec(v_initHeartbeats_4417_);
lean_dec(v___x_4269_);
lean_dec(v_mod_4228_);
lean_dec(v_sp_4226_);
lean_dec_ref(v_linterOpts_4225_);
v_a_4441_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4427_, 1);
v_a_4240_ = v_a_4441_;
goto v___jp_4239_;
}
}
v___jp_4442_:
{
if (v___y_4443_ == 0)
{
lean_object* v___x_4444_; lean_object* v_env_4445_; lean_object* v_nextMacroScope_4446_; lean_object* v_ngen_4447_; lean_object* v_auxDeclNGen_4448_; lean_object* v_traceState_4449_; lean_object* v_messages_4450_; lean_object* v_infoState_4451_; lean_object* v_snapshotTasks_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4461_; 
v___x_4444_ = lean_st_ref_take(v___x_4269_);
v_env_4445_ = lean_ctor_get(v___x_4444_, 0);
v_nextMacroScope_4446_ = lean_ctor_get(v___x_4444_, 1);
v_ngen_4447_ = lean_ctor_get(v___x_4444_, 2);
v_auxDeclNGen_4448_ = lean_ctor_get(v___x_4444_, 3);
v_traceState_4449_ = lean_ctor_get(v___x_4444_, 4);
v_messages_4450_ = lean_ctor_get(v___x_4444_, 6);
v_infoState_4451_ = lean_ctor_get(v___x_4444_, 7);
v_snapshotTasks_4452_ = lean_ctor_get(v___x_4444_, 8);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v___x_4444_, 5);
lean_dec(v_unused_4462_);
v___x_4454_ = v___x_4444_;
v_isShared_4455_ = v_isSharedCheck_4461_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_snapshotTasks_4452_);
lean_inc(v_infoState_4451_);
lean_inc(v_messages_4450_);
lean_inc(v_traceState_4449_);
lean_inc(v_auxDeclNGen_4448_);
lean_inc(v_ngen_4447_);
lean_inc(v_nextMacroScope_4446_);
lean_inc(v_env_4445_);
lean_dec(v___x_4444_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4461_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4456_ = l_Lean_Kernel_enableDiag(v_env_4445_, v___x_4411_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 5, v___x_4255_);
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4458_ = v___x_4454_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_nextMacroScope_4446_);
lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_ngen_4447_);
lean_ctor_set(v_reuseFailAlloc_4460_, 3, v_auxDeclNGen_4448_);
lean_ctor_set(v_reuseFailAlloc_4460_, 4, v_traceState_4449_);
lean_ctor_set(v_reuseFailAlloc_4460_, 5, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4460_, 6, v_messages_4450_);
lean_ctor_set(v_reuseFailAlloc_4460_, 7, v_infoState_4451_);
lean_ctor_set(v_reuseFailAlloc_4460_, 8, v_snapshotTasks_4452_);
v___x_4458_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_st_ref_put(v___x_4269_, v___x_4458_);
lean_inc(v___x_4269_);
v_fileName_4413_ = v___x_4373_;
v_fileMap_4414_ = v___x_4374_;
v_currNamespace_4415_ = v___x_4261_;
v_openDecls_4416_ = v___x_4262_;
v_initHeartbeats_4417_ = v___x_4257_;
v_maxHeartbeats_4418_ = v___x_4376_;
v_quotContext_4419_ = v___x_4261_;
v_currMacroScope_4420_ = v___x_4258_;
v_cancelTk_x3f_4421_ = v___x_4377_;
v_inheritedTraceOptions_4422_ = v___x_4370_;
v_currRecDepth_4423_ = v___x_4254_;
v_ref_4424_ = v___x_4378_;
v_suppressElabErrors_4425_ = v___x_4379_;
v___y_4426_ = v___x_4269_;
goto v___jp_4412_;
}
}
}
else
{
lean_inc(v___x_4269_);
v_fileName_4413_ = v___x_4373_;
v_fileMap_4414_ = v___x_4374_;
v_currNamespace_4415_ = v___x_4261_;
v_openDecls_4416_ = v___x_4262_;
v_initHeartbeats_4417_ = v___x_4257_;
v_maxHeartbeats_4418_ = v___x_4376_;
v_quotContext_4419_ = v___x_4261_;
v_currMacroScope_4420_ = v___x_4258_;
v_cancelTk_x3f_4421_ = v___x_4377_;
v_inheritedTraceOptions_4422_ = v___x_4370_;
v_currRecDepth_4423_ = v___x_4254_;
v_ref_4424_ = v___x_4378_;
v_suppressElabErrors_4425_ = v___x_4379_;
v___y_4426_ = v___x_4269_;
goto v___jp_4412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4464_, lean_object* v_linterOpts_4465_, lean_object* v_sp_4466_, lean_object* v_env_4467_, lean_object* v_mod_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4464_, v_linterOpts_4465_, v_sp_4466_, v_env_4467_, v_mod_4468_);
lean_dec_ref(v_args_4464_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4471_, lean_object* v_t_4472_, lean_object* v_k_4473_, lean_object* v_fallback_4474_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4472_, v_k_4473_, v_fallback_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4476_, lean_object* v_t_4477_, lean_object* v_k_4478_, lean_object* v_fallback_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4476_, v_t_4477_, v_k_4478_, v_fallback_4479_);
lean_dec(v_fallback_4479_);
lean_dec_ref(v_k_4478_);
lean_dec(v_t_4477_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4481_, lean_object* v_k_4482_, lean_object* v_v_4483_, lean_object* v_t_4484_, lean_object* v_hl_4485_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4482_, v_v_4483_, v_t_4484_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4487_, lean_object* v_init_4488_, lean_object* v_x_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4487_, v_init_4488_, v_x_4489_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4494_, lean_object* v_init_4495_, lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4494_, v_init_4495_, v_x_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4501_, lean_object* v_constName_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4502_, v___y_4503_, v___y_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4507_, lean_object* v_constName_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4507_, v_constName_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4513_, lean_object* v_ref_4514_, lean_object* v_constName_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4514_, v_constName_4515_, v___y_4516_, v___y_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4520_, lean_object* v_ref_4521_, lean_object* v_constName_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4520_, v_ref_4521_, v_constName_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v_ref_4521_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4527_, lean_object* v_ref_4528_, lean_object* v_msg_4529_, lean_object* v_declHint_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4528_, v_msg_4529_, v_declHint_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4535_, lean_object* v_ref_4536_, lean_object* v_msg_4537_, lean_object* v_declHint_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4535_, v_ref_4536_, v_msg_4537_, v_declHint_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v_ref_4536_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4543_, lean_object* v_declHint_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4543_, v_declHint_4544_, v___y_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4549_, lean_object* v_declHint_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4549_, v_declHint_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4555_, lean_object* v_ref_4556_, lean_object* v_msg_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4556_, v_msg_4557_, v___y_4558_, v___y_4559_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4562_, lean_object* v_ref_4563_, lean_object* v_msg_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4562_, v_ref_4563_, v_msg_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v_ref_4563_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4569_, lean_object* v_msg_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4570_, v___y_4571_, v___y_4572_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4575_, lean_object* v_msg_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4575_, v_msg_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4581_){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; uint32_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4583_ = l_Std_Format_defWidth;
v___x_4584_ = lean_unsigned_to_nat(0u);
v___x_4585_ = l_Std_Format_pretty(v_s_4581_, v___x_4583_, v___x_4584_, v___x_4584_);
v___x_4586_ = 10;
v___x_4587_ = lean_string_push(v___x_4585_, v___x_4586_);
v___x_4588_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4587_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4589_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4592_, size_t v_sz_4593_, size_t v_i_4594_, lean_object* v_b_4595_, lean_object* v___y_4596_){
_start:
{
uint8_t v___x_4598_; 
v___x_4598_ = lean_usize_dec_lt(v_i_4594_, v_sz_4593_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v_b_4595_);
return v___x_4599_;
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v_a_4600_ = lean_array_uget_borrowed(v_as_4592_, v_i_4594_);
v___x_4601_ = lean_box(0);
lean_inc(v_a_4600_);
v___x_4602_ = l_Lean_MessageData_format(v_a_4600_, v___x_4601_);
v___x_4603_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4602_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v___x_4604_; size_t v___x_4605_; size_t v___x_4606_; 
lean_dec_ref_known(v___x_4603_, 1);
v___x_4604_ = lean_box(0);
v___x_4605_ = ((size_t)1ULL);
v___x_4606_ = lean_usize_add(v_i_4594_, v___x_4605_);
v_i_4594_ = v___x_4606_;
v_b_4595_ = v___x_4604_;
goto _start;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4620_; 
v_a_4608_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4610_ = v___x_4603_;
v_isShared_4611_ = v_isSharedCheck_4620_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4603_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4620_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v_ref_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v_ref_4612_ = lean_ctor_get(v___y_4596_, 2);
v___x_4613_ = lean_io_error_to_string(v_a_4608_);
v___x_4614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
v___x_4615_ = l_Lean_MessageData_ofFormat(v___x_4614_);
lean_inc(v_ref_4612_);
v___x_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4616_, 0, v_ref_4612_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4616_);
v___x_4618_ = v___x_4610_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4621_, lean_object* v_sz_4622_, lean_object* v_i_4623_, lean_object* v_b_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
size_t v_sz_boxed_4627_; size_t v_i_boxed_4628_; lean_object* v_res_4629_; 
v_sz_boxed_4627_ = lean_unbox_usize(v_sz_4622_);
lean_dec(v_sz_4622_);
v_i_boxed_4628_ = lean_unbox_usize(v_i_4623_);
lean_dec(v_i_4623_);
v_res_4629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4621_, v_sz_boxed_4627_, v_i_boxed_4628_, v_b_4624_, v___y_4625_);
lean_dec_ref(v___y_4625_);
lean_dec_ref(v_as_4621_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4630_, lean_object* v_entries_4631_, lean_object* v_____r_4632_, uint8_t v_anyFailed_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; size_t v_sz_4638_; size_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4637_ = lean_box(0);
v_sz_4638_ = lean_array_size(v_errors_4630_);
v___x_4639_ = ((size_t)0ULL);
v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4630_, v_sz_4638_, v___x_4639_, v___x_4637_, v___y_4634_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4649_; 
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v___x_4640_, 0);
lean_dec(v_unused_4650_);
v___x_4642_ = v___x_4640_;
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
else
{
lean_dec(v___x_4640_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4644_ = lean_box(v_anyFailed_4633_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_entries_4631_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 0, v___x_4645_);
v___x_4647_ = v___x_4642_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec_ref(v_entries_4631_);
v_a_4651_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4640_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4640_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4659_, lean_object* v_entries_4660_, lean_object* v_____r_4661_, lean_object* v_anyFailed_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
uint8_t v_anyFailed_boxed_4666_; lean_object* v_res_4667_; 
v_anyFailed_boxed_4666_ = lean_unbox(v_anyFailed_4662_);
v_res_4667_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4659_, v_entries_4660_, v_____r_4661_, v_anyFailed_boxed_4666_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec_ref(v_errors_4659_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4668_, lean_object* v_env_4669_, lean_object* v_mod_4670_){
_start:
{
lean_object* v_a_4673_; lean_object* v_a_4677_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___y_4713_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v_env_4731_; uint8_t v_anyFailed_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; lean_object* v_fileName_4741_; lean_object* v_fileMap_4742_; lean_object* v_currNamespace_4743_; lean_object* v_openDecls_4744_; lean_object* v_initHeartbeats_4745_; lean_object* v_maxHeartbeats_4746_; lean_object* v_quotContext_4747_; lean_object* v_currMacroScope_4748_; lean_object* v_cancelTk_x3f_4749_; lean_object* v_inheritedTraceOptions_4750_; lean_object* v_currRecDepth_4751_; lean_object* v_ref_4752_; uint8_t v_suppressElabErrors_4753_; lean_object* v___y_4754_; uint8_t v___y_4774_; uint8_t v___x_4794_; 
v___x_4694_ = lean_unsigned_to_nat(0u);
v___x_4695_ = lean_unsigned_to_nat(32u);
v___x_4696_ = lean_mk_empty_array_with_capacity(v___x_4695_);
lean_dec_ref(v___x_4696_);
v___x_4697_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9);
v___x_4698_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10);
v___x_4699_ = lean_io_get_num_heartbeats();
v___x_4700_ = l_Lean_firstFrontendMacroScope;
v___x_4701_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11);
v___x_4702_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14));
v___x_4703_ = lean_box(0);
v___x_4704_ = lean_box(0);
v___x_4705_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15));
v___x_4706_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_4707_ = 1;
v___x_4708_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4709_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18));
v___x_4710_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4710_, 0, v_env_4669_);
lean_ctor_set(v___x_4710_, 1, v___x_4701_);
lean_ctor_set(v___x_4710_, 2, v___x_4702_);
lean_ctor_set(v___x_4710_, 3, v___x_4705_);
lean_ctor_set(v___x_4710_, 4, v___x_4706_);
lean_ctor_set(v___x_4710_, 5, v___x_4697_);
lean_ctor_set(v___x_4710_, 6, v___x_4698_);
lean_ctor_set(v___x_4710_, 7, v___x_4708_);
lean_ctor_set(v___x_4710_, 8, v___x_4709_);
v___x_4711_ = lean_st_mk_ref(v___x_4710_);
v___x_4728_ = l_Lean_inheritedTraceOptions;
v___x_4729_ = lean_st_ref_get(v___x_4728_);
v___x_4730_ = lean_st_ref_get(v___x_4711_);
v_env_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc_ref(v_env_4731_);
lean_dec(v___x_4730_);
v_anyFailed_4732_ = 0;
v___x_4733_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4734_ = l_Lean_instInhabitedFileMap_default;
v___x_4735_ = l_Lean_Options_empty;
v___x_4736_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4737_ = lean_box(0);
v___x_4738_ = lean_box(0);
v___x_4739_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4794_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4731_);
lean_dec_ref(v_env_4731_);
if (v___x_4739_ == 0)
{
if (v___x_4794_ == 0)
{
lean_inc(v___x_4711_);
v_fileName_4741_ = v___x_4733_;
v_fileMap_4742_ = v___x_4734_;
v_currNamespace_4743_ = v___x_4703_;
v_openDecls_4744_ = v___x_4704_;
v_initHeartbeats_4745_ = v___x_4699_;
v_maxHeartbeats_4746_ = v___x_4736_;
v_quotContext_4747_ = v___x_4703_;
v_currMacroScope_4748_ = v___x_4700_;
v_cancelTk_x3f_4749_ = v___x_4737_;
v_inheritedTraceOptions_4750_ = v___x_4729_;
v_currRecDepth_4751_ = v___x_4694_;
v_ref_4752_ = v___x_4738_;
v_suppressElabErrors_4753_ = v_anyFailed_4732_;
v___y_4754_ = v___x_4711_;
goto v___jp_4740_;
}
else
{
v___y_4774_ = v___x_4739_;
goto v___jp_4773_;
}
}
else
{
v___y_4774_ = v___x_4794_;
goto v___jp_4773_;
}
v___jp_4672_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_mk_io_user_error(v_a_4673_);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
return v___x_4675_;
}
v___jp_4676_:
{
if (lean_obj_tag(v_a_4677_) == 0)
{
lean_object* v_msg_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v_msg_4678_ = lean_ctor_get(v_a_4677_, 1);
lean_inc_ref(v_msg_4678_);
lean_dec_ref_known(v_a_4677_, 2);
v___x_4679_ = l_Lean_MessageData_toString(v_msg_4678_);
v___x_4680_ = lean_mk_io_user_error(v___x_4679_);
v___x_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
return v___x_4681_;
}
else
{
lean_object* v_id_4682_; lean_object* v___x_4683_; 
v_id_4682_ = lean_ctor_get(v_a_4677_, 0);
lean_inc(v_id_4682_);
lean_dec_ref_known(v_a_4677_, 2);
v___x_4683_ = l_Lean_InternalExceptionId_getName(v_id_4682_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
lean_dec(v_id_4682_);
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4686_ = 1;
v___x_4687_ = l_Lean_Name_toString(v_a_4684_, v___x_4686_);
v___x_4688_ = lean_string_append(v___x_4685_, v___x_4687_);
lean_dec_ref(v___x_4687_);
v_a_4673_ = v___x_4688_;
goto v___jp_4672_;
}
else
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
lean_dec_ref_known(v___x_4683_, 1);
v___x_4689_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4690_ = l_Nat_reprFast(v_id_4682_);
v___x_4691_ = lean_string_append(v___x_4689_, v___x_4690_);
lean_dec_ref(v___x_4690_);
v___x_4692_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4693_ = lean_string_append(v___x_4691_, v___x_4692_);
v_a_4673_ = v___x_4693_;
goto v___jp_4672_;
}
}
}
v___jp_4712_:
{
if (lean_obj_tag(v___y_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4726_; 
v_a_4714_ = lean_ctor_get(v___y_4713_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___y_4713_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4716_ = v___y_4713_;
v_isShared_4717_ = v_isSharedCheck_4726_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___y_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4726_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v_fst_4719_; lean_object* v_snd_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; lean_object* v___x_4724_; 
v___x_4718_ = lean_st_ref_get(v___x_4711_);
lean_dec(v___x_4711_);
lean_dec(v___x_4718_);
v_fst_4719_ = lean_ctor_get(v_a_4714_, 0);
lean_inc(v_fst_4719_);
v_snd_4720_ = lean_ctor_get(v_a_4714_, 1);
lean_inc(v_snd_4720_);
lean_dec(v_a_4714_);
v___x_4721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4721_, 0, v_fst_4719_);
v___x_4722_ = lean_unbox(v_snd_4720_);
lean_dec(v_snd_4720_);
lean_ctor_set_uint8(v___x_4721_, sizeof(void*)*1, v___x_4722_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4721_);
v___x_4724_ = v___x_4716_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4721_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
else
{
lean_object* v_a_4727_; 
lean_dec(v___x_4711_);
v_a_4727_ = lean_ctor_get(v___y_4713_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v___y_4713_, 1);
v_a_4677_ = v_a_4727_;
goto v___jp_4676_;
}
}
v___jp_4740_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4755_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4749_);
lean_inc(v_currMacroScope_4748_);
lean_inc(v_quotContext_4747_);
lean_inc(v_maxHeartbeats_4746_);
lean_inc(v_openDecls_4744_);
lean_inc(v_currNamespace_4743_);
lean_inc_ref(v_fileMap_4742_);
lean_inc_ref(v_fileName_4741_);
v___x_4756_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4756_, 0, v_fileName_4741_);
lean_ctor_set(v___x_4756_, 1, v_fileMap_4742_);
lean_ctor_set(v___x_4756_, 2, v___x_4735_);
lean_ctor_set(v___x_4756_, 3, v___x_4755_);
lean_ctor_set(v___x_4756_, 4, v_currNamespace_4743_);
lean_ctor_set(v___x_4756_, 5, v_openDecls_4744_);
lean_ctor_set(v___x_4756_, 6, v_initHeartbeats_4745_);
lean_ctor_set(v___x_4756_, 7, v_maxHeartbeats_4746_);
lean_ctor_set(v___x_4756_, 8, v_quotContext_4747_);
lean_ctor_set(v___x_4756_, 9, v_currMacroScope_4748_);
lean_ctor_set(v___x_4756_, 10, v_cancelTk_x3f_4749_);
lean_ctor_set(v___x_4756_, 11, v_inheritedTraceOptions_4750_);
lean_inc(v_ref_4752_);
v___x_4757_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
lean_ctor_set(v___x_4757_, 1, v_currRecDepth_4751_);
lean_ctor_set(v___x_4757_, 2, v_ref_4752_);
lean_ctor_set_uint8(v___x_4757_, sizeof(void*)*3, v___x_4739_);
lean_ctor_set_uint8(v___x_4757_, sizeof(void*)*3 + 1, v_suppressElabErrors_4753_);
v___x_4758_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4757_, v___y_4754_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4758_, 1);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v_sp_4668_);
lean_ctor_set(v___x_4760_, 1, v_mod_4670_);
v___x_4761_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4759_, v___x_4760_, v___x_4757_, v___y_4754_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v_entries_4763_; lean_object* v_errors_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v_entries_4763_ = lean_ctor_get(v_a_4762_, 0);
lean_inc_ref(v_entries_4763_);
v_errors_4764_ = lean_ctor_get(v_a_4762_, 1);
lean_inc_ref(v_errors_4764_);
lean_dec(v_a_4762_);
v___x_4765_ = lean_array_get_size(v_errors_4764_);
v___x_4766_ = lean_nat_dec_eq(v___x_4765_, v___x_4694_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_box(0);
v___x_4768_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4764_, v_entries_4763_, v___x_4767_, v___x_4707_, v___x_4757_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref_known(v___x_4757_, 3);
lean_dec_ref(v_errors_4764_);
v___y_4713_ = v___x_4768_;
goto v___jp_4712_;
}
else
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4769_ = lean_box(0);
v___x_4770_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4764_, v_entries_4763_, v___x_4769_, v_anyFailed_4732_, v___x_4757_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref_known(v___x_4757_, 3);
lean_dec_ref(v_errors_4764_);
v___y_4713_ = v___x_4770_;
goto v___jp_4712_;
}
}
else
{
lean_object* v_a_4771_; 
lean_dec_ref_known(v___x_4757_, 3);
lean_dec(v___y_4754_);
lean_dec(v___x_4711_);
v_a_4771_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4761_, 1);
v_a_4677_ = v_a_4771_;
goto v___jp_4676_;
}
}
else
{
lean_object* v_a_4772_; 
lean_dec_ref_known(v___x_4757_, 3);
lean_dec(v___y_4754_);
lean_dec(v___x_4711_);
lean_dec(v_mod_4670_);
lean_dec(v_sp_4668_);
v_a_4772_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4758_, 1);
v_a_4677_ = v_a_4772_;
goto v___jp_4676_;
}
}
v___jp_4773_:
{
if (v___y_4774_ == 0)
{
lean_object* v___x_4775_; lean_object* v_env_4776_; lean_object* v_nextMacroScope_4777_; lean_object* v_ngen_4778_; lean_object* v_auxDeclNGen_4779_; lean_object* v_traceState_4780_; lean_object* v_messages_4781_; lean_object* v_infoState_4782_; lean_object* v_snapshotTasks_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4792_; 
v___x_4775_ = lean_st_ref_take(v___x_4711_);
v_env_4776_ = lean_ctor_get(v___x_4775_, 0);
v_nextMacroScope_4777_ = lean_ctor_get(v___x_4775_, 1);
v_ngen_4778_ = lean_ctor_get(v___x_4775_, 2);
v_auxDeclNGen_4779_ = lean_ctor_get(v___x_4775_, 3);
v_traceState_4780_ = lean_ctor_get(v___x_4775_, 4);
v_messages_4781_ = lean_ctor_get(v___x_4775_, 6);
v_infoState_4782_ = lean_ctor_get(v___x_4775_, 7);
v_snapshotTasks_4783_ = lean_ctor_get(v___x_4775_, 8);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; 
v_unused_4793_ = lean_ctor_get(v___x_4775_, 5);
lean_dec(v_unused_4793_);
v___x_4785_ = v___x_4775_;
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snapshotTasks_4783_);
lean_inc(v_infoState_4782_);
lean_inc(v_messages_4781_);
lean_inc(v_traceState_4780_);
lean_inc(v_auxDeclNGen_4779_);
lean_inc(v_ngen_4778_);
lean_inc(v_nextMacroScope_4777_);
lean_inc(v_env_4776_);
lean_dec(v___x_4775_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4792_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4789_; 
v___x_4787_ = l_Lean_Kernel_enableDiag(v_env_4776_, v___x_4739_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 5, v___x_4697_);
lean_ctor_set(v___x_4785_, 0, v___x_4787_);
v___x_4789_ = v___x_4785_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v_nextMacroScope_4777_);
lean_ctor_set(v_reuseFailAlloc_4791_, 2, v_ngen_4778_);
lean_ctor_set(v_reuseFailAlloc_4791_, 3, v_auxDeclNGen_4779_);
lean_ctor_set(v_reuseFailAlloc_4791_, 4, v_traceState_4780_);
lean_ctor_set(v_reuseFailAlloc_4791_, 5, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4791_, 6, v_messages_4781_);
lean_ctor_set(v_reuseFailAlloc_4791_, 7, v_infoState_4782_);
lean_ctor_set(v_reuseFailAlloc_4791_, 8, v_snapshotTasks_4783_);
v___x_4789_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4790_; 
v___x_4790_ = lean_st_ref_put(v___x_4711_, v___x_4789_);
lean_inc(v___x_4711_);
v_fileName_4741_ = v___x_4733_;
v_fileMap_4742_ = v___x_4734_;
v_currNamespace_4743_ = v___x_4703_;
v_openDecls_4744_ = v___x_4704_;
v_initHeartbeats_4745_ = v___x_4699_;
v_maxHeartbeats_4746_ = v___x_4736_;
v_quotContext_4747_ = v___x_4703_;
v_currMacroScope_4748_ = v___x_4700_;
v_cancelTk_x3f_4749_ = v___x_4737_;
v_inheritedTraceOptions_4750_ = v___x_4729_;
v_currRecDepth_4751_ = v___x_4694_;
v_ref_4752_ = v___x_4738_;
v_suppressElabErrors_4753_ = v_anyFailed_4732_;
v___y_4754_ = v___x_4711_;
goto v___jp_4740_;
}
}
}
else
{
lean_inc(v___x_4711_);
v_fileName_4741_ = v___x_4733_;
v_fileMap_4742_ = v___x_4734_;
v_currNamespace_4743_ = v___x_4703_;
v_openDecls_4744_ = v___x_4704_;
v_initHeartbeats_4745_ = v___x_4699_;
v_maxHeartbeats_4746_ = v___x_4736_;
v_quotContext_4747_ = v___x_4703_;
v_currMacroScope_4748_ = v___x_4700_;
v_cancelTk_x3f_4749_ = v___x_4737_;
v_inheritedTraceOptions_4750_ = v___x_4729_;
v_currRecDepth_4751_ = v___x_4694_;
v_ref_4752_ = v___x_4738_;
v_suppressElabErrors_4753_ = v_anyFailed_4732_;
v___y_4754_ = v___x_4711_;
goto v___jp_4740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4795_, lean_object* v_env_4796_, lean_object* v_mod_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4795_, v_env_4796_, v_mod_4797_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4800_, size_t v_sz_4801_, size_t v_i_4802_, lean_object* v_b_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4800_, v_sz_4801_, v_i_4802_, v_b_4803_, v___y_4804_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4808_, lean_object* v_sz_4809_, lean_object* v_i_4810_, lean_object* v_b_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
size_t v_sz_boxed_4815_; size_t v_i_boxed_4816_; lean_object* v_res_4817_; 
v_sz_boxed_4815_ = lean_unbox_usize(v_sz_4809_);
lean_dec(v_sz_4809_);
v_i_boxed_4816_ = lean_unbox_usize(v_i_4810_);
lean_dec(v_i_4810_);
v_res_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4808_, v_sz_boxed_4815_, v_i_boxed_4816_, v_b_4811_, v___y_4812_, v___y_4813_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec_ref(v_as_4808_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_enable_initializer_execution();
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4822_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = lean_compacted_region_free(v_region_4822_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4825_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4831_, lean_object* v_k_4832_, uint8_t v_v_4833_){
_start:
{
lean_object* v_map_4834_; uint8_t v_hasTrace_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4849_; 
v_map_4834_ = lean_ctor_get(v_o_4831_, 0);
v_hasTrace_4835_ = lean_ctor_get_uint8(v_o_4831_, sizeof(void*)*1);
v_isSharedCheck_4849_ = !lean_is_exclusive(v_o_4831_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4837_ = v_o_4831_;
v_isShared_4838_ = v_isSharedCheck_4849_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_map_4834_);
lean_dec(v_o_4831_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4849_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4839_, 0, v_v_4833_);
lean_inc(v_k_4832_);
v___x_4840_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4832_, v___x_4839_, v_map_4834_);
if (v_hasTrace_4835_ == 0)
{
lean_object* v___x_4841_; uint8_t v___x_4842_; lean_object* v___x_4844_; 
v___x_4841_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4842_ = l_Lean_Name_isPrefixOf(v___x_4841_, v_k_4832_);
lean_dec(v_k_4832_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v___x_4840_);
v___x_4844_ = v___x_4837_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4840_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_ctor_set_uint8(v___x_4844_, sizeof(void*)*1, v___x_4842_);
return v___x_4844_;
}
}
else
{
lean_object* v___x_4847_; 
lean_dec(v_k_4832_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v___x_4840_);
v___x_4847_ = v___x_4837_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4840_);
lean_ctor_set_uint8(v_reuseFailAlloc_4848_, sizeof(void*)*1, v_hasTrace_4835_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4850_, lean_object* v_k_4851_, lean_object* v_v_4852_){
_start:
{
uint8_t v_v_boxed_4853_; lean_object* v_res_4854_; 
v_v_boxed_4853_ = lean_unbox(v_v_4852_);
v_res_4854_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4850_, v_k_4851_, v_v_boxed_4853_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; uint32_t v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4857_ = lean_unsigned_to_nat(80u);
v___x_4858_ = l_Lean_Json_pretty(v_s_4855_, v___x_4857_);
v___x_4859_ = 10;
v___x_4860_ = lean_string_push(v___x_4858_, v___x_4859_);
v___x_4861_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4860_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4865_, size_t v_sz_4866_, size_t v_i_4867_, lean_object* v_b_4868_){
_start:
{
uint8_t v___x_4870_; 
v___x_4870_ = lean_usize_dec_lt(v_i_4867_, v_sz_4866_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v_b_4868_);
return v___x_4871_;
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_a_4872_ = lean_array_uget_borrowed(v_as_4865_, v_i_4867_);
lean_inc(v_a_4872_);
v___x_4873_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4872_);
v___x_4874_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4873_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v___x_4875_; size_t v___x_4876_; size_t v___x_4877_; 
lean_dec_ref_known(v___x_4874_, 1);
v___x_4875_ = lean_box(0);
v___x_4876_ = ((size_t)1ULL);
v___x_4877_ = lean_usize_add(v_i_4867_, v___x_4876_);
v_i_4867_ = v___x_4877_;
v_b_4868_ = v___x_4875_;
goto _start;
}
else
{
return v___x_4874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4879_, lean_object* v_sz_4880_, lean_object* v_i_4881_, lean_object* v_b_4882_, lean_object* v___y_4883_){
_start:
{
size_t v_sz_boxed_4884_; size_t v_i_boxed_4885_; lean_object* v_res_4886_; 
v_sz_boxed_4884_ = lean_unbox_usize(v_sz_4880_);
lean_dec(v_sz_4880_);
v_i_boxed_4885_ = lean_unbox_usize(v_i_4881_);
lean_dec(v_i_4881_);
v_res_4886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4879_, v_sz_boxed_4884_, v_i_boxed_4885_, v_b_4882_);
lean_dec_ref(v_as_4879_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4887_, size_t v_sz_4888_, size_t v_i_4889_, lean_object* v_bs_4890_){
_start:
{
uint8_t v_anyUnlocated_4891_; 
v_anyUnlocated_4891_ = lean_usize_dec_lt(v_i_4889_, v_sz_4888_);
if (v_anyUnlocated_4891_ == 0)
{
return v_bs_4890_;
}
else
{
lean_object* v___x_4892_; uint8_t v_anyFailed_4893_; lean_object* v_v_4894_; lean_object* v_bs_x27_4895_; lean_object* v___x_4896_; size_t v___x_4897_; size_t v___x_4898_; lean_object* v___x_4899_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v_anyFailed_4893_ = lean_nat_dec_eq(v___x_4887_, v___x_4892_);
v_v_4894_ = lean_array_uget(v_bs_4890_, v_i_4889_);
v_bs_x27_4895_ = lean_array_uset(v_bs_4890_, v_i_4889_, v___x_4892_);
v___x_4896_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4896_, 0, v_v_4894_);
lean_ctor_set_uint8(v___x_4896_, sizeof(void*)*1, v_anyFailed_4893_);
lean_ctor_set_uint8(v___x_4896_, sizeof(void*)*1 + 1, v_anyUnlocated_4891_);
lean_ctor_set_uint8(v___x_4896_, sizeof(void*)*1 + 2, v_anyFailed_4893_);
v___x_4897_ = ((size_t)1ULL);
v___x_4898_ = lean_usize_add(v_i_4889_, v___x_4897_);
v___x_4899_ = lean_array_uset(v_bs_x27_4895_, v_i_4889_, v___x_4896_);
v_i_4889_ = v___x_4898_;
v_bs_4890_ = v___x_4899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4901_, lean_object* v_sz_4902_, lean_object* v_i_4903_, lean_object* v_bs_4904_){
_start:
{
size_t v_sz_boxed_4905_; size_t v_i_boxed_4906_; lean_object* v_res_4907_; 
v_sz_boxed_4905_ = lean_unbox_usize(v_sz_4902_);
lean_dec(v_sz_4902_);
v_i_boxed_4906_ = lean_unbox_usize(v_i_4903_);
lean_dec(v_i_4903_);
v_res_4907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4901_, v_sz_boxed_4905_, v_i_boxed_4906_, v_bs_4904_);
lean_dec(v___x_4901_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4908_, size_t v_i_4909_, size_t v_stop_4910_, lean_object* v_b_4911_){
_start:
{
uint8_t v___x_4912_; 
v___x_4912_ = lean_usize_dec_eq(v_i_4909_, v_stop_4910_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; lean_object* v_fst_4914_; lean_object* v_snd_4915_; uint8_t v___x_4916_; lean_object* v___x_4917_; size_t v___x_4918_; size_t v___x_4919_; 
v___x_4913_ = lean_array_uget_borrowed(v_as_4908_, v_i_4909_);
v_fst_4914_ = lean_ctor_get(v___x_4913_, 0);
v_snd_4915_ = lean_ctor_get(v___x_4913_, 1);
v___x_4916_ = lean_unbox(v_snd_4915_);
lean_inc(v_fst_4914_);
v___x_4917_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4911_, v_fst_4914_, v___x_4916_);
v___x_4918_ = ((size_t)1ULL);
v___x_4919_ = lean_usize_add(v_i_4909_, v___x_4918_);
v_i_4909_ = v___x_4919_;
v_b_4911_ = v___x_4917_;
goto _start;
}
else
{
return v_b_4911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4921_, lean_object* v_i_4922_, lean_object* v_stop_4923_, lean_object* v_b_4924_){
_start:
{
size_t v_i_boxed_4925_; size_t v_stop_boxed_4926_; lean_object* v_res_4927_; 
v_i_boxed_4925_ = lean_unbox_usize(v_i_4922_);
lean_dec(v_i_4922_);
v_stop_boxed_4926_ = lean_unbox_usize(v_stop_4923_);
lean_dec(v_stop_4923_);
v_res_4927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4921_, v_i_boxed_4925_, v_stop_boxed_4926_, v_b_4924_);
lean_dec_ref(v_as_4921_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4937_, lean_object* v_checkImports_4938_, lean_object* v_args_4939_, lean_object* v___x_4940_, lean_object* v_as_4941_, size_t v_sz_4942_, size_t v_i_4943_, lean_object* v_b_4944_){
_start:
{
lean_object* v_a_4947_; lean_object* v___x_4951_; uint8_t v_anyFailed_4952_; uint8_t v_anyUnlocated_4953_; lean_object* v___x_4954_; lean_object* v_envLinterModule_4955_; uint8_t v___x_4956_; 
v___x_4951_ = lean_unsigned_to_nat(0u);
v_anyFailed_4952_ = lean_nat_dec_eq(v___x_4937_, v___x_4951_);
v_anyUnlocated_4953_ = 1;
v___x_4954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4955_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4955_, 0, v___x_4954_);
lean_ctor_set_uint8(v_envLinterModule_4955_, sizeof(void*)*1, v_anyFailed_4952_);
lean_ctor_set_uint8(v_envLinterModule_4955_, sizeof(void*)*1 + 1, v_anyUnlocated_4953_);
lean_ctor_set_uint8(v_envLinterModule_4955_, sizeof(void*)*1 + 2, v_anyFailed_4952_);
v___x_4956_ = lean_usize_dec_lt(v_i_4943_, v_sz_4942_);
if (v___x_4956_ == 0)
{
lean_object* v___x_4957_; 
lean_dec_ref_known(v_envLinterModule_4955_, 1);
lean_dec(v___x_4940_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_b_4944_);
return v___x_4957_;
}
else
{
lean_object* v___x_4958_; lean_object* v_a_4959_; lean_object* v___x_4960_; 
v___x_4958_ = lean_enable_initializer_execution();
v_a_4959_ = lean_array_uget_borrowed(v_as_4941_, v_i_4943_);
lean_inc(v_a_4959_);
v___x_4960_ = l_Lean_findOLean(v_a_4959_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = l_Lean_readModuleData(v_a_4961_);
lean_dec(v_a_4961_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v_fst_4964_; lean_object* v_snd_4965_; uint8_t v___x_4966_; lean_object* v_snd_4967_; lean_object* v_snd_4968_; lean_object* v_snd_4969_; lean_object* v_snd_4970_; lean_object* v_fst_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5259_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v_fst_4964_ = lean_ctor_get(v_a_4963_, 0);
lean_inc(v_fst_4964_);
v_snd_4965_ = lean_ctor_get(v_a_4963_, 1);
lean_inc(v_snd_4965_);
lean_dec(v_a_4963_);
v___x_4966_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_4964_);
lean_dec(v_fst_4964_);
v_snd_4967_ = lean_ctor_get(v_b_4944_, 1);
lean_inc(v_snd_4967_);
v_snd_4968_ = lean_ctor_get(v_snd_4967_, 1);
lean_inc(v_snd_4968_);
v_snd_4969_ = lean_ctor_get(v_snd_4968_, 1);
lean_inc(v_snd_4969_);
v_snd_4970_ = lean_ctor_get(v_snd_4969_, 1);
lean_inc(v_snd_4970_);
v_fst_4971_ = lean_ctor_get(v_b_4944_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v_b_4944_);
if (v_isSharedCheck_5259_ == 0)
{
lean_object* v_unused_5260_; 
v_unused_5260_ = lean_ctor_get(v_b_4944_, 1);
lean_dec(v_unused_5260_);
v___x_4973_ = v_b_4944_;
v_isShared_4974_ = v_isSharedCheck_5259_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_fst_4971_);
lean_dec(v_b_4944_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5259_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v_fst_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5257_; 
v_fst_4975_ = lean_ctor_get(v_snd_4967_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_snd_4967_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v_snd_4967_, 1);
lean_dec(v_unused_5258_);
v___x_4977_ = v_snd_4967_;
v_isShared_4978_ = v_isSharedCheck_5257_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_fst_4975_);
lean_dec(v_snd_4967_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5257_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v_fst_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5255_; 
v_fst_4979_ = lean_ctor_get(v_snd_4968_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_snd_4968_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; 
v_unused_5256_ = lean_ctor_get(v_snd_4968_, 1);
lean_dec(v_unused_5256_);
v___x_4981_ = v_snd_4968_;
v_isShared_4982_ = v_isSharedCheck_5255_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_fst_4979_);
lean_dec(v_snd_4968_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5255_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v_fst_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5253_; 
v_fst_4983_ = lean_ctor_get(v_snd_4969_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_snd_4969_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v_snd_4969_, 1);
lean_dec(v_unused_5254_);
v___x_4985_ = v_snd_4969_;
v_isShared_4986_ = v_isSharedCheck_5253_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_fst_4983_);
lean_dec(v_snd_4969_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5253_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v_fst_4987_; lean_object* v_snd_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_5252_; 
v_fst_4987_ = lean_ctor_get(v_snd_4970_, 0);
v_snd_4988_ = lean_ctor_get(v_snd_4970_, 1);
v_isSharedCheck_5252_ = !lean_is_exclusive(v_snd_4970_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_4990_ = v_snd_4970_;
v_isShared_4991_ = v_isSharedCheck_5252_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_snd_4988_);
lean_inc(v_fst_4987_);
lean_dec(v_snd_4970_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_5252_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___y_4993_; lean_object* v___y_4994_; uint8_t v_anyFailed_4995_; uint8_t v_anyUnlocated_4996_; lean_object* v_records_4997_; lean_object* v_codeQualityEntries_4998_; lean_object* v___y_5145_; lean_object* v___y_5146_; uint8_t v_anyFailed_5147_; uint8_t v_anyUnlocated_5148_; lean_object* v_records_5149_; lean_object* v_codeQualityEntries_5150_; lean_object* v___x_5167_; lean_object* v___y_5169_; lean_object* v___y_5170_; uint8_t v___y_5210_; 
v___x_5167_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
if (v___x_4966_ == 0)
{
uint8_t v___x_5250_; 
v___x_5250_ = 2;
v___y_5210_ = v___x_5250_;
goto v___jp_5209_;
}
else
{
uint8_t v___x_5251_; 
v___x_5251_ = 1;
v___y_5210_ = v___x_5251_;
goto v___jp_5209_;
}
v___jp_4992_:
{
uint8_t v_mode_4999_; uint8_t v___x_5000_; uint8_t v___x_5001_; 
v_mode_4999_ = lean_ctor_get_uint8(v_args_4939_, sizeof(void*)*4 + 1);
v___x_5000_ = 2;
v___x_5001_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4999_, v___x_5000_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = l_Lean_Name_getRoot(v_a_4959_);
lean_inc(v___x_4940_);
v___x_5003_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4939_, v___y_4994_, v___x_4940_, v___y_4993_, v___x_5002_, v_fst_4987_);
lean_dec_ref(v___y_4994_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v_outcome_5005_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v_outcome_5005_ = lean_ctor_get(v_a_5004_, 0);
if (lean_obj_tag(v_outcome_5005_) == 0)
{
uint8_t v_failed_5006_; 
v_failed_5006_ = lean_ctor_get_uint8(v_outcome_5005_, 0);
if (v_failed_5006_ == 0)
{
lean_object* v_checkedModules_5007_; lean_object* v___x_5009_; 
v_checkedModules_5007_ = lean_ctor_get(v_a_5004_, 1);
lean_inc(v_checkedModules_5007_);
lean_dec(v_a_5004_);
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_checkedModules_5007_);
v___x_5009_ = v___x_4990_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_checkedModules_5007_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v_snd_4988_);
v___x_5009_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5011_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5009_);
lean_ctor_set(v___x_4985_, 0, v_codeQualityEntries_4998_);
v___x_5011_ = v___x_4985_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_codeQualityEntries_4998_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
lean_object* v___x_5013_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5011_);
lean_ctor_set(v___x_4981_, 0, v_records_4997_);
v___x_5013_ = v___x_4981_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_records_4997_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5014_ = lean_box(v_anyUnlocated_4996_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5013_);
lean_ctor_set(v___x_4977_, 0, v___x_5014_);
v___x_5016_ = v___x_4977_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v___x_5013_);
v___x_5016_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = lean_box(v_anyFailed_4995_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_5016_);
lean_ctor_set(v___x_4973_, 0, v___x_5017_);
v___x_5019_ = v___x_4973_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5017_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v___x_5016_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
v_a_4947_ = v___x_5019_;
goto v___jp_4946_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5025_; lean_object* v___x_5027_; 
v_checkedModules_5025_ = lean_ctor_get(v_a_5004_, 1);
lean_inc(v_checkedModules_5025_);
lean_dec(v_a_5004_);
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_checkedModules_5025_);
v___x_5027_ = v___x_4990_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_checkedModules_5025_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v_snd_4988_);
v___x_5027_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5029_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5027_);
lean_ctor_set(v___x_4985_, 0, v_codeQualityEntries_4998_);
v___x_5029_ = v___x_4985_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_codeQualityEntries_4998_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5031_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5029_);
lean_ctor_set(v___x_4981_, 0, v_records_4997_);
v___x_5031_ = v___x_4981_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_records_4997_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5032_ = lean_box(v_anyUnlocated_4996_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5031_);
lean_ctor_set(v___x_4977_, 0, v___x_5032_);
v___x_5034_ = v___x_4977_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5032_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v___x_5031_);
v___x_5034_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
lean_object* v___x_5035_; lean_object* v___x_5037_; 
v___x_5035_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_5034_);
lean_ctor_set(v___x_4973_, 0, v___x_5035_);
v___x_5037_ = v___x_4973_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5035_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5034_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
v_a_4947_ = v___x_5037_;
goto v___jp_4946_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5043_; lean_object* v_records_5044_; uint8_t v_unlocated_5045_; lean_object* v___x_5046_; 
lean_inc_ref(v_outcome_5005_);
v_checkedModules_5043_ = lean_ctor_get(v_a_5004_, 1);
lean_inc(v_checkedModules_5043_);
lean_dec(v_a_5004_);
v_records_5044_ = lean_ctor_get(v_outcome_5005_, 0);
lean_inc_ref(v_records_5044_);
v_unlocated_5045_ = lean_ctor_get_uint8(v_outcome_5005_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_5005_, 1);
v___x_5046_ = l_Array_append___redArg(v_records_4997_, v_records_5044_);
lean_dec_ref(v_records_5044_);
if (v_unlocated_5045_ == 0)
{
lean_object* v___x_5048_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_checkedModules_5043_);
v___x_5048_ = v___x_4990_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_checkedModules_5043_);
lean_ctor_set(v_reuseFailAlloc_5063_, 1, v_snd_4988_);
v___x_5048_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5050_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5048_);
lean_ctor_set(v___x_4985_, 0, v_codeQualityEntries_4998_);
v___x_5050_ = v___x_4985_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_codeQualityEntries_4998_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5052_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5050_);
lean_ctor_set(v___x_4981_, 0, v___x_5046_);
v___x_5052_ = v___x_4981_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
v___x_5053_ = lean_box(v_anyUnlocated_4996_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5052_);
lean_ctor_set(v___x_4977_, 0, v___x_5053_);
v___x_5055_ = v___x_4977_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5053_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v___x_5052_);
v___x_5055_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_box(v_anyFailed_4995_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_5055_);
lean_ctor_set(v___x_4973_, 0, v___x_5056_);
v___x_5058_ = v___x_4973_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5056_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5055_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
v_a_4947_ = v___x_5058_;
goto v___jp_4946_;
}
}
}
}
}
}
else
{
lean_object* v___x_5065_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_checkedModules_5043_);
v___x_5065_ = v___x_4990_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_checkedModules_5043_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_snd_4988_);
v___x_5065_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
lean_object* v___x_5067_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5065_);
lean_ctor_set(v___x_4985_, 0, v_codeQualityEntries_4998_);
v___x_5067_ = v___x_4985_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_codeQualityEntries_4998_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
lean_object* v___x_5069_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5067_);
lean_ctor_set(v___x_4981_, 0, v___x_5046_);
v___x_5069_ = v___x_4981_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5072_; 
v___x_5070_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5069_);
lean_ctor_set(v___x_4977_, 0, v___x_5070_);
v___x_5072_ = v___x_4977_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5070_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5069_);
v___x_5072_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5073_ = lean_box(v_anyFailed_4995_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_5072_);
lean_ctor_set(v___x_4973_, 0, v___x_5073_);
v___x_5075_ = v___x_4973_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v___x_5072_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
v_a_4947_ = v___x_5075_;
goto v___jp_4946_;
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
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec_ref(v_codeQualityEntries_4998_);
lean_dec_ref(v_records_4997_);
lean_del_object(v___x_4990_);
lean_dec(v_snd_4988_);
lean_del_object(v___x_4985_);
lean_del_object(v___x_4981_);
lean_del_object(v___x_4977_);
lean_del_object(v___x_4973_);
lean_dec(v___x_4940_);
v_a_5081_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5003_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5003_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
else
{
lean_object* v___x_5089_; lean_object* v_fst_5090_; lean_object* v_snd_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5143_; 
lean_del_object(v___x_4973_);
v___x_5089_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4939_, v___y_4994_, v___y_4993_, v_a_4959_, v_snd_4988_);
lean_dec_ref(v___y_4994_);
v_fst_5090_ = lean_ctor_get(v___x_5089_, 0);
v_snd_5091_ = lean_ctor_get(v___x_5089_, 1);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5093_ = v___x_5089_;
v_isShared_5094_ = v_isSharedCheck_5143_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_snd_5091_);
lean_inc(v_fst_5090_);
lean_dec(v___x_5089_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5143_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5095_; 
lean_inc(v_a_4959_);
lean_inc(v___x_4940_);
v___x_5095_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4940_, v___y_4993_, v_a_4959_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_a_5096_; lean_object* v_entries_5097_; uint8_t v_failed_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___x_5095_, 1);
v_entries_5097_ = lean_ctor_get(v_a_5096_, 0);
lean_inc_ref(v_entries_5097_);
v_failed_5098_ = lean_ctor_get_uint8(v_a_5096_, sizeof(void*)*1);
lean_dec(v_a_5096_);
v___x_5099_ = l_Array_append___redArg(v_codeQualityEntries_4998_, v_fst_5090_);
lean_dec(v_fst_5090_);
v___x_5100_ = l_Array_append___redArg(v___x_5099_, v_entries_5097_);
lean_dec_ref(v_entries_5097_);
if (v_failed_5098_ == 0)
{
lean_object* v___x_5102_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v_fst_4987_);
v___x_5102_ = v___x_5093_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_fst_4987_);
lean_ctor_set(v_reuseFailAlloc_5117_, 1, v_snd_5091_);
v___x_5102_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5104_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 1, v___x_5102_);
lean_ctor_set(v___x_4990_, 0, v___x_5100_);
v___x_5104_ = v___x_4990_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5106_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5104_);
lean_ctor_set(v___x_4985_, 0, v_records_4997_);
v___x_5106_ = v___x_4985_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_records_4997_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5104_);
v___x_5106_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; lean_object* v___x_5109_; 
v___x_5107_ = lean_box(v_anyUnlocated_4996_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5106_);
lean_ctor_set(v___x_4981_, 0, v___x_5107_);
v___x_5109_ = v___x_4981_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v___x_5107_);
lean_ctor_set(v_reuseFailAlloc_5114_, 1, v___x_5106_);
v___x_5109_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5110_ = lean_box(v_anyFailed_4995_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5109_);
lean_ctor_set(v___x_4977_, 0, v___x_5110_);
v___x_5112_ = v___x_4977_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v___x_5109_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
v_a_4947_ = v___x_5112_;
goto v___jp_4946_;
}
}
}
}
}
}
else
{
lean_object* v___x_5119_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v_fst_4987_);
v___x_5119_ = v___x_5093_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_fst_4987_);
lean_ctor_set(v_reuseFailAlloc_5134_, 1, v_snd_5091_);
v___x_5119_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
lean_object* v___x_5121_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 1, v___x_5119_);
lean_ctor_set(v___x_4990_, 0, v___x_5100_);
v___x_5121_ = v___x_4990_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5133_, 1, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5123_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_5121_);
lean_ctor_set(v___x_4985_, 0, v_records_4997_);
v___x_5123_ = v___x_4985_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_records_4997_);
lean_ctor_set(v_reuseFailAlloc_5132_, 1, v___x_5121_);
v___x_5123_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
lean_object* v___x_5124_; lean_object* v___x_5126_; 
v___x_5124_ = lean_box(v_anyUnlocated_4996_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5123_);
lean_ctor_set(v___x_4981_, 0, v___x_5124_);
v___x_5126_ = v___x_4981_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5124_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v___x_5123_);
v___x_5126_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; lean_object* v___x_5129_; 
v___x_5127_ = lean_box(v_anyUnlocated_4953_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5126_);
lean_ctor_set(v___x_4977_, 0, v___x_5127_);
v___x_5129_ = v___x_4977_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5127_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5126_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
v_a_4947_ = v___x_5129_;
goto v___jp_4946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_del_object(v___x_5093_);
lean_dec(v_snd_5091_);
lean_dec(v_fst_5090_);
lean_dec_ref(v_codeQualityEntries_4998_);
lean_dec_ref(v_records_4997_);
lean_del_object(v___x_4990_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_del_object(v___x_4981_);
lean_del_object(v___x_4977_);
lean_dec(v___x_4940_);
v_a_5135_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5095_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5095_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
}
}
v___jp_5144_:
{
lean_object* v___x_5151_; 
lean_inc(v_a_4959_);
lean_inc_ref(v___y_5145_);
lean_inc(v___x_4940_);
lean_inc_ref(v___y_5146_);
v___x_5151_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4939_, v___y_5146_, v___x_4940_, v___y_5145_, v_a_4959_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5151_, 1);
switch(lean_obj_tag(v_a_5152_))
{
case 0:
{
uint8_t v_failed_5153_; 
v_failed_5153_ = lean_ctor_get_uint8(v_a_5152_, 0);
lean_dec_ref_known(v_a_5152_, 0);
if (v_failed_5153_ == 0)
{
v___y_4993_ = v___y_5145_;
v___y_4994_ = v___y_5146_;
v_anyFailed_4995_ = v_anyFailed_5147_;
v_anyUnlocated_4996_ = v_anyUnlocated_5148_;
v_records_4997_ = v_records_5149_;
v_codeQualityEntries_4998_ = v_codeQualityEntries_5150_;
goto v___jp_4992_;
}
else
{
v___y_4993_ = v___y_5145_;
v___y_4994_ = v___y_5146_;
v_anyFailed_4995_ = v_anyUnlocated_4953_;
v_anyUnlocated_4996_ = v_anyUnlocated_5148_;
v_records_4997_ = v_records_5149_;
v_codeQualityEntries_4998_ = v_codeQualityEntries_5150_;
goto v___jp_4992_;
}
}
case 1:
{
lean_object* v_records_5154_; uint8_t v_unlocated_5155_; lean_object* v___x_5156_; 
v_records_5154_ = lean_ctor_get(v_a_5152_, 0);
lean_inc_ref(v_records_5154_);
v_unlocated_5155_ = lean_ctor_get_uint8(v_a_5152_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5152_, 1);
v___x_5156_ = l_Array_append___redArg(v_records_5149_, v_records_5154_);
lean_dec_ref(v_records_5154_);
if (v_unlocated_5155_ == 0)
{
v___y_4993_ = v___y_5145_;
v___y_4994_ = v___y_5146_;
v_anyFailed_4995_ = v_anyFailed_5147_;
v_anyUnlocated_4996_ = v_anyUnlocated_5148_;
v_records_4997_ = v___x_5156_;
v_codeQualityEntries_4998_ = v_codeQualityEntries_5150_;
goto v___jp_4992_;
}
else
{
v___y_4993_ = v___y_5145_;
v___y_4994_ = v___y_5146_;
v_anyFailed_4995_ = v_anyFailed_5147_;
v_anyUnlocated_4996_ = v_anyUnlocated_4953_;
v_records_4997_ = v___x_5156_;
v_codeQualityEntries_4998_ = v_codeQualityEntries_5150_;
goto v___jp_4992_;
}
}
default: 
{
lean_object* v_entries_5157_; lean_object* v___x_5158_; 
v_entries_5157_ = lean_ctor_get(v_a_5152_, 0);
lean_inc_ref(v_entries_5157_);
lean_dec_ref_known(v_a_5152_, 1);
v___x_5158_ = l_Array_append___redArg(v_codeQualityEntries_5150_, v_entries_5157_);
lean_dec_ref(v_entries_5157_);
v___y_4993_ = v___y_5145_;
v___y_4994_ = v___y_5146_;
v_anyFailed_4995_ = v_anyFailed_5147_;
v_anyUnlocated_4996_ = v_anyUnlocated_5148_;
v_records_4997_ = v_records_5149_;
v_codeQualityEntries_4998_ = v___x_5158_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec_ref(v_codeQualityEntries_5150_);
lean_dec_ref(v_records_5149_);
lean_dec_ref(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_del_object(v___x_4990_);
lean_dec(v_snd_4988_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_del_object(v___x_4981_);
lean_del_object(v___x_4977_);
lean_del_object(v___x_4973_);
lean_dec(v___x_4940_);
v_a_5159_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5151_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5151_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
v___jp_5168_:
{
lean_object* v___x_5171_; lean_object* v_toEnvExtension_5172_; lean_object* v_asyncMode_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v_merged_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5207_; 
v___x_5171_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5172_ = lean_ctor_get(v___x_5171_, 0);
v_asyncMode_5173_ = lean_ctor_get(v_toEnvExtension_5172_, 2);
v___x_5174_ = lean_box(0);
lean_inc_ref(v___y_5169_);
v___x_5175_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5167_, v___x_5171_, v___y_5169_, v_asyncMode_5173_, v___x_5174_);
v_merged_5176_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5207_ == 0)
{
lean_object* v_unused_5208_; 
v_unused_5208_ = lean_ctor_get(v___x_5175_, 1);
lean_dec(v_unused_5208_);
v___x_5178_ = v___x_5175_;
v_isShared_5179_ = v_isSharedCheck_5207_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_merged_5176_);
lean_dec(v___x_5175_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5207_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 1, v_merged_5176_);
lean_ctor_set(v___x_5178_, 0, v___y_5170_);
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___y_5170_);
lean_ctor_set(v_reuseFailAlloc_5206_, 1, v_merged_5176_);
v___x_5181_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
lean_object* v___x_5182_; 
v___x_5182_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4939_, v___x_5181_, v___y_5169_, v_a_4959_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref_known(v___x_5182_, 1);
switch(lean_obj_tag(v_a_5183_))
{
case 0:
{
uint8_t v___x_5184_; 
v___x_5184_ = lean_unbox(v_fst_4971_);
lean_dec(v_fst_4971_);
if (v___x_5184_ == 0)
{
uint8_t v_failed_5185_; uint8_t v___x_5186_; 
v_failed_5185_ = lean_ctor_get_uint8(v_a_5183_, 0);
lean_dec_ref_known(v_a_5183_, 0);
v___x_5186_ = lean_unbox(v_fst_4975_);
lean_dec(v_fst_4975_);
v___y_5145_ = v___y_5169_;
v___y_5146_ = v___x_5181_;
v_anyFailed_5147_ = v_failed_5185_;
v_anyUnlocated_5148_ = v___x_5186_;
v_records_5149_ = v_fst_4979_;
v_codeQualityEntries_5150_ = v_fst_4983_;
goto v___jp_5144_;
}
else
{
uint8_t v___x_5187_; 
lean_dec_ref_known(v_a_5183_, 0);
v___x_5187_ = lean_unbox(v_fst_4975_);
lean_dec(v_fst_4975_);
v___y_5145_ = v___y_5169_;
v___y_5146_ = v___x_5181_;
v_anyFailed_5147_ = v_anyUnlocated_4953_;
v_anyUnlocated_5148_ = v___x_5187_;
v_records_5149_ = v_fst_4979_;
v_codeQualityEntries_5150_ = v_fst_4983_;
goto v___jp_5144_;
}
}
case 1:
{
lean_object* v_records_5188_; uint8_t v_unlocated_5189_; lean_object* v___x_5190_; 
v_records_5188_ = lean_ctor_get(v_a_5183_, 0);
lean_inc_ref(v_records_5188_);
v_unlocated_5189_ = lean_ctor_get_uint8(v_a_5183_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5183_, 1);
v___x_5190_ = l_Array_append___redArg(v_fst_4979_, v_records_5188_);
lean_dec_ref(v_records_5188_);
if (v_unlocated_5189_ == 0)
{
uint8_t v___x_5191_; uint8_t v___x_5192_; 
v___x_5191_ = lean_unbox(v_fst_4971_);
lean_dec(v_fst_4971_);
v___x_5192_ = lean_unbox(v_fst_4975_);
lean_dec(v_fst_4975_);
v___y_5145_ = v___y_5169_;
v___y_5146_ = v___x_5181_;
v_anyFailed_5147_ = v___x_5191_;
v_anyUnlocated_5148_ = v___x_5192_;
v_records_5149_ = v___x_5190_;
v_codeQualityEntries_5150_ = v_fst_4983_;
goto v___jp_5144_;
}
else
{
uint8_t v___x_5193_; 
lean_dec(v_fst_4975_);
v___x_5193_ = lean_unbox(v_fst_4971_);
lean_dec(v_fst_4971_);
v___y_5145_ = v___y_5169_;
v___y_5146_ = v___x_5181_;
v_anyFailed_5147_ = v___x_5193_;
v_anyUnlocated_5148_ = v_anyUnlocated_4953_;
v_records_5149_ = v___x_5190_;
v_codeQualityEntries_5150_ = v_fst_4983_;
goto v___jp_5144_;
}
}
default: 
{
lean_object* v_entries_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; uint8_t v___x_5197_; 
v_entries_5194_ = lean_ctor_get(v_a_5183_, 0);
lean_inc_ref(v_entries_5194_);
lean_dec_ref_known(v_a_5183_, 1);
v___x_5195_ = l_Array_append___redArg(v_fst_4983_, v_entries_5194_);
lean_dec_ref(v_entries_5194_);
v___x_5196_ = lean_unbox(v_fst_4971_);
lean_dec(v_fst_4971_);
v___x_5197_ = lean_unbox(v_fst_4975_);
lean_dec(v_fst_4975_);
v___y_5145_ = v___y_5169_;
v___y_5146_ = v___x_5181_;
v_anyFailed_5147_ = v___x_5196_;
v_anyUnlocated_5148_ = v___x_5197_;
v_records_5149_ = v_fst_4979_;
v_codeQualityEntries_5150_ = v___x_5195_;
goto v___jp_5144_;
}
}
}
else
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v___y_5169_);
lean_del_object(v___x_4990_);
lean_dec(v_snd_4988_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_del_object(v___x_4981_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4977_);
lean_dec(v_fst_4975_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4971_);
lean_dec(v___x_4940_);
v_a_5198_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5182_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5182_);
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
}
}
v___jp_5209_:
{
lean_object* v___x_5211_; 
v___x_5211_ = lean_compacted_region_free(v_snd_4965_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; uint32_t v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec_ref_known(v___x_5211_, 1);
lean_inc(v_a_4959_);
v___x_5212_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5212_, 0, v_a_4959_);
lean_ctor_set_uint8(v___x_5212_, sizeof(void*)*1, v_anyFailed_4952_);
lean_ctor_set_uint8(v___x_5212_, sizeof(void*)*1 + 1, v_anyUnlocated_4953_);
lean_ctor_set_uint8(v___x_5212_, sizeof(void*)*1 + 2, v_anyFailed_4952_);
v___x_5213_ = lean_unsigned_to_nat(2u);
v___x_5214_ = lean_mk_empty_array_with_capacity(v___x_5213_);
v___x_5215_ = lean_array_push(v___x_5214_, v___x_5212_);
v___x_5216_ = lean_array_push(v___x_5215_, v_envLinterModule_4955_);
v___x_5217_ = l_Array_append___redArg(v___x_5216_, v_checkImports_4938_);
v___x_5218_ = l_Lean_Options_empty;
v___x_5219_ = 1024;
v___x_5220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5221_ = lean_box(1);
v___x_5222_ = l_Lean_importModules(v___x_5217_, v___x_5218_, v___x_5219_, v___x_5220_, v_anyFailed_4952_, v_anyUnlocated_4953_, v___y_5210_, v___x_5221_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v_a_5223_; lean_object* v_linterOverrides_5224_; lean_object* v___x_5225_; uint8_t v___x_5226_; 
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5223_);
lean_dec_ref_known(v___x_5222_, 1);
v_linterOverrides_5224_ = lean_ctor_get(v_args_4939_, 0);
v___x_5225_ = lean_array_get_size(v_linterOverrides_5224_);
v___x_5226_ = lean_nat_dec_lt(v___x_4951_, v___x_5225_);
if (v___x_5226_ == 0)
{
v___y_5169_ = v_a_5223_;
v___y_5170_ = v___x_5218_;
goto v___jp_5168_;
}
else
{
uint8_t v___x_5227_; 
v___x_5227_ = lean_nat_dec_le(v___x_5225_, v___x_5225_);
if (v___x_5227_ == 0)
{
if (v___x_5226_ == 0)
{
v___y_5169_ = v_a_5223_;
v___y_5170_ = v___x_5218_;
goto v___jp_5168_;
}
else
{
size_t v___x_5228_; size_t v___x_5229_; lean_object* v___x_5230_; 
v___x_5228_ = ((size_t)0ULL);
v___x_5229_ = lean_usize_of_nat(v___x_5225_);
v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5224_, v___x_5228_, v___x_5229_, v___x_5218_);
v___y_5169_ = v_a_5223_;
v___y_5170_ = v___x_5230_;
goto v___jp_5168_;
}
}
else
{
size_t v___x_5231_; size_t v___x_5232_; lean_object* v___x_5233_; 
v___x_5231_ = ((size_t)0ULL);
v___x_5232_ = lean_usize_of_nat(v___x_5225_);
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5224_, v___x_5231_, v___x_5232_, v___x_5218_);
v___y_5169_ = v_a_5223_;
v___y_5170_ = v___x_5233_;
goto v___jp_5168_;
}
}
}
else
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_del_object(v___x_4990_);
lean_dec(v_snd_4988_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_del_object(v___x_4981_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4977_);
lean_dec(v_fst_4975_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4971_);
lean_dec(v___x_4940_);
v_a_5234_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5222_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5222_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_del_object(v___x_4990_);
lean_dec(v_snd_4988_);
lean_dec(v_fst_4987_);
lean_del_object(v___x_4985_);
lean_dec(v_fst_4983_);
lean_del_object(v___x_4981_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4977_);
lean_dec(v_fst_4975_);
lean_del_object(v___x_4973_);
lean_dec(v_fst_4971_);
lean_dec_ref_known(v_envLinterModule_4955_, 1);
lean_dec(v___x_4940_);
v_a_5242_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5211_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5211_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
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
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
lean_dec_ref_known(v_envLinterModule_4955_, 1);
lean_dec_ref(v_b_4944_);
lean_dec(v___x_4940_);
v_a_5261_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_4962_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_4962_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec_ref_known(v_envLinterModule_4955_, 1);
lean_dec_ref(v_b_4944_);
lean_dec(v___x_4940_);
v_a_5269_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_4960_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_4960_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
v___jp_4946_:
{
size_t v___x_4948_; size_t v___x_4949_; 
v___x_4948_ = ((size_t)1ULL);
v___x_4949_ = lean_usize_add(v_i_4943_, v___x_4948_);
v_i_4943_ = v___x_4949_;
v_b_4944_ = v_a_4947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5277_, lean_object* v_checkImports_5278_, lean_object* v_args_5279_, lean_object* v___x_5280_, lean_object* v_as_5281_, lean_object* v_sz_5282_, lean_object* v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_){
_start:
{
size_t v_sz_boxed_5286_; size_t v_i_boxed_5287_; lean_object* v_res_5288_; 
v_sz_boxed_5286_ = lean_unbox_usize(v_sz_5282_);
lean_dec(v_sz_5282_);
v_i_boxed_5287_ = lean_unbox_usize(v_i_5283_);
lean_dec(v_i_5283_);
v_res_5288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5277_, v_checkImports_5278_, v_args_5279_, v___x_5280_, v_as_5281_, v_sz_boxed_5286_, v_i_boxed_5287_, v_b_5284_);
lean_dec_ref(v_as_5281_);
lean_dec_ref(v_args_5279_);
lean_dec_ref(v_checkImports_5278_);
lean_dec(v___x_5277_);
return v_res_5288_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = l_Lean_NameSet_empty;
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
return v___x_5290_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5291_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5292_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
lean_ctor_set(v___x_5293_, 1, v___x_5291_);
return v___x_5293_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5295_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
lean_ctor_set(v___x_5296_, 1, v___x_5294_);
return v___x_5296_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = 0;
v___x_5299_ = lean_box_uint32(v___x_5298_);
return v___x_5299_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = 1;
v___x_5301_ = lean_box_uint32(v___x_5300_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5302_){
_start:
{
lean_object* v_mods_5304_; uint8_t v_mode_5305_; lean_object* v_checks_5306_; lean_object* v_srcSearchPath_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; uint8_t v_anyFailed_5310_; 
v_mods_5304_ = lean_ctor_get(v_args_5302_, 1);
lean_inc_ref(v_mods_5304_);
v_mode_5305_ = lean_ctor_get_uint8(v_args_5302_, sizeof(void*)*4 + 1);
v_checks_5306_ = lean_ctor_get(v_args_5302_, 2);
v_srcSearchPath_5307_ = lean_ctor_get(v_args_5302_, 3);
v___x_5308_ = lean_array_get_size(v_mods_5304_);
v___x_5309_ = lean_unsigned_to_nat(0u);
v_anyFailed_5310_ = lean_nat_dec_eq(v___x_5308_, v___x_5309_);
if (v_anyFailed_5310_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; size_t v_sz_5313_; size_t v___x_5314_; lean_object* v_checkImports_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; size_t v_sz_5322_; lean_object* v___x_5323_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5311_, 1);
v_sz_5313_ = lean_array_size(v_checks_5306_);
v___x_5314_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5306_);
v_checkImports_5315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5308_, v_sz_5313_, v___x_5314_, v_checks_5306_);
lean_inc(v_srcSearchPath_5307_);
v___x_5316_ = l_List_appendTR___redArg(v_srcSearchPath_5307_, v_a_5312_);
v___x_5317_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5318_ = lean_box(v_anyFailed_5310_);
v___x_5319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
lean_ctor_set(v___x_5319_, 1, v___x_5317_);
v___x_5320_ = lean_box(v_anyFailed_5310_);
v___x_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
lean_ctor_set(v___x_5321_, 1, v___x_5319_);
v_sz_5322_ = lean_array_size(v_mods_5304_);
v___x_5323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5308_, v_checkImports_5315_, v_args_5302_, v___x_5316_, v_mods_5304_, v_sz_5322_, v___x_5314_, v___x_5321_);
lean_dec_ref(v_mods_5304_);
lean_dec_ref(v_args_5302_);
lean_dec_ref(v_checkImports_5315_);
if (lean_obj_tag(v___x_5323_) == 0)
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5395_; 
v_a_5324_ = lean_ctor_get(v___x_5323_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5323_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5326_ = v___x_5323_;
v_isShared_5327_ = v_isSharedCheck_5395_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5323_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5395_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
switch(v_mode_5305_)
{
case 0:
{
lean_object* v_fst_5328_; uint8_t v___x_5329_; 
v_fst_5328_ = lean_ctor_get(v_a_5324_, 0);
lean_inc(v_fst_5328_);
lean_dec(v_a_5324_);
v___x_5329_ = lean_unbox(v_fst_5328_);
lean_dec(v_fst_5328_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5332_; 
v___x_5330_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 0, v___x_5330_);
v___x_5332_ = v___x_5326_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5330_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
else
{
lean_object* v___x_5334_; lean_object* v___x_5336_; 
v___x_5334_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 0, v___x_5334_);
v___x_5336_ = v___x_5326_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5334_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
case 1:
{
lean_object* v_snd_5338_; lean_object* v_snd_5339_; lean_object* v_fst_5340_; lean_object* v_fst_5341_; lean_object* v___x_5342_; 
v_snd_5338_ = lean_ctor_get(v_a_5324_, 1);
lean_inc(v_snd_5338_);
lean_del_object(v___x_5326_);
lean_dec(v_a_5324_);
v_snd_5339_ = lean_ctor_get(v_snd_5338_, 1);
lean_inc(v_snd_5339_);
v_fst_5340_ = lean_ctor_get(v_snd_5338_, 0);
lean_inc(v_fst_5340_);
lean_dec(v_snd_5338_);
v_fst_5341_ = lean_ctor_get(v_snd_5339_, 0);
lean_inc(v_fst_5341_);
lean_dec(v_snd_5339_);
v___x_5342_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5341_);
lean_dec(v_fst_5341_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5355_; 
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5355_ == 0)
{
lean_object* v_unused_5356_; 
v_unused_5356_ = lean_ctor_get(v___x_5342_, 0);
lean_dec(v_unused_5356_);
v___x_5344_ = v___x_5342_;
v_isShared_5345_ = v_isSharedCheck_5355_;
goto v_resetjp_5343_;
}
else
{
lean_dec(v___x_5342_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5355_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
uint8_t v___x_5346_; 
v___x_5346_ = lean_unbox(v_fst_5340_);
lean_dec(v_fst_5340_);
if (v___x_5346_ == 0)
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5345_ == 0)
{
lean_ctor_set(v___x_5344_, 0, v___x_5347_);
v___x_5349_ = v___x_5344_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
else
{
lean_object* v___x_5351_; lean_object* v___x_5353_; 
v___x_5351_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5345_ == 0)
{
lean_ctor_set(v___x_5344_, 0, v___x_5351_);
v___x_5353_ = v___x_5344_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5351_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec(v_fst_5340_);
v_a_5357_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5342_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5342_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
default: 
{
lean_object* v_snd_5365_; lean_object* v_snd_5366_; lean_object* v_snd_5367_; lean_object* v_fst_5368_; lean_object* v_fst_5369_; lean_object* v___x_5370_; size_t v_sz_5371_; lean_object* v___x_5372_; 
v_snd_5365_ = lean_ctor_get(v_a_5324_, 1);
lean_del_object(v___x_5326_);
v_snd_5366_ = lean_ctor_get(v_snd_5365_, 1);
v_snd_5367_ = lean_ctor_get(v_snd_5366_, 1);
lean_inc(v_snd_5367_);
v_fst_5368_ = lean_ctor_get(v_a_5324_, 0);
lean_inc(v_fst_5368_);
lean_dec(v_a_5324_);
v_fst_5369_ = lean_ctor_get(v_snd_5367_, 0);
lean_inc(v_fst_5369_);
lean_dec(v_snd_5367_);
v___x_5370_ = lean_box(0);
v_sz_5371_ = lean_array_size(v_fst_5369_);
v___x_5372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5369_, v_sz_5371_, v___x_5314_, v___x_5370_);
lean_dec(v_fst_5369_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5385_; 
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5385_ == 0)
{
lean_object* v_unused_5386_; 
v_unused_5386_ = lean_ctor_get(v___x_5372_, 0);
lean_dec(v_unused_5386_);
v___x_5374_ = v___x_5372_;
v_isShared_5375_ = v_isSharedCheck_5385_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v___x_5372_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5385_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
uint8_t v___x_5376_; 
v___x_5376_ = lean_unbox(v_fst_5368_);
lean_dec(v_fst_5368_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5379_; 
v___x_5377_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v___x_5377_);
v___x_5379_ = v___x_5374_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5381_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v___x_5381_);
v___x_5383_ = v___x_5374_;
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
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec(v_fst_5368_);
v_a_5387_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5372_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5372_);
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
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
v_a_5396_ = lean_ctor_get(v___x_5323_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5323_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5323_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5323_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec_ref(v_mods_5304_);
lean_dec_ref(v_args_5302_);
v_a_5404_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5311_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5311_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
else
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
lean_dec_ref(v_mods_5304_);
lean_dec_ref(v_args_5302_);
v___x_5412_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5413_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5412_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5421_; 
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; 
v_unused_5422_ = lean_ctor_get(v___x_5413_, 0);
lean_dec(v_unused_5422_);
v___x_5415_ = v___x_5413_;
v_isShared_5416_ = v_isSharedCheck_5421_;
goto v_resetjp_5414_;
}
else
{
lean_dec(v___x_5413_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5421_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5417_; lean_object* v___x_5419_; 
v___x_5417_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 0, v___x_5417_);
v___x_5419_ = v___x_5415_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5417_);
v___x_5419_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
return v___x_5419_;
}
}
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
v_a_5423_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5413_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5413_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5431_, lean_object* v_a_5432_){
_start:
{
lean_object* v_res_5433_; 
v_res_5433_ = l_Lake_BuiltinLint_run(v_args_5431_);
return v_res_5433_;
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
