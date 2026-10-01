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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
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
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "warning: could not determine the position of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "`; cannot record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` exception"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "warning: could not locate source file for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` to record a `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "error: in module `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "`, in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": error: in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint16_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7;
static const lean_string_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__8_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11_value;
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
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21;
static lean_once_cell_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_11544__boxed_985_; uint8_t v_res_986_; lean_object* v_r_987_; 
v___x_11544__boxed_985_ = lean_unbox(v___x_982_);
v_res_986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11544__boxed_985_, v_a_983_, v_b_984_);
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
v___y_1199_ = v_fst_1236_;
v___y_1200_ = v___x_1243_;
v___y_1201_ = v___x_1245_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1246_; 
v___x_1246_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1199_ = v_fst_1236_;
v___y_1200_ = v___x_1243_;
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
v___x_1262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1260_, v___y_1258_, v___y_1257_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
v___y_1229_ = v___y_1259_;
v___y_1230_ = v___x_1262_;
goto v___jp_1228_;
}
v___jp_1263_:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_le(v___y_1268_, v___y_1265_);
if (v___x_1269_ == 0)
{
lean_dec(v___y_1265_);
lean_inc(v___y_1268_);
v___y_1257_ = v___y_1268_;
v___y_1258_ = v___y_1264_;
v___y_1259_ = v___y_1267_;
v___y_1260_ = v___y_1266_;
v___y_1261_ = v___y_1268_;
goto v___jp_1256_;
}
else
{
v___y_1257_ = v___y_1268_;
v___y_1258_ = v___y_1264_;
v___y_1259_ = v___y_1267_;
v___y_1260_ = v___y_1266_;
v___y_1261_ = v___y_1265_;
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
v___y_1264_ = v___y_1271_;
v___y_1265_ = v___x_1275_;
v___y_1266_ = v___x_1273_;
v___y_1267_ = v___x_1272_;
v___y_1268_ = v___x_1275_;
goto v___jp_1263_;
}
else
{
v___y_1264_ = v___y_1271_;
v___y_1265_ = v___x_1275_;
v___y_1266_ = v___x_1273_;
v___y_1267_ = v___x_1272_;
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
v___x_1202_ = lean_string_append(v___y_1200_, v___y_1201_);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0));
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_string_append(v___x_1204_, v_fst_1192_);
v___x_1206_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1));
v___x_1208_ = lean_array_to_list(v___y_1199_);
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
lean_dec(v___y_1199_);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1979_, lean_object* v_opt_1980_){
_start:
{
lean_object* v_name_1981_; lean_object* v_defValue_1982_; lean_object* v_map_1983_; lean_object* v___x_1984_; 
v_name_1981_ = lean_ctor_get(v_opt_1980_, 0);
v_defValue_1982_ = lean_ctor_get(v_opt_1980_, 1);
v_map_1983_ = lean_ctor_get(v_opts_1979_, 0);
v___x_1984_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1983_, v_name_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_inc(v_defValue_1982_);
return v_defValue_1982_;
}
else
{
lean_object* v_val_1985_; 
v_val_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v___x_1984_, 1);
if (lean_obj_tag(v_val_1985_) == 3)
{
lean_object* v_v_1986_; 
v_v_1986_ = lean_ctor_get(v_val_1985_, 0);
lean_inc(v_v_1986_);
lean_dec_ref_known(v_val_1985_, 1);
return v_v_1986_;
}
else
{
lean_dec(v_val_1985_);
lean_inc(v_defValue_1982_);
return v_defValue_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1987_, lean_object* v_opt_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1987_, v_opt_1988_);
lean_dec_ref(v_opt_1988_);
lean_dec_ref(v_opts_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_options_1994_; lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2006_; 
v_options_1994_ = lean_ctor_get(v_c_1990_, 6);
lean_inc_ref(v_options_1994_);
lean_dec_ref(v_c_1990_);
v___x_1995_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1994_, v___y_1992_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2000_ = l_Lean_linter_doc_deferred;
v___x_2001_ = l_Lean_Linter_getLinterValue(v___x_2000_, v_a_1996_);
lean_dec(v_a_1996_);
v___x_2002_ = lean_box(v___x_2001_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2002_);
v___x_2004_ = v___x_1998_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_2012_, lean_object* v_docCheckedModules_2013_, uint8_t v___y_2014_, lean_object* v_m_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2012_, v_m_2015_);
if (v___x_2016_ == 0)
{
return v___x_2016_;
}
else
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_NameSet_contains(v_docCheckedModules_2013_, v_m_2015_);
if (v___x_2017_ == 0)
{
return v___y_2014_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = 0;
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_2019_, lean_object* v_docCheckedModules_2020_, lean_object* v___y_2021_, lean_object* v_m_2022_){
_start:
{
uint8_t v___y_7530__boxed_2023_; uint8_t v_res_2024_; lean_object* v_r_2025_; 
v___y_7530__boxed_2023_ = lean_unbox(v___y_2021_);
v_res_2024_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_2019_, v_docCheckedModules_2020_, v___y_7530__boxed_2023_, v_m_2022_);
lean_dec(v_m_2022_);
lean_dec(v_docCheckedModules_2020_);
lean_dec(v_pkgRoot_2019_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t v___x_2033_, lean_object* v_sp_2034_, lean_object* v_as_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_a_2043_; uint8_t v_unlocated_2047_; 
v_unlocated_2047_ = lean_usize_dec_lt(v_i_2037_, v_sz_2036_);
if (v_unlocated_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v_sp_2034_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2038_);
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v_snd_2050_; lean_object* v_fst_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2173_; 
v_a_2049_ = lean_array_uget_borrowed(v_as_2035_, v_i_2037_);
v_snd_2050_ = lean_ctor_get(v_a_2049_, 1);
lean_inc(v_snd_2050_);
v_fst_2051_ = lean_ctor_get(v_snd_2050_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_snd_2050_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v_snd_2050_, 1);
lean_dec(v_unused_2174_);
v___x_2053_ = v_snd_2050_;
v_isShared_2054_ = v_isSharedCheck_2173_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_fst_2051_);
lean_dec(v_snd_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2173_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_fst_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2172_; 
v_fst_2055_ = lean_ctor_get(v_a_2049_, 0);
v_fst_2056_ = lean_ctor_get(v_b_2038_, 0);
v_snd_2057_ = lean_ctor_get(v_b_2038_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_b_2038_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2059_ = v_b_2038_;
v_isShared_2060_ = v_isSharedCheck_2172_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_inc(v_fst_2056_);
lean_dec(v_b_2038_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2172_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_site_2061_; lean_object* v___x_2062_; 
v_site_2061_ = lean_ctor_get(v_fst_2051_, 0);
lean_inc_ref_n(v_site_2061_, 2);
lean_dec(v_fst_2051_);
v___x_2062_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2055_, v_site_2061_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
if (lean_obj_tag(v_a_2063_) == 0)
{
lean_object* v___x_2064_; lean_object* v_name_2065_; lean_object* v_ref_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_snd_2057_);
v___x_2064_ = l_Lean_linter_doc_deferred;
v_name_2065_ = lean_ctor_get(v___x_2064_, 0);
v_ref_2066_ = lean_ctor_get(v___y_2039_, 2);
lean_inc(v_fst_2055_);
v___x_2067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2055_, v___x_2033_);
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0));
v___x_2069_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2061_);
v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1));
v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
v___x_2073_ = lean_string_append(v___x_2072_, v___x_2067_);
lean_dec_ref(v___x_2067_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_2075_ = lean_string_append(v___x_2073_, v___x_2074_);
lean_inc(v_name_2065_);
v___x_2076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2065_, v___x_2033_);
v___x_2077_ = lean_string_append(v___x_2075_, v___x_2076_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2079_ = lean_string_append(v___x_2077_, v___x_2078_);
v___x_2080_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
lean_dec_ref_known(v___x_2080_, 1);
lean_del_object(v___x_2053_);
v___x_2081_ = lean_box(v_unlocated_2047_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2081_);
v___x_2083_ = v___x_2059_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
v_a_2043_ = v___x_2083_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2098_; 
lean_del_object(v___x_2059_);
lean_dec(v_fst_2056_);
lean_dec(v_sp_2034_);
v_a_2085_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2087_ = v___x_2080_;
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2089_ = lean_io_error_to_string(v_a_2085_);
v___x_2090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
v___x_2091_ = l_Lean_MessageData_ofFormat(v___x_2090_);
lean_inc(v_ref_2066_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2091_);
lean_ctor_set(v___x_2053_, 0, v_ref_2066_);
v___x_2093_ = v___x_2053_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_ref_2066_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2093_);
v___x_2095_ = v___x_2087_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_site_2061_);
v_val_2099_ = lean_ctor_get(v_a_2063_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2101_ = v_a_2063_;
v_isShared_2102_ = v_isSharedCheck_2163_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_val_2099_);
lean_dec(v_a_2063_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2163_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_ref_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_ref_2103_ = lean_ctor_get(v___y_2039_, 2);
v___x_2104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2055_);
lean_inc(v_sp_2034_);
v___x_2105_ = l_Lean_SearchPath_findWithExt(v_sp_2034_, v___x_2104_, v_fst_2055_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
if (lean_obj_tag(v_a_2106_) == 0)
{
lean_object* v___x_2107_; lean_object* v_name_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_val_2099_);
lean_dec(v_snd_2057_);
v___x_2107_ = l_Lean_linter_doc_deferred;
v_name_2108_ = lean_ctor_get(v___x_2107_, 0);
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
lean_inc(v_fst_2055_);
v___x_2110_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2055_, v___x_2033_);
v___x_2111_ = lean_string_append(v___x_2109_, v___x_2110_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_2113_ = lean_string_append(v___x_2111_, v___x_2112_);
lean_inc(v_name_2108_);
v___x_2114_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2108_, v___x_2033_);
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
v___x_2118_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec_ref_known(v___x_2118_, 1);
lean_del_object(v___x_2101_);
lean_del_object(v___x_2053_);
v___x_2119_ = lean_box(v_unlocated_2047_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2119_);
v___x_2121_ = v___x_2059_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
v_a_2043_ = v___x_2121_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2059_);
lean_dec(v_fst_2056_);
lean_dec(v_sp_2034_);
v_a_2123_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2125_ = v___x_2118_;
v_isShared_2126_ = v_isSharedCheck_2138_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2138_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_io_error_to_string(v_a_2123_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 3);
lean_ctor_set(v___x_2101_, 0, v___x_2127_);
v___x_2129_ = v___x_2101_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = l_Lean_MessageData_ofFormat(v___x_2129_);
lean_inc(v_ref_2103_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2130_);
lean_ctor_set(v___x_2053_, 0, v_ref_2103_);
v___x_2132_ = v___x_2053_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_ref_2103_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2132_);
v___x_2134_ = v___x_2125_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2140_; lean_object* v_name_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_del_object(v___x_2101_);
lean_del_object(v___x_2053_);
v_val_2139_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v_a_2106_, 1);
v___x_2140_ = l_Lean_linter_doc_deferred;
v_name_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_name_2141_);
v___x_2142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2142_, 0, v_val_2139_);
lean_ctor_set(v___x_2142_, 1, v_val_2099_);
lean_ctor_set(v___x_2142_, 2, v_name_2141_);
v___x_2143_ = lean_array_push(v_fst_2056_, v___x_2142_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2143_);
v___x_2145_ = v___x_2059_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_snd_2057_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v_a_2043_ = v___x_2145_;
goto v___jp_2042_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_val_2099_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_dec(v_sp_2034_);
v_a_2147_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2149_ = v___x_2105_;
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2105_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_io_error_to_string(v_a_2147_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 3);
lean_ctor_set(v___x_2101_, 0, v___x_2151_);
v___x_2153_ = v___x_2101_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = l_Lean_MessageData_ofFormat(v___x_2153_);
lean_inc(v_ref_2103_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2154_);
lean_ctor_set(v___x_2053_, 0, v_ref_2103_);
v___x_2156_ = v___x_2053_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_ref_2103_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2156_);
v___x_2158_ = v___x_2149_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
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
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_site_2061_);
lean_del_object(v___x_2059_);
lean_dec(v_snd_2057_);
lean_dec(v_fst_2056_);
lean_del_object(v___x_2053_);
lean_dec(v_sp_2034_);
v_a_2164_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2062_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2062_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
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
v___jp_2042_:
{
size_t v___x_2044_; size_t v___x_2045_; 
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2037_, v___x_2044_);
v_i_2037_ = v___x_2045_;
v_b_2038_ = v_a_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v___x_2175_, lean_object* v_sp_2176_, lean_object* v_as_2177_, lean_object* v_sz_2178_, lean_object* v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_7554__boxed_2184_; size_t v_sz_boxed_2185_; size_t v_i_boxed_2186_; lean_object* v_res_2187_; 
v___x_7554__boxed_2184_ = lean_unbox(v___x_2175_);
v_sz_boxed_2185_ = lean_unbox_usize(v_sz_2178_);
lean_dec(v_sz_2178_);
v_i_boxed_2186_ = lean_unbox_usize(v_i_2179_);
lean_dec(v_i_2179_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_7554__boxed_2184_, v_sp_2176_, v_as_2177_, v_sz_boxed_2185_, v_i_boxed_2186_, v_b_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec_ref(v_as_2177_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object* v_sp_2194_, uint8_t v___y_2195_, lean_object* v_as_2196_, size_t v_sz_2197_, size_t v_i_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_a_2203_; uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_lt(v_i_2198_, v_sz_2197_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_sp_2194_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_b_2199_);
return v___x_2208_;
}
else
{
lean_object* v_a_2209_; lean_object* v_snd_2210_; lean_object* v_fst_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2306_; 
v_a_2209_ = lean_array_uget_borrowed(v_as_2196_, v_i_2198_);
v_snd_2210_ = lean_ctor_get(v_a_2209_, 1);
lean_inc(v_snd_2210_);
v_fst_2211_ = lean_ctor_get(v_snd_2210_, 0);
lean_inc(v_fst_2211_);
v_fst_2212_ = lean_ctor_get(v_a_2209_, 0);
v_snd_2213_ = lean_ctor_get(v_snd_2210_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_snd_2210_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v_snd_2210_, 0);
lean_dec(v_unused_2307_);
v___x_2215_ = v_snd_2210_;
v_isShared_2216_ = v_isSharedCheck_2306_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_dec(v_snd_2210_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2306_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_site_2217_; lean_object* v_sourceString_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_site_2217_ = lean_ctor_get(v_fst_2211_, 0);
lean_inc_ref(v_site_2217_);
v_sourceString_2218_ = lean_ctor_get(v_fst_2211_, 2);
lean_inc_ref(v_sourceString_2218_);
lean_dec(v_fst_2211_);
v___x_2219_ = lean_box(0);
v___x_2298_ = lean_string_utf8_byte_size(v_sourceString_2218_);
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = lean_nat_dec_eq(v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4));
v___x_2302_ = lean_string_append(v___x_2301_, v_sourceString_2218_);
lean_dec_ref(v_sourceString_2218_);
v___x_2303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___y_2221_ = v___x_2304_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2305_; 
lean_dec_ref(v_sourceString_2218_);
v___x_2305_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2221_ = v___x_2305_;
goto v___jp_2220_;
}
v___jp_2220_:
{
lean_object* v_ref_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_ref_2222_ = lean_ctor_get(v___y_2200_, 2);
v___x_2223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2212_);
lean_inc(v_sp_2194_);
v___x_2224_ = l_Lean_SearchPath_findWithExt(v_sp_2194_, v___x_2223_, v_fst_2212_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
if (lean_obj_tag(v_a_2225_) == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2226_ = l_Lean_MessageData_toString(v_snd_2213_);
v___x_2227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0));
lean_inc(v_fst_2212_);
v___x_2228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2212_, v___y_2195_);
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
v___x_2232_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2217_);
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = lean_string_append(v___x_2233_, v___y_2221_);
lean_dec_ref(v___y_2221_);
v___x_2235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2236_ = lean_string_append(v___x_2234_, v___x_2235_);
v___x_2237_ = lean_string_append(v___x_2236_, v___x_2226_);
lean_dec_ref(v___x_2226_);
v___x_2238_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_dec_ref_known(v___x_2238_, 1);
lean_del_object(v___x_2215_);
v_a_2203_ = v___x_2219_;
goto v___jp_2202_;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_sp_2194_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2252_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2252_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2243_ = lean_io_error_to_string(v_a_2239_);
v___x_2244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
v___x_2245_ = l_Lean_MessageData_ofFormat(v___x_2244_);
lean_inc(v_ref_2222_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2245_);
lean_ctor_set(v___x_2215_, 0, v_ref_2222_);
v___x_2247_ = v___x_2215_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_ref_2222_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2247_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v_val_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2283_; 
v_val_2253_ = lean_ctor_get(v_a_2225_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2255_ = v_a_2225_;
v_isShared_2256_ = v_isSharedCheck_2283_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_val_2253_);
lean_dec(v_a_2225_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2283_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2257_ = l_Lean_MessageData_toString(v_snd_2213_);
v___x_2258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3));
v___x_2259_ = lean_string_append(v_val_2253_, v___x_2258_);
v___x_2260_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2217_);
v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = lean_string_append(v___x_2261_, v___y_2221_);
lean_dec_ref(v___y_2221_);
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_string_append(v___x_2264_, v___x_2257_);
lean_dec_ref(v___x_2257_);
v___x_2266_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_dec_ref_known(v___x_2266_, 1);
lean_del_object(v___x_2255_);
lean_del_object(v___x_2215_);
v_a_2203_ = v___x_2219_;
goto v___jp_2202_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_sp_2194_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2282_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2282_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = lean_io_error_to_string(v_a_2267_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set_tag(v___x_2255_, 3);
lean_ctor_set(v___x_2255_, 0, v___x_2271_);
v___x_2273_ = v___x_2255_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = l_Lean_MessageData_ofFormat(v___x_2273_);
lean_inc(v_ref_2222_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2274_);
lean_ctor_set(v___x_2215_, 0, v_ref_2222_);
v___x_2276_ = v___x_2215_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_ref_2222_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2276_);
v___x_2278_ = v___x_2269_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
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
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_site_2217_);
lean_dec(v_snd_2213_);
lean_dec(v_sp_2194_);
v_a_2284_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2286_ = v___x_2224_;
v_isShared_2287_ = v_isSharedCheck_2297_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2224_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2297_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2288_ = lean_io_error_to_string(v_a_2284_);
v___x_2289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_ofFormat(v___x_2289_);
lean_inc(v_ref_2222_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2290_);
lean_ctor_set(v___x_2215_, 0, v_ref_2222_);
v___x_2292_ = v___x_2215_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_ref_2222_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2294_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2292_);
v___x_2294_ = v___x_2286_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
}
}
v___jp_2202_:
{
size_t v___x_2204_; size_t v___x_2205_; 
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_add(v_i_2198_, v___x_2204_);
v_i_2198_ = v___x_2205_;
v_b_2199_ = v_a_2203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object* v_sp_2308_, lean_object* v___y_2309_, lean_object* v_as_2310_, lean_object* v_sz_2311_, lean_object* v_i_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v___y_7836__boxed_2316_; size_t v_sz_boxed_2317_; size_t v_i_boxed_2318_; lean_object* v_res_2319_; 
v___y_7836__boxed_2316_ = lean_unbox(v___y_2309_);
v_sz_boxed_2317_ = lean_unbox_usize(v_sz_2311_);
lean_dec(v_sz_2311_);
v_i_boxed_2318_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2308_, v___y_7836__boxed_2316_, v_as_2310_, v_sz_boxed_2317_, v_i_boxed_2318_, v_b_2313_, v___y_2314_);
lean_dec_ref(v___y_2314_);
lean_dec_ref(v_as_2310_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2320_, lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_b_2324_){
_start:
{
lean_object* v_a_2327_; uint8_t v___x_2331_; 
v___x_2331_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_b_2324_);
return v___x_2332_;
}
else
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_array_uget_borrowed(v_as_2321_, v_i_2323_);
v___x_2334_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2320_, v_a_2333_);
if (v___x_2334_ == 0)
{
v_a_2327_ = v_b_2324_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2335_; 
lean_inc(v_a_2333_);
v___x_2335_ = l_Lean_NameSet_insert(v_b_2324_, v_a_2333_);
v_a_2327_ = v___x_2335_;
goto v___jp_2326_;
}
}
v___jp_2326_:
{
size_t v___x_2328_; size_t v___x_2329_; 
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2323_, v___x_2328_);
v_i_2323_ = v___x_2329_;
v_b_2324_ = v_a_2327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2336_, lean_object* v_as_2337_, lean_object* v_sz_2338_, lean_object* v_i_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_){
_start:
{
size_t v_sz_boxed_2342_; size_t v_i_boxed_2343_; lean_object* v_res_2344_; 
v_sz_boxed_2342_ = lean_unbox_usize(v_sz_2338_);
lean_dec(v_sz_2338_);
v_i_boxed_2343_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2336_, v_as_2337_, v_sz_boxed_2342_, v_i_boxed_2343_, v_b_2340_);
lean_dec_ref(v_as_2337_);
lean_dec(v_pkgRoot_2336_);
return v_res_2344_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_Options_empty;
v___x_2352_ = l_Lean_Core_getMaxHeartbeats(v___x_2351_);
return v___x_2352_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2353_; uint16_t v___x_2354_; 
v___x_2353_ = l_Lean_Options_empty;
v___x_2354_ = l_Lean_OptionFlags_ofOptions(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = l_Lean_firstFrontendMacroScope;
v___x_2357_ = lean_nat_add(v___x_2356_, v___x_2355_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = lean_unsigned_to_nat(32u);
v___x_2369_ = lean_mk_empty_array_with_capacity(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
size_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = ((size_t)5ULL);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_unsigned_to_nat(32u);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2375_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2376_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
lean_ctor_set(v___x_2376_, 2, v___x_2372_);
lean_ctor_set(v___x_2376_, 3, v___x_2372_);
lean_ctor_set_usize(v___x_2376_, 4, v___x_2371_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2377_; uint64_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2378_ = 0ULL;
v___x_2379_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set_uint64(v___x_2379_, sizeof(void*)*1, v___x_2378_);
return v___x_2379_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
return v___x_2384_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = l_Lean_Options_empty;
v___x_2387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
lean_ctor_set(v___x_2388_, 2, v___x_2387_);
lean_ctor_set(v___x_2388_, 3, v___x_2385_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = l_Lean_NameSet_empty;
v___x_2390_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
lean_ctor_set(v___x_2391_, 2, v___x_2389_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v_unlocated_2394_; lean_object* v___x_2395_; 
v___x_2392_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2393_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v_unlocated_2394_ = 1;
v___x_2395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2393_);
lean_ctor_set(v___x_2395_, 2, v___x_2392_);
lean_ctor_set_uint8(v___x_2395_, sizeof(void*)*3, v_unlocated_2394_);
return v___x_2395_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21(void){
_start:
{
uint16_t v___x_2396_; uint16_t v___x_2397_; uint16_t v___x_2398_; 
v___x_2396_ = 512;
v___x_2397_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2398_ = lean_uint16_land(v___x_2397_, v___x_2396_);
return v___x_2398_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22(void){
_start:
{
uint16_t v___x_2399_; uint16_t v___x_2400_; uint8_t v___x_2401_; 
v___x_2399_ = 0;
v___x_2400_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21);
v___x_2401_ = lean_uint16_dec_eq(v___x_2400_, v___x_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2402_, lean_object* v_linterOpts_2403_, lean_object* v_sp_2404_, lean_object* v_env_2405_, lean_object* v_pkgRoot_2406_, lean_object* v_docCheckedModules_2407_){
_start:
{
lean_object* v___y_2410_; lean_object* v_a_2414_; uint8_t v___y_2418_; lean_object* v_a_2419_; lean_object* v___y_2436_; lean_object* v_a_2437_; lean_object* v___y_2462_; uint8_t v___y_2463_; uint8_t v_lintOnly_2465_; uint8_t v_mode_2466_; lean_object* v___f_2467_; uint8_t v___y_2469_; lean_object* v___y_2470_; uint16_t v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2474_; lean_object* v___y_2475_; lean_object* v_fileName_2476_; lean_object* v_fileMap_2477_; lean_object* v_currNamespace_2478_; lean_object* v_openDecls_2479_; lean_object* v_initHeartbeats_2480_; lean_object* v_maxHeartbeats_2481_; lean_object* v_quotContext_2482_; lean_object* v_currMacroScope_2483_; lean_object* v_cancelTk_x3f_2484_; lean_object* v_inheritedTraceOptions_2485_; lean_object* v_currRecDepth_2486_; lean_object* v_ref_2487_; uint8_t v_suppressElabErrors_2488_; uint8_t v_isRecordingDeps_2489_; lean_object* v___y_2490_; uint8_t v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; uint16_t v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2566_; 
v_lintOnly_2465_ = lean_ctor_get_uint8(v_args_2402_, sizeof(void*)*4);
v_mode_2466_ = lean_ctor_get_uint8(v_args_2402_, sizeof(void*)*4 + 1);
v___f_2467_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2465_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = l_Lean_linter_doc_deferred;
v___x_2608_ = l_Lean_Linter_getLinterValue(v___x_2607_, v_linterOpts_2403_);
v___y_2566_ = v___x_2608_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2609_; lean_object* v_name_2610_; uint8_t v___x_2611_; 
v___x_2609_ = l_Lean_linter_doc_deferred;
v_name_2610_ = lean_ctor_get(v___x_2609_, 0);
v___x_2611_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2610_, v_linterOpts_2403_);
v___y_2566_ = v___x_2611_;
goto v___jp_2565_;
}
v___jp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___y_2410_);
lean_ctor_set(v___x_2411_, 1, v_docCheckedModules_2407_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
v___jp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_mk_io_user_error(v_a_2414_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
v___jp_2417_:
{
if (lean_obj_tag(v_a_2419_) == 0)
{
lean_object* v_msg_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_msg_2420_ = lean_ctor_get(v_a_2419_, 1);
lean_inc_ref(v_msg_2420_);
lean_dec_ref_known(v_a_2419_, 2);
v___x_2421_ = l_Lean_MessageData_toString(v_msg_2420_);
v___x_2422_ = lean_mk_io_user_error(v___x_2421_);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
else
{
lean_object* v_id_2424_; lean_object* v___x_2425_; 
v_id_2424_ = lean_ctor_get(v_a_2419_, 0);
lean_inc(v_id_2424_);
lean_dec_ref_known(v_a_2419_, 2);
v___x_2425_ = l_Lean_InternalExceptionId_getName(v_id_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v_id_2424_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2428_ = l_Lean_Name_toString(v_a_2426_, v___y_2418_);
v___x_2429_ = lean_string_append(v___x_2427_, v___x_2428_);
lean_dec_ref(v___x_2428_);
v_a_2414_ = v___x_2429_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec_ref_known(v___x_2425_, 1);
v___x_2430_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2431_ = l_Nat_reprFast(v_id_2424_);
v___x_2432_ = lean_string_append(v___x_2430_, v___x_2431_);
lean_dec_ref(v___x_2431_);
v___x_2433_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2434_ = lean_string_append(v___x_2432_, v___x_2433_);
v_a_2414_ = v___x_2434_;
goto v___jp_2413_;
}
}
}
v___jp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2438_ = lean_st_ref_get(v___y_2436_);
lean_dec(v___y_2436_);
lean_dec(v___x_2438_);
v___x_2439_ = l_Lean_Environment_header(v_env_2405_);
lean_dec_ref(v_env_2405_);
v___x_2440_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2439_);
v_sz_2441_ = lean_array_size(v___x_2440_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2406_, v___x_2440_, v_sz_2441_, v___x_2442_, v_docCheckedModules_2407_);
lean_dec_ref(v___x_2440_);
lean_dec(v_pkgRoot_2406_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2452_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2437_);
lean_ctor_set(v___x_2448_, 1, v_a_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_a_2437_);
v_a_2453_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2443_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2443_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
v___jp_2461_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2464_, 0, v___y_2463_);
v___y_2436_ = v___y_2462_;
v_a_2437_ = v___x_2464_;
goto v___jp_2435_;
}
v___jp_2468_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2491_ = l_Lean_maxRecDepth;
v___x_2492_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_2472_, v___x_2491_);
lean_inc_ref(v___y_2472_);
v___x_2493_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2493_, 0, v_fileName_2476_);
lean_ctor_set(v___x_2493_, 1, v_fileMap_2477_);
lean_ctor_set(v___x_2493_, 2, v___y_2472_);
lean_ctor_set(v___x_2493_, 3, v___x_2492_);
lean_ctor_set(v___x_2493_, 4, v_currNamespace_2478_);
lean_ctor_set(v___x_2493_, 5, v_openDecls_2479_);
lean_ctor_set(v___x_2493_, 6, v_initHeartbeats_2480_);
lean_ctor_set(v___x_2493_, 7, v_maxHeartbeats_2481_);
lean_ctor_set(v___x_2493_, 8, v_quotContext_2482_);
lean_ctor_set(v___x_2493_, 9, v_currMacroScope_2483_);
lean_ctor_set(v___x_2493_, 10, v_cancelTk_x3f_2484_);
lean_ctor_set(v___x_2493_, 11, v_inheritedTraceOptions_2485_);
v___x_2494_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v_currRecDepth_2486_);
lean_ctor_set(v___x_2494_, 2, v_ref_2487_);
lean_ctor_set_uint16(v___x_2494_, sizeof(void*)*3, v___y_2471_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*3 + 2, v_suppressElabErrors_2488_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*3 + 3, v_isRecordingDeps_2489_);
v___x_2495_ = l_Lean_Doc_DeferredCheck_run(v___y_2475_, v___f_2467_, v___x_2494_, v___y_2490_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; uint8_t v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = 1;
v___x_2498_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2466_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v___y_2490_);
v___x_2499_ = lean_box(0);
v_sz_2500_ = lean_array_size(v_a_2496_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2404_, v___y_2474_, v_a_2496_, v_sz_2500_, v___x_2501_, v___x_2499_, v___x_2494_);
lean_dec_ref_known(v___x_2494_, 3);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v___x_2503_; uint8_t v___x_2504_; 
lean_dec_ref_known(v___x_2502_, 1);
v___x_2503_ = lean_array_get_size(v_a_2496_);
lean_dec(v_a_2496_);
v___x_2504_ = lean_nat_dec_eq(v___x_2503_, v___y_2473_);
lean_dec(v___y_2473_);
if (v___x_2504_ == 0)
{
v___y_2462_ = v___y_2470_;
v___y_2463_ = v___y_2474_;
goto v___jp_2461_;
}
else
{
v___y_2462_ = v___y_2470_;
v___y_2463_ = v___x_2498_;
goto v___jp_2461_;
}
}
else
{
lean_object* v_a_2505_; 
lean_dec(v_a_2496_);
lean_dec(v___y_2473_);
lean_dec(v___y_2470_);
lean_dec(v_docCheckedModules_2407_);
lean_dec(v_pkgRoot_2406_);
lean_dec_ref(v_env_2405_);
v_a_2505_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2502_, 1);
v___y_2418_ = v___y_2474_;
v_a_2419_ = v_a_2505_;
goto v___jp_2417_;
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; size_t v_sz_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2506_ = lean_mk_empty_array_with_capacity(v___y_2473_);
lean_dec(v___y_2473_);
v___x_2507_ = lean_box(v___y_2469_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v_sz_2509_ = lean_array_size(v_a_2496_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2498_, v_sp_2404_, v_a_2496_, v_sz_2509_, v___x_2510_, v___x_2508_, v___x_2494_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref_known(v___x_2494_, 3);
lean_dec(v_a_2496_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v_fst_2513_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_fst_2513_);
v_snd_2514_ = lean_ctor_get(v_a_2512_, 1);
lean_inc(v_snd_2514_);
lean_dec(v_a_2512_);
v___x_2515_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2515_, 0, v_fst_2513_);
v___x_2516_ = lean_unbox(v_snd_2514_);
lean_dec(v_snd_2514_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2516_);
v___y_2436_ = v___y_2470_;
v_a_2437_ = v___x_2515_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2517_; 
lean_dec(v___y_2470_);
lean_dec(v_docCheckedModules_2407_);
lean_dec(v_pkgRoot_2406_);
lean_dec_ref(v_env_2405_);
v_a_2517_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2511_, 1);
v___y_2418_ = v___y_2474_;
v_a_2419_ = v_a_2517_;
goto v___jp_2417_;
}
}
}
else
{
lean_object* v_a_2518_; 
lean_dec_ref_known(v___x_2494_, 3);
lean_dec(v___y_2490_);
lean_dec(v___y_2473_);
lean_dec(v___y_2470_);
lean_dec(v_docCheckedModules_2407_);
lean_dec(v_pkgRoot_2406_);
lean_dec_ref(v_env_2405_);
lean_dec(v_sp_2404_);
v_a_2518_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2495_, 1);
v___y_2418_ = v___y_2474_;
v_a_2419_ = v_a_2518_;
goto v___jp_2417_;
}
}
v___jp_2519_:
{
lean_object* v___x_2530_; lean_object* v_env_2531_; lean_object* v_nextMacroScope_2532_; lean_object* v_ngen_2533_; lean_object* v_auxDeclNGen_2534_; lean_object* v_traceState_2535_; lean_object* v_recordedDeps_2536_; lean_object* v_messages_2537_; lean_object* v_infoState_2538_; lean_object* v_snapshotTasks_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2563_; 
v___x_2530_ = lean_st_ref_take(v___y_2523_);
v_env_2531_ = lean_ctor_get(v___x_2530_, 0);
v_nextMacroScope_2532_ = lean_ctor_get(v___x_2530_, 1);
v_ngen_2533_ = lean_ctor_get(v___x_2530_, 2);
v_auxDeclNGen_2534_ = lean_ctor_get(v___x_2530_, 3);
v_traceState_2535_ = lean_ctor_get(v___x_2530_, 4);
v_recordedDeps_2536_ = lean_ctor_get(v___x_2530_, 6);
v_messages_2537_ = lean_ctor_get(v___x_2530_, 7);
v_infoState_2538_ = lean_ctor_get(v___x_2530_, 8);
v_snapshotTasks_2539_ = lean_ctor_get(v___x_2530_, 9);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2530_, 5);
lean_dec(v_unused_2564_);
v___x_2541_ = v___x_2530_;
v_isShared_2542_ = v_isSharedCheck_2563_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_snapshotTasks_2539_);
lean_inc(v_infoState_2538_);
lean_inc(v_messages_2537_);
lean_inc(v_recordedDeps_2536_);
lean_inc(v_traceState_2535_);
lean_inc(v_auxDeclNGen_2534_);
lean_inc(v_ngen_2533_);
lean_inc(v_nextMacroScope_2532_);
lean_inc(v_env_2531_);
lean_dec(v___x_2530_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2563_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = l_Lean_Kernel_enableDiag(v_env_2531_, v___y_2520_);
lean_inc_ref(v___y_2522_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 5, v___y_2522_);
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_nextMacroScope_2532_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_ngen_2533_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_auxDeclNGen_2534_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_traceState_2535_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v___y_2522_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_recordedDeps_2536_);
lean_ctor_set(v_reuseFailAlloc_2562_, 7, v_messages_2537_);
lean_ctor_set(v_reuseFailAlloc_2562_, 8, v_infoState_2538_);
lean_ctor_set(v_reuseFailAlloc_2562_, 9, v_snapshotTasks_2539_);
v___x_2545_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v_toCold_2547_; lean_object* v_currRecDepth_2548_; lean_object* v_ref_2549_; uint8_t v_suppressElabErrors_2550_; uint8_t v_isRecordingDeps_2551_; lean_object* v_fileName_2552_; lean_object* v_fileMap_2553_; lean_object* v_currNamespace_2554_; lean_object* v_openDecls_2555_; lean_object* v_initHeartbeats_2556_; lean_object* v_maxHeartbeats_2557_; lean_object* v_quotContext_2558_; lean_object* v_currMacroScope_2559_; lean_object* v_cancelTk_x3f_2560_; lean_object* v_inheritedTraceOptions_2561_; 
v___x_2546_ = lean_st_ref_put(v___y_2523_, v___x_2545_);
v_toCold_2547_ = lean_ctor_get(v___y_2524_, 0);
lean_inc_ref(v_toCold_2547_);
v_currRecDepth_2548_ = lean_ctor_get(v___y_2524_, 1);
lean_inc(v_currRecDepth_2548_);
v_ref_2549_ = lean_ctor_get(v___y_2524_, 2);
lean_inc(v_ref_2549_);
v_suppressElabErrors_2550_ = lean_ctor_get_uint8(v___y_2524_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2551_ = lean_ctor_get_uint8(v___y_2524_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_2524_);
v_fileName_2552_ = lean_ctor_get(v_toCold_2547_, 0);
lean_inc_ref(v_fileName_2552_);
v_fileMap_2553_ = lean_ctor_get(v_toCold_2547_, 1);
lean_inc_ref(v_fileMap_2553_);
v_currNamespace_2554_ = lean_ctor_get(v_toCold_2547_, 4);
lean_inc(v_currNamespace_2554_);
v_openDecls_2555_ = lean_ctor_get(v_toCold_2547_, 5);
lean_inc(v_openDecls_2555_);
v_initHeartbeats_2556_ = lean_ctor_get(v_toCold_2547_, 6);
lean_inc(v_initHeartbeats_2556_);
v_maxHeartbeats_2557_ = lean_ctor_get(v_toCold_2547_, 7);
lean_inc(v_maxHeartbeats_2557_);
v_quotContext_2558_ = lean_ctor_get(v_toCold_2547_, 8);
lean_inc(v_quotContext_2558_);
v_currMacroScope_2559_ = lean_ctor_get(v_toCold_2547_, 9);
lean_inc(v_currMacroScope_2559_);
v_cancelTk_x3f_2560_ = lean_ctor_get(v_toCold_2547_, 10);
lean_inc(v_cancelTk_x3f_2560_);
v_inheritedTraceOptions_2561_ = lean_ctor_get(v_toCold_2547_, 11);
lean_inc_ref(v_inheritedTraceOptions_2561_);
lean_dec_ref(v_toCold_2547_);
lean_inc(v___y_2523_);
v___y_2469_ = v___y_2521_;
v___y_2470_ = v___y_2523_;
v___y_2471_ = v___y_2526_;
v___y_2472_ = v___y_2525_;
v___y_2473_ = v___y_2528_;
v___y_2474_ = v___y_2527_;
v___y_2475_ = v___y_2529_;
v_fileName_2476_ = v_fileName_2552_;
v_fileMap_2477_ = v_fileMap_2553_;
v_currNamespace_2478_ = v_currNamespace_2554_;
v_openDecls_2479_ = v_openDecls_2555_;
v_initHeartbeats_2480_ = v_initHeartbeats_2556_;
v_maxHeartbeats_2481_ = v_maxHeartbeats_2557_;
v_quotContext_2482_ = v_quotContext_2558_;
v_currMacroScope_2483_ = v_currMacroScope_2559_;
v_cancelTk_x3f_2484_ = v_cancelTk_x3f_2560_;
v_inheritedTraceOptions_2485_ = v_inheritedTraceOptions_2561_;
v_currRecDepth_2486_ = v_currRecDepth_2548_;
v_ref_2487_ = v_ref_2549_;
v_suppressElabErrors_2488_ = v_suppressElabErrors_2550_;
v_isRecordingDeps_2489_ = v_isRecordingDeps_2551_;
v___y_2490_ = v___y_2523_;
goto v___jp_2468_;
}
}
}
v___jp_2565_:
{
if (v___y_2566_ == 0)
{
uint8_t v___x_2567_; uint8_t v___x_2568_; 
lean_dec(v_pkgRoot_2406_);
lean_dec_ref(v_env_2405_);
lean_dec(v_sp_2404_);
v___x_2567_ = 1;
v___x_2568_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2466_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2569_, 0, v___x_2568_);
v___y_2410_ = v___x_2569_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2571_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*1, v___y_2566_);
v___y_2410_ = v___x_2571_;
goto v___jp_2409_;
}
}
else
{
lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint16_t v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_env_2604_; uint8_t v___x_2605_; uint8_t v___x_2606_; 
v___x_2572_ = lean_box(v___y_2566_);
lean_inc(v_docCheckedModules_2407_);
lean_inc(v_pkgRoot_2406_);
v___f_2573_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2573_, 0, v_pkgRoot_2406_);
lean_closure_set(v___f_2573_, 1, v_docCheckedModules_2407_);
lean_closure_set(v___f_2573_, 2, v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2575_ = l_Lean_instInhabitedFileMap_default;
v___x_2576_ = l_Lean_Options_empty;
v___x_2577_ = lean_unsigned_to_nat(1000u);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2582_ = l_Lean_firstFrontendMacroScope;
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2586_ = 0;
v___x_2587_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2588_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2589_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_2590_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2591_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2593_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2594_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2595_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
lean_inc_ref(v_env_2405_);
v___x_2596_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2596_, 0, v_env_2405_);
lean_ctor_set(v___x_2596_, 1, v___x_2587_);
lean_ctor_set(v___x_2596_, 2, v___x_2588_);
lean_ctor_set(v___x_2596_, 3, v___x_2589_);
lean_ctor_set(v___x_2596_, 4, v___x_2590_);
lean_ctor_set(v___x_2596_, 5, v___x_2591_);
lean_ctor_set(v___x_2596_, 6, v___x_2593_);
lean_ctor_set(v___x_2596_, 7, v___x_2594_);
lean_ctor_set(v___x_2596_, 8, v___x_2595_);
lean_ctor_set(v___x_2596_, 9, v___x_2592_);
v___x_2597_ = lean_io_get_num_heartbeats();
v___x_2598_ = lean_st_mk_ref(v___x_2596_);
v___x_2599_ = l_Lean_inheritedTraceOptions;
v___x_2600_ = lean_st_ref_get(v___x_2599_);
lean_inc(v___x_2600_);
lean_inc(v___x_2597_);
v___x_2601_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2574_);
lean_ctor_set(v___x_2601_, 1, v___x_2575_);
lean_ctor_set(v___x_2601_, 2, v___x_2576_);
lean_ctor_set(v___x_2601_, 3, v___x_2577_);
lean_ctor_set(v___x_2601_, 4, v___x_2578_);
lean_ctor_set(v___x_2601_, 5, v___x_2579_);
lean_ctor_set(v___x_2601_, 6, v___x_2597_);
lean_ctor_set(v___x_2601_, 7, v___x_2581_);
lean_ctor_set(v___x_2601_, 8, v___x_2578_);
lean_ctor_set(v___x_2601_, 9, v___x_2582_);
lean_ctor_set(v___x_2601_, 10, v___x_2583_);
lean_ctor_set(v___x_2601_, 11, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2580_);
lean_ctor_set(v___x_2602_, 2, v___x_2584_);
lean_ctor_set_uint16(v___x_2602_, sizeof(void*)*3, v___x_2585_);
lean_ctor_set_uint8(v___x_2602_, sizeof(void*)*3 + 2, v___x_2586_);
lean_ctor_set_uint8(v___x_2602_, sizeof(void*)*3 + 3, v___x_2586_);
v___x_2603_ = lean_st_ref_get(v___x_2598_);
v_env_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc_ref(v_env_2604_);
lean_dec(v___x_2603_);
v___x_2605_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2604_);
lean_dec_ref(v_env_2604_);
v___x_2606_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_2606_ == 0)
{
if (v___x_2605_ == 0)
{
lean_dec(v___x_2600_);
lean_dec(v___x_2597_);
v___y_2520_ = v___y_2566_;
v___y_2521_ = v___x_2586_;
v___y_2522_ = v___x_2591_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2602_;
v___y_2525_ = v___x_2576_;
v___y_2526_ = v___x_2585_;
v___y_2527_ = v___y_2566_;
v___y_2528_ = v___x_2580_;
v___y_2529_ = v___f_2573_;
goto v___jp_2519_;
}
else
{
lean_dec_ref_known(v___x_2602_, 3);
lean_inc(v___x_2598_);
v___y_2469_ = v___x_2586_;
v___y_2470_ = v___x_2598_;
v___y_2471_ = v___x_2585_;
v___y_2472_ = v___x_2576_;
v___y_2473_ = v___x_2580_;
v___y_2474_ = v___y_2566_;
v___y_2475_ = v___f_2573_;
v_fileName_2476_ = v___x_2574_;
v_fileMap_2477_ = v___x_2575_;
v_currNamespace_2478_ = v___x_2578_;
v_openDecls_2479_ = v___x_2579_;
v_initHeartbeats_2480_ = v___x_2597_;
v_maxHeartbeats_2481_ = v___x_2581_;
v_quotContext_2482_ = v___x_2578_;
v_currMacroScope_2483_ = v___x_2582_;
v_cancelTk_x3f_2484_ = v___x_2583_;
v_inheritedTraceOptions_2485_ = v___x_2600_;
v_currRecDepth_2486_ = v___x_2580_;
v_ref_2487_ = v___x_2584_;
v_suppressElabErrors_2488_ = v___x_2586_;
v_isRecordingDeps_2489_ = v___x_2586_;
v___y_2490_ = v___x_2598_;
goto v___jp_2468_;
}
}
else
{
if (v___x_2605_ == 0)
{
lean_dec_ref_known(v___x_2602_, 3);
lean_inc(v___x_2598_);
v___y_2469_ = v___x_2586_;
v___y_2470_ = v___x_2598_;
v___y_2471_ = v___x_2585_;
v___y_2472_ = v___x_2576_;
v___y_2473_ = v___x_2580_;
v___y_2474_ = v___y_2566_;
v___y_2475_ = v___f_2573_;
v_fileName_2476_ = v___x_2574_;
v_fileMap_2477_ = v___x_2575_;
v_currNamespace_2478_ = v___x_2578_;
v_openDecls_2479_ = v___x_2579_;
v_initHeartbeats_2480_ = v___x_2597_;
v_maxHeartbeats_2481_ = v___x_2581_;
v_quotContext_2482_ = v___x_2578_;
v_currMacroScope_2483_ = v___x_2582_;
v_cancelTk_x3f_2484_ = v___x_2583_;
v_inheritedTraceOptions_2485_ = v___x_2600_;
v_currRecDepth_2486_ = v___x_2580_;
v_ref_2487_ = v___x_2584_;
v_suppressElabErrors_2488_ = v___x_2586_;
v_isRecordingDeps_2489_ = v___x_2586_;
v___y_2490_ = v___x_2598_;
goto v___jp_2468_;
}
else
{
lean_dec(v___x_2600_);
lean_dec(v___x_2597_);
v___y_2520_ = v___x_2586_;
v___y_2521_ = v___x_2586_;
v___y_2522_ = v___x_2591_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2602_;
v___y_2525_ = v___x_2576_;
v___y_2526_ = v___x_2585_;
v___y_2527_ = v___y_2566_;
v___y_2528_ = v___x_2580_;
v___y_2529_ = v___f_2573_;
goto v___jp_2519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2612_, lean_object* v_linterOpts_2613_, lean_object* v_sp_2614_, lean_object* v_env_2615_, lean_object* v_pkgRoot_2616_, lean_object* v_docCheckedModules_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2612_, v_linterOpts_2613_, v_sp_2614_, v_env_2615_, v_pkgRoot_2616_, v_docCheckedModules_2617_);
lean_dec_ref(v_linterOpts_2613_);
lean_dec_ref(v_args_2612_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_sp_2620_, uint8_t v___y_2621_, lean_object* v_as_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2620_, v___y_2621_, v_as_2622_, v_sz_2623_, v_i_2624_, v_b_2625_, v___y_2626_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_sp_2630_, lean_object* v___y_2631_, lean_object* v_as_2632_, lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v___y_8578__boxed_2639_; size_t v_sz_boxed_2640_; size_t v_i_boxed_2641_; lean_object* v_res_2642_; 
v___y_8578__boxed_2639_ = lean_unbox(v___y_2631_);
v_sz_boxed_2640_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2641_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2630_, v___y_8578__boxed_2639_, v_as_2632_, v_sz_boxed_2640_, v_i_boxed_2641_, v_b_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_as_2632_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2643_, lean_object* v_as_2644_, size_t v_i_2645_, size_t v_stop_2646_, lean_object* v_b_2647_){
_start:
{
lean_object* v___y_2649_; uint8_t v___x_2653_; 
v___x_2653_ = lean_usize_dec_eq(v_i_2645_, v_stop_2646_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v_linter_2655_; uint8_t v___x_2656_; 
v___x_2654_ = lean_array_uget_borrowed(v_as_2644_, v_i_2645_);
v_linter_2655_ = lean_ctor_get(v___x_2654_, 0);
v___x_2656_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2655_, v_linterOpts_2643_);
if (v___x_2656_ == 0)
{
v___y_2649_ = v_b_2647_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2657_; 
lean_inc(v___x_2654_);
v___x_2657_ = lean_array_push(v_b_2647_, v___x_2654_);
v___y_2649_ = v___x_2657_;
goto v___jp_2648_;
}
}
else
{
return v_b_2647_;
}
v___jp_2648_:
{
size_t v___x_2650_; size_t v___x_2651_; 
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2645_, v___x_2650_);
v_i_2645_ = v___x_2651_;
v_b_2647_ = v___y_2649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2658_, lean_object* v_as_2659_, lean_object* v_i_2660_, lean_object* v_stop_2661_, lean_object* v_b_2662_){
_start:
{
size_t v_i_boxed_2663_; size_t v_stop_boxed_2664_; lean_object* v_res_2665_; 
v_i_boxed_2663_ = lean_unbox_usize(v_i_2660_);
lean_dec(v_i_2660_);
v_stop_boxed_2664_ = lean_unbox_usize(v_stop_2661_);
lean_dec(v_stop_2661_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2658_, v_as_2659_, v_i_boxed_2663_, v_stop_boxed_2664_, v_b_2662_);
lean_dec_ref(v_as_2659_);
lean_dec_ref(v_linterOpts_2658_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2668_, lean_object* v_as_2669_, size_t v_i_2670_, size_t v_stop_2671_, lean_object* v_b_2672_){
_start:
{
lean_object* v___y_2674_; uint8_t v___x_2678_; 
v___x_2678_ = lean_usize_dec_eq(v_i_2670_, v_stop_2671_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2705_; 
v___x_2679_ = lean_array_uget(v_as_2669_, v_i_2670_);
v_fst_2680_ = lean_ctor_get(v___x_2679_, 0);
v_snd_2681_ = lean_ctor_get(v___x_2679_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2683_ = v___x_2679_;
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v___x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___y_2686_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_array_get_size(v_snd_2681_);
v___x_2696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2697_ = lean_nat_dec_lt(v___x_2694_, v___x_2695_);
if (v___x_2697_ == 0)
{
lean_dec(v_snd_2681_);
v___y_2686_ = v___x_2696_;
goto v___jp_2685_;
}
else
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_nat_dec_le(v___x_2695_, v___x_2695_);
if (v___x_2698_ == 0)
{
if (v___x_2697_ == 0)
{
lean_dec(v_snd_2681_);
v___y_2686_ = v___x_2696_;
goto v___jp_2685_;
}
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2695_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2668_, v_snd_2681_, v___x_2699_, v___x_2700_, v___x_2696_);
lean_dec(v_snd_2681_);
v___y_2686_ = v___x_2701_;
goto v___jp_2685_;
}
}
else
{
size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = lean_usize_of_nat(v___x_2695_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2668_, v_snd_2681_, v___x_2702_, v___x_2703_, v___x_2696_);
lean_dec(v_snd_2681_);
v___y_2686_ = v___x_2704_;
goto v___jp_2685_;
}
}
v___jp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2687_ = lean_array_get_size(v___y_2686_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_nat_dec_eq(v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2691_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___y_2686_);
v___x_2691_ = v___x_2683_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___y_2686_);
v___x_2691_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_array_push(v_b_2672_, v___x_2691_);
v___y_2674_ = v___x_2692_;
goto v___jp_2673_;
}
}
else
{
lean_dec_ref(v___y_2686_);
lean_del_object(v___x_2683_);
lean_dec(v_fst_2680_);
v___y_2674_ = v_b_2672_;
goto v___jp_2673_;
}
}
}
}
else
{
return v_b_2672_;
}
v___jp_2673_:
{
size_t v___x_2675_; size_t v___x_2676_; 
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_add(v_i_2670_, v___x_2675_);
v_i_2670_ = v___x_2676_;
v_b_2672_ = v___y_2674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2706_, lean_object* v_as_2707_, lean_object* v_i_2708_, lean_object* v_stop_2709_, lean_object* v_b_2710_){
_start:
{
size_t v_i_boxed_2711_; size_t v_stop_boxed_2712_; lean_object* v_res_2713_; 
v_i_boxed_2711_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_stop_boxed_2712_ = lean_unbox_usize(v_stop_2709_);
lean_dec(v_stop_2709_);
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2706_, v_as_2707_, v_i_boxed_2711_, v_stop_boxed_2712_, v_b_2710_);
lean_dec_ref(v_as_2707_);
lean_dec_ref(v_linterOpts_2706_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2714_, lean_object* v_as_2715_, lean_object* v_start_2716_, lean_object* v_stop_2717_){
_start:
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2719_ = lean_nat_dec_lt(v_start_2716_, v_stop_2717_);
if (v___x_2719_ == 0)
{
return v___x_2718_;
}
else
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = lean_array_get_size(v_as_2715_);
v___x_2721_ = lean_nat_dec_le(v_stop_2717_, v___x_2720_);
if (v___x_2721_ == 0)
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_nat_dec_lt(v_start_2716_, v___x_2720_);
if (v___x_2722_ == 0)
{
return v___x_2718_;
}
else
{
size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_usize_of_nat(v_start_2716_);
v___x_2724_ = lean_usize_of_nat(v___x_2720_);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2714_, v_as_2715_, v___x_2723_, v___x_2724_, v___x_2718_);
return v___x_2725_;
}
}
else
{
size_t v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_usize_of_nat(v_start_2716_);
v___x_2727_ = lean_usize_of_nat(v_stop_2717_);
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2714_, v_as_2715_, v___x_2726_, v___x_2727_, v___x_2718_);
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2729_, lean_object* v_as_2730_, lean_object* v_start_2731_, lean_object* v_stop_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2729_, v_as_2730_, v_start_2731_, v_stop_2732_);
lean_dec(v_stop_2732_);
lean_dec(v_start_2731_);
lean_dec_ref(v_as_2730_);
lean_dec_ref(v_linterOpts_2729_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2734_, lean_object* v_init_2735_, lean_object* v_x_2736_){
_start:
{
if (lean_obj_tag(v_x_2736_) == 0)
{
lean_object* v_k_2738_; lean_object* v_v_2739_; lean_object* v_l_2740_; lean_object* v_r_2741_; uint8_t v_anyUnlocated_2742_; lean_object* v___x_2743_; lean_object* v_a_2744_; lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2758_; 
v_k_2738_ = lean_ctor_get(v_x_2736_, 1);
lean_inc(v_k_2738_);
v_v_2739_ = lean_ctor_get(v_x_2736_, 2);
lean_inc(v_v_2739_);
v_l_2740_ = lean_ctor_get(v_x_2736_, 3);
lean_inc(v_l_2740_);
v_r_2741_ = lean_ctor_get(v_x_2736_, 4);
lean_inc(v_r_2741_);
lean_dec_ref_known(v_x_2736_, 5);
v_anyUnlocated_2742_ = 1;
lean_inc(v_fst_2734_);
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2734_, v_init_2735_, v_l_2740_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v_a_2745_ = lean_ctor_get(v_a_2744_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_a_2744_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2747_ = v_a_2744_;
v_isShared_2748_ = v_isSharedCheck_2758_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v_a_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2758_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2749_ = l_Lean_Name_toString(v_k_2738_, v_anyUnlocated_2742_);
lean_inc(v_fst_2734_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
lean_ctor_set(v___x_2747_, 0, v_fst_2734_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_fst_2734_);
v___x_2751_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
double v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2752_ = lean_float_of_nat(v_v_2739_);
v___x_2753_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2753_, 0, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2749_);
lean_ctor_set(v___x_2754_, 1, v___x_2751_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v___x_2755_ = lean_array_push(v_a_2745_, v___x_2754_);
v_init_2735_ = v___x_2755_;
v_x_2736_ = v_r_2741_;
goto _start;
}
}
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v_fst_2734_);
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_init_2735_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2761_, lean_object* v_init_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2761_, v_init_2762_, v_x_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2766_, lean_object* v_k_2767_, lean_object* v_fallback_2768_){
_start:
{
if (lean_obj_tag(v_t_2766_) == 0)
{
lean_object* v_k_2769_; lean_object* v_v_2770_; lean_object* v_l_2771_; lean_object* v_r_2772_; uint8_t v___x_2773_; 
v_k_2769_ = lean_ctor_get(v_t_2766_, 1);
v_v_2770_ = lean_ctor_get(v_t_2766_, 2);
v_l_2771_ = lean_ctor_get(v_t_2766_, 3);
v_r_2772_ = lean_ctor_get(v_t_2766_, 4);
v___x_2773_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2767_, v_k_2769_);
switch(v___x_2773_)
{
case 0:
{
v_t_2766_ = v_l_2771_;
goto _start;
}
case 1:
{
lean_inc(v_v_2770_);
return v_v_2770_;
}
default: 
{
v_t_2766_ = v_r_2772_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2768_);
return v_fallback_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2776_, lean_object* v_k_2777_, lean_object* v_fallback_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2776_, v_k_2777_, v_fallback_2778_);
lean_dec(v_fallback_2778_);
lean_dec(v_k_2777_);
lean_dec(v_t_2776_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2780_, size_t v_i_2781_, size_t v_stop_2782_, lean_object* v_b_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_usize_dec_eq(v_i_2781_, v_stop_2782_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v_linter_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; 
v___x_2785_ = lean_array_uget_borrowed(v_as_2780_, v_i_2781_);
v_linter_2786_ = lean_ctor_get(v___x_2785_, 0);
v___x_2787_ = lean_unsigned_to_nat(0u);
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2783_, v_linter_2786_, v___x_2787_);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v___x_2788_, v___x_2789_);
lean_dec(v___x_2788_);
lean_inc(v_linter_2786_);
v___x_2791_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2786_, v___x_2790_, v_b_2783_);
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_add(v_i_2781_, v___x_2792_);
v_i_2781_ = v___x_2793_;
v_b_2783_ = v___x_2791_;
goto _start;
}
else
{
return v_b_2783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_){
_start:
{
size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_i_boxed_2799_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2795_, v_i_boxed_2799_, v_stop_boxed_2800_, v_b_2798_);
lean_dec_ref(v_as_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2802_, size_t v_sz_2803_, size_t v_i_2804_, lean_object* v_b_2805_){
_start:
{
lean_object* v_a_2808_; uint8_t v___x_2812_; 
v___x_2812_ = lean_usize_dec_lt(v_i_2804_, v_sz_2803_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_b_2805_);
return v___x_2813_;
}
else
{
lean_object* v_a_2814_; lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___y_2818_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_a_2814_ = lean_array_uget_borrowed(v_as_2802_, v_i_2804_);
v_fst_2815_ = lean_ctor_get(v_a_2814_, 0);
v_snd_2816_ = lean_ctor_get(v_a_2814_, 1);
v___x_2840_ = lean_box(1);
v___x_2841_ = lean_unsigned_to_nat(0u);
v___x_2842_ = lean_array_get_size(v_snd_2816_);
v___x_2843_ = lean_nat_dec_lt(v___x_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
v___y_2818_ = v___x_2840_;
goto v___jp_2817_;
}
else
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_nat_dec_le(v___x_2842_, v___x_2842_);
if (v___x_2844_ == 0)
{
if (v___x_2843_ == 0)
{
v___y_2818_ = v___x_2840_;
goto v___jp_2817_;
}
else
{
size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = lean_usize_of_nat(v___x_2842_);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2816_, v___x_2845_, v___x_2846_, v___x_2840_);
v___y_2818_ = v___x_2847_;
goto v___jp_2817_;
}
}
else
{
size_t v___x_2848_; size_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = ((size_t)0ULL);
v___x_2849_ = lean_usize_of_nat(v___x_2842_);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2816_, v___x_2848_, v___x_2849_, v___x_2840_);
v___y_2818_ = v___x_2850_;
goto v___jp_2817_;
}
}
v___jp_2817_:
{
lean_object* v___x_2819_; 
lean_inc(v_fst_2815_);
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2815_, v_b_2805_, v___y_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v_a_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v_a_2821_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_a_2821_);
lean_dec(v_a_2820_);
v_a_2808_ = v_a_2821_;
goto v___jp_2807_;
}
else
{
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2831_; 
v_a_2822_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2824_ = v___x_2819_;
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2819_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2831_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
if (lean_obj_tag(v_a_2822_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; 
v_a_2826_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v_a_2822_, 1);
if (v_isShared_2825_ == 0)
{
lean_ctor_set_tag(v___x_2824_, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2826_);
v___x_2828_ = v___x_2824_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
else
{
lean_object* v_a_2830_; 
lean_del_object(v___x_2824_);
v_a_2830_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v_a_2822_, 1);
v_a_2808_ = v_a_2830_;
goto v___jp_2807_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2832_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2819_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2819_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
}
v___jp_2807_:
{
size_t v___x_2809_; size_t v___x_2810_; 
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2804_, v___x_2809_);
v_i_2804_ = v___x_2810_;
v_b_2805_ = v_a_2808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2851_, lean_object* v_sz_2852_, lean_object* v_i_2853_, lean_object* v_b_2854_, lean_object* v___y_2855_){
_start:
{
size_t v_sz_boxed_2856_; size_t v_i_boxed_2857_; lean_object* v_res_2858_; 
v_sz_boxed_2856_ = lean_unbox_usize(v_sz_2852_);
lean_dec(v_sz_2852_);
v_i_boxed_2857_ = lean_unbox_usize(v_i_2853_);
lean_dec(v_i_2853_);
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2851_, v_sz_boxed_2856_, v_i_boxed_2857_, v_b_2854_);
lean_dec_ref(v_as_2851_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2862_, lean_object* v_as_2863_, size_t v_sz_2864_, size_t v_i_2865_, lean_object* v_b_2866_){
_start:
{
lean_object* v_a_2869_; uint8_t v_anyUnlocated_2873_; 
v_anyUnlocated_2873_ = lean_usize_dec_lt(v_i_2865_, v_sz_2864_);
if (v_anyUnlocated_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v_fst_2862_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_b_2866_);
return v___x_2874_;
}
else
{
lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2913_; 
v_fst_2875_ = lean_ctor_get(v_b_2866_, 0);
v_snd_2876_ = lean_ctor_get(v_b_2866_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_b_2866_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2878_ = v_b_2866_;
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snd_2876_);
lean_inc(v_fst_2875_);
lean_dec(v_b_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_a_2880_; lean_object* v_position_x3f_2881_; 
v_a_2880_ = lean_array_uget_borrowed(v_as_2863_, v_i_2865_);
v_position_x3f_2881_ = lean_ctor_get(v_a_2880_, 2);
if (lean_obj_tag(v_position_x3f_2881_) == 0)
{
lean_object* v_linter_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec(v_snd_2876_);
v_linter_2882_ = lean_ctor_get(v_a_2880_, 0);
v___x_2883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2882_);
v___x_2884_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2882_, v_anyUnlocated_2873_);
v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2887_ = lean_string_append(v___x_2885_, v___x_2886_);
lean_inc(v_fst_2862_);
v___x_2888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2862_, v_anyUnlocated_2873_);
v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
v___x_2892_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec_ref_known(v___x_2892_, 1);
v___x_2893_ = lean_box(v_anyUnlocated_2873_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2893_);
v___x_2895_ = v___x_2878_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_fst_2875_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
v_a_2869_ = v___x_2895_;
goto v___jp_2868_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_del_object(v___x_2878_);
lean_dec(v_fst_2875_);
lean_dec(v_fst_2862_);
v_a_2897_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2892_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2892_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_linter_2905_; lean_object* v_file_2906_; lean_object* v_val_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v_linter_2905_ = lean_ctor_get(v_a_2880_, 0);
v_file_2906_ = lean_ctor_get(v_a_2880_, 3);
v_val_2907_ = lean_ctor_get(v_position_x3f_2881_, 0);
lean_inc(v_linter_2905_);
lean_inc(v_val_2907_);
lean_inc_ref(v_file_2906_);
v___x_2908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2908_, 0, v_file_2906_);
lean_ctor_set(v___x_2908_, 1, v_val_2907_);
lean_ctor_set(v___x_2908_, 2, v_linter_2905_);
v___x_2909_ = lean_array_push(v_fst_2875_, v___x_2908_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2909_);
v___x_2911_ = v___x_2878_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_snd_2876_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v_a_2869_ = v___x_2911_;
goto v___jp_2868_;
}
}
}
}
v___jp_2868_:
{
size_t v___x_2870_; size_t v___x_2871_; 
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_add(v_i_2865_, v___x_2870_);
v_i_2865_ = v___x_2871_;
v_b_2866_ = v_a_2869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2914_, lean_object* v_as_2915_, lean_object* v_sz_2916_, lean_object* v_i_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_){
_start:
{
size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2916_);
lean_dec(v_sz_2916_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2914_, v_as_2915_, v_sz_boxed_2920_, v_i_boxed_2921_, v_b_2918_);
lean_dec_ref(v_as_2915_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2923_, size_t v_sz_2924_, size_t v_i_2925_, lean_object* v_b_2926_){
_start:
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_usize_dec_lt(v_i_2925_, v_sz_2924_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_b_2926_);
return v___x_2929_;
}
else
{
lean_object* v_a_2930_; lean_object* v_fst_2931_; lean_object* v_snd_2932_; lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2957_; 
v_a_2930_ = lean_array_uget_borrowed(v_as_2923_, v_i_2925_);
v_fst_2931_ = lean_ctor_get(v_a_2930_, 0);
v_snd_2932_ = lean_ctor_get(v_a_2930_, 1);
v_fst_2933_ = lean_ctor_get(v_b_2926_, 0);
v_snd_2934_ = lean_ctor_get(v_b_2926_, 1);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_b_2926_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2936_ = v_b_2926_;
v_isShared_2937_ = v_isSharedCheck_2957_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_snd_2934_);
lean_inc(v_fst_2933_);
lean_dec(v_b_2926_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2957_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_fst_2933_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_snd_2934_);
v___x_2939_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
size_t v_sz_2940_; size_t v___x_2941_; lean_object* v___x_2942_; 
v_sz_2940_ = lean_array_size(v_snd_2932_);
v___x_2941_ = ((size_t)0ULL);
lean_inc(v_fst_2931_);
v___x_2942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2931_, v_snd_2932_, v_sz_2940_, v___x_2941_, v___x_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v_fst_2944_; lean_object* v_snd_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2955_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v_fst_2944_ = lean_ctor_get(v_a_2943_, 0);
v_snd_2945_ = lean_ctor_get(v_a_2943_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_a_2943_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2947_ = v_a_2943_;
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snd_2945_);
lean_inc(v_fst_2944_);
lean_dec(v_a_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2955_;
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
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_fst_2944_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_snd_2945_);
v___x_2950_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
size_t v___x_2951_; size_t v___x_2952_; 
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_add(v_i_2925_, v___x_2951_);
v_i_2925_ = v___x_2952_;
v_b_2926_ = v___x_2950_;
goto _start;
}
}
}
else
{
return v___x_2942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2958_, lean_object* v_sz_2959_, lean_object* v_i_2960_, lean_object* v_b_2961_, lean_object* v___y_2962_){
_start:
{
size_t v_sz_boxed_2963_; size_t v_i_boxed_2964_; lean_object* v_res_2965_; 
v_sz_boxed_2963_ = lean_unbox_usize(v_sz_2959_);
lean_dec(v_sz_2959_);
v_i_boxed_2964_ = lean_unbox_usize(v_i_2960_);
lean_dec(v_i_2960_);
v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2958_, v_sz_boxed_2963_, v_i_boxed_2964_, v_b_2961_);
lean_dec_ref(v_as_2958_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2966_, size_t v_sz_2967_, size_t v_i_2968_, lean_object* v_b_2969_){
_start:
{
uint8_t v___x_2971_; 
v___x_2971_ = lean_usize_dec_lt(v_i_2968_, v_sz_2967_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_b_2969_);
return v___x_2972_;
}
else
{
lean_object* v_a_2973_; lean_object* v_message_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2973_ = lean_array_uget_borrowed(v_as_2966_, v_i_2968_);
v_message_2974_ = lean_ctor_get(v_a_2973_, 1);
v___x_2975_ = lean_box(0);
v___x_2976_ = 0;
lean_inc_ref(v_message_2974_);
v___x_2977_ = l_Lean_SerialMessage_toString(v_message_2974_, v___x_2976_);
v___x_2978_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
size_t v___x_2979_; size_t v___x_2980_; 
lean_dec_ref_known(v___x_2978_, 1);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_add(v_i_2968_, v___x_2979_);
v_i_2968_ = v___x_2980_;
v_b_2969_ = v___x_2975_;
goto _start;
}
else
{
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2982_, lean_object* v_sz_2983_, lean_object* v_i_2984_, lean_object* v_b_2985_, lean_object* v___y_2986_){
_start:
{
size_t v_sz_boxed_2987_; size_t v_i_boxed_2988_; lean_object* v_res_2989_; 
v_sz_boxed_2987_ = lean_unbox_usize(v_sz_2983_);
lean_dec(v_sz_2983_);
v_i_boxed_2988_ = lean_unbox_usize(v_i_2984_);
lean_dec(v_i_2984_);
v_res_2989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2982_, v_sz_boxed_2987_, v_i_boxed_2988_, v_b_2985_);
lean_dec_ref(v_as_2982_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2992_, size_t v_sz_2993_, size_t v_i_2994_, lean_object* v_b_2995_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_usize_dec_lt(v_i_2994_, v_sz_2993_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2995_);
return v___x_2998_;
}
else
{
lean_object* v_a_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_2999_ = lean_array_uget_borrowed(v_as_2992_, v_i_2994_);
v_fst_3000_ = lean_ctor_get(v_a_2999_, 0);
v_snd_3001_ = lean_ctor_get(v_a_2999_, 1);
v___x_3002_ = lean_box(0);
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_3000_);
v___x_3004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3000_, v___x_2997_);
v___x_3005_ = lean_string_append(v___x_3003_, v___x_3004_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_3007_ = lean_string_append(v___x_3005_, v___x_3006_);
v___x_3008_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_3007_);
if (lean_obj_tag(v___x_3008_) == 0)
{
size_t v_sz_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref_known(v___x_3008_, 1);
v_sz_3009_ = lean_array_size(v_snd_3001_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_3001_, v_sz_3009_, v___x_3010_, v___x_3002_);
if (lean_obj_tag(v___x_3011_) == 0)
{
size_t v___x_3012_; size_t v___x_3013_; 
lean_dec_ref_known(v___x_3011_, 1);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_2994_, v___x_3012_);
v_i_2994_ = v___x_3013_;
v_b_2995_ = v___x_3002_;
goto _start;
}
else
{
return v___x_3011_;
}
}
else
{
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_3015_, lean_object* v_sz_3016_, lean_object* v_i_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3016_);
lean_dec(v_sz_3016_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_3015_, v_sz_boxed_3020_, v_i_boxed_3021_, v_b_3018_);
lean_dec_ref(v_as_3015_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_3027_, lean_object* v_linterOpts_3028_, lean_object* v_env_3029_, lean_object* v_mod_3030_){
_start:
{
uint8_t v_lintOnly_3032_; uint8_t v_mode_3033_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3104_; lean_object* v___x_3110_; lean_object* v_textGroups_3111_; 
v_lintOnly_3032_ = lean_ctor_get_uint8(v_args_3027_, sizeof(void*)*4);
v_mode_3033_ = lean_ctor_get_uint8(v_args_3027_, sizeof(void*)*4 + 1);
v___x_3110_ = l_Lean_Name_getRoot(v_mod_3030_);
v_textGroups_3111_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_3029_, v___x_3110_);
lean_dec(v___x_3110_);
if (v_lintOnly_3032_ == 0)
{
v___y_3104_ = v_textGroups_3111_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = lean_array_get_size(v_textGroups_3111_);
v___x_3114_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_3028_, v_textGroups_3111_, v___x_3112_, v___x_3113_);
lean_dec_ref(v_textGroups_3111_);
v___y_3104_ = v___x_3114_;
goto v___jp_3103_;
}
v___jp_3034_:
{
switch(v_mode_3033_)
{
case 0:
{
lean_object* v___x_3037_; size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3037_ = lean_box(0);
v_sz_3038_ = lean_array_size(v___y_3035_);
v___x_3039_ = ((size_t)0ULL);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_3035_, v_sz_3038_, v___x_3039_, v___x_3037_);
lean_dec_ref(v___y_3035_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3048_; 
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3049_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3048_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3048_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3044_, 0, v___y_3036_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3044_);
v___x_3046_ = v___x_3042_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3040_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
case 1:
{
lean_object* v___x_3058_; size_t v_sz_3059_; size_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3058_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3059_ = lean_array_size(v___y_3035_);
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_3035_, v_sz_3059_, v___x_3060_, v___x_3058_);
lean_dec_ref(v___y_3035_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3073_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3073_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3073_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v_fst_3066_; lean_object* v_snd_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3071_; 
v_fst_3066_ = lean_ctor_get(v_a_3062_, 0);
lean_inc(v_fst_3066_);
v_snd_3067_ = lean_ctor_get(v_a_3062_, 1);
lean_inc(v_snd_3067_);
lean_dec(v_a_3062_);
v___x_3068_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3068_, 0, v_fst_3066_);
v___x_3069_ = lean_unbox(v_snd_3067_);
lean_dec(v_snd_3067_);
lean_ctor_set_uint8(v___x_3068_, sizeof(void*)*1, v___x_3069_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3068_);
v___x_3071_ = v___x_3064_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3068_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v_a_3074_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3061_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3061_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3082_; size_t v_sz_3083_; size_t v___x_3084_; lean_object* v___x_3085_; 
v_codeQualityEntries_3082_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3083_ = lean_array_size(v___y_3035_);
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_3035_, v_sz_3083_, v___x_3084_, v_codeQualityEntries_3082_);
lean_dec_ref(v___y_3035_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3094_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3094_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3094_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3090_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3086_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3090_);
v___x_3092_ = v___x_3088_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
v_a_3095_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3085_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3085_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
v___jp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3105_ = lean_array_get_size(v___y_3104_);
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = lean_nat_dec_eq(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
uint8_t v___x_3108_; 
v___x_3108_ = 1;
v___y_3035_ = v___y_3104_;
v___y_3036_ = v___x_3108_;
goto v___jp_3034_;
}
else
{
uint8_t v___x_3109_; 
v___x_3109_ = 0;
v___y_3035_ = v___y_3104_;
v___y_3036_ = v___x_3109_;
goto v___jp_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3115_, lean_object* v_linterOpts_3116_, lean_object* v_env_3117_, lean_object* v_mod_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3115_, v_linterOpts_3116_, v_env_3117_, v_mod_3118_);
lean_dec(v_mod_3118_);
lean_dec_ref(v_env_3117_);
lean_dec_ref(v_linterOpts_3116_);
lean_dec_ref(v_args_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3121_, lean_object* v_t_3122_, lean_object* v_k_3123_, lean_object* v_fallback_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3122_, v_k_3123_, v_fallback_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3126_, lean_object* v_t_3127_, lean_object* v_k_3128_, lean_object* v_fallback_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3126_, v_t_3127_, v_k_3128_, v_fallback_3129_);
lean_dec(v_fallback_3129_);
lean_dec(v_k_3128_);
lean_dec(v_t_3127_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3131_, lean_object* v_____r_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3136_, 0, v___y_3131_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3138_, lean_object* v_____r_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
uint8_t v___y_16371__boxed_3143_; lean_object* v_res_3144_; 
v___y_16371__boxed_3143_ = lean_unbox(v___y_3138_);
v_res_3144_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16371__boxed_3143_, v_____r_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3144_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
lean_ctor_set(v___x_3149_, 2, v___x_3148_);
lean_ctor_set(v___x_3149_, 3, v___x_3148_);
lean_ctor_set(v___x_3149_, 4, v___x_3147_);
lean_ctor_set(v___x_3149_, 5, v___x_3147_);
lean_ctor_set(v___x_3149_, 6, v___x_3147_);
lean_ctor_set(v___x_3149_, 7, v___x_3147_);
lean_ctor_set(v___x_3149_, 8, v___x_3147_);
lean_ctor_set(v___x_3149_, 9, v___x_3147_);
lean_ctor_set(v___x_3149_, 10, v___x_3147_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_unsigned_to_nat(32u);
v___x_3151_ = lean_mk_empty_array_with_capacity(v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
size_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3153_ = ((size_t)5ULL);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = lean_unsigned_to_nat(32u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
v___x_3157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3158_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v___x_3156_);
lean_ctor_set(v___x_3158_, 2, v___x_3154_);
lean_ctor_set(v___x_3158_, 3, v___x_3154_);
lean_ctor_set_usize(v___x_3158_, 4, v___x_3153_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3159_ = lean_box(1);
v___x_3160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v___x_3160_);
lean_ctor_set(v___x_3162_, 2, v___x_3159_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; lean_object* v_toCold_3168_; lean_object* v_env_3169_; lean_object* v_options_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3167_ = lean_st_ref_get(v___y_3165_);
v_toCold_3168_ = lean_ctor_get(v___y_3164_, 0);
v_env_3169_ = lean_ctor_get(v___x_3167_, 0);
lean_inc_ref(v_env_3169_);
lean_dec(v___x_3167_);
v_options_3170_ = lean_ctor_get(v_toCold_3168_, 2);
v___x_3171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3170_);
v___x_3173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3173_, 0, v_env_3169_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
lean_ctor_set(v___x_3173_, 3, v_options_3170_);
v___x_3174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v_msgData_3163_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_ref_3185_; lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3195_; 
v_ref_3185_ = lean_ctor_get(v___y_3182_, 2);
v___x_3186_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3181_, v___y_3182_, v___y_3183_);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_inc(v_ref_3185_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_ref_3185_);
lean_ctor_set(v___x_3191_, 1, v_a_3187_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3191_);
v___x_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3201_, lean_object* v_msg_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_toCold_3206_; lean_object* v_currRecDepth_3207_; lean_object* v_ref_3208_; uint16_t v_optionFlags_3209_; uint8_t v_suppressElabErrors_3210_; uint8_t v_isRecordingDeps_3211_; lean_object* v_ref_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_toCold_3206_ = lean_ctor_get(v___y_3203_, 0);
v_currRecDepth_3207_ = lean_ctor_get(v___y_3203_, 1);
v_ref_3208_ = lean_ctor_get(v___y_3203_, 2);
v_optionFlags_3209_ = lean_ctor_get_uint16(v___y_3203_, sizeof(void*)*3);
v_suppressElabErrors_3210_ = lean_ctor_get_uint8(v___y_3203_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3211_ = lean_ctor_get_uint8(v___y_3203_, sizeof(void*)*3 + 3);
v_ref_3212_ = l_Lean_replaceRef(v_ref_3201_, v_ref_3208_);
lean_inc(v_currRecDepth_3207_);
lean_inc_ref(v_toCold_3206_);
v___x_3213_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3213_, 0, v_toCold_3206_);
lean_ctor_set(v___x_3213_, 1, v_currRecDepth_3207_);
lean_ctor_set(v___x_3213_, 2, v_ref_3212_);
lean_ctor_set_uint16(v___x_3213_, sizeof(void*)*3, v_optionFlags_3209_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*3 + 2, v_suppressElabErrors_3210_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*3 + 3, v_isRecordingDeps_3211_);
v___x_3214_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3202_, v___x_3213_, v___y_3204_);
lean_dec_ref_known(v___x_3213_, 3);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3215_, lean_object* v_msg_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3215_, v_msg_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v_ref_3215_);
return v_res_3220_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3226_ = l_Lean_stringToMessageData(v___x_3225_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3229_ = l_Lean_stringToMessageData(v___x_3228_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3238_ = l_Lean_stringToMessageData(v___x_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3241_ = l_Lean_stringToMessageData(v___x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3242_, lean_object* v_declHint_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_env_3248_; uint8_t v___x_3249_; 
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_st_ref_get(v___y_3244_);
v_env_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_env_3248_);
lean_dec(v___x_3247_);
v___x_3249_ = l_Lean_Name_isAnonymous(v_declHint_3243_);
if (v___x_3249_ == 0)
{
uint8_t v_isExporting_3250_; 
v_isExporting_3250_ = lean_ctor_get_uint8(v_env_3248_, sizeof(void*)*8);
if (v_isExporting_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v_env_3248_);
lean_dec(v_declHint_3243_);
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_msg_3242_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; uint8_t v___x_3253_; 
lean_inc_ref(v_env_3248_);
v___x_3252_ = l_Lean_Environment_setExporting(v_env_3248_, v___x_3249_);
lean_inc(v_declHint_3243_);
lean_inc_ref(v___x_3252_);
v___x_3253_ = l_Lean_Environment_contains(v___x_3252_, v_declHint_3243_, v_isExporting_3250_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref(v___x_3252_);
lean_dec_ref(v_env_3248_);
lean_dec(v_declHint_3243_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_msg_3242_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v_c_3260_; lean_object* v___x_3261_; 
v___x_3255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3257_ = l_Lean_Options_empty;
v___x_3258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3252_);
lean_ctor_set(v___x_3258_, 1, v___x_3255_);
lean_ctor_set(v___x_3258_, 2, v___x_3256_);
lean_ctor_set(v___x_3258_, 3, v___x_3257_);
lean_inc(v_declHint_3243_);
v___x_3259_ = l_Lean_MessageData_ofConstName(v_declHint_3243_, v___x_3249_);
v_c_3260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3260_, 0, v___x_3258_);
lean_ctor_set(v_c_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3248_, v_declHint_3243_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec_ref(v_env_3248_);
lean_dec(v_declHint_3243_);
v___x_3262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
lean_ctor_set(v___x_3263_, 1, v_c_3260_);
v___x_3264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = l_Lean_MessageData_note(v___x_3265_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_msg_3242_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3303_; 
v_val_3269_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3271_ = v___x_3261_;
v_isShared_3272_ = v_isSharedCheck_3303_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_val_3269_);
lean_dec(v___x_3261_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3303_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_mod_3275_; uint8_t v___x_3276_; 
v___x_3273_ = l_Lean_Environment_header(v_env_3248_);
lean_dec_ref(v_env_3248_);
v___x_3274_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3273_);
v_mod_3275_ = lean_array_get(v___x_3246_, v___x_3274_, v_val_3269_);
lean_dec(v_val_3269_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = l_Lean_isPrivateName(v_declHint_3243_);
lean_dec(v_declHint_3243_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
lean_ctor_set(v___x_3278_, 1, v_c_3260_);
v___x_3279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_MessageData_ofName(v_mod_3275_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_MessageData_note(v___x_3284_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_msg_3242_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3286_);
v___x_3288_ = v___x_3271_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v_c_3260_);
v___x_3292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_MessageData_ofName(v_mod_3275_);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_MessageData_note(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_msg_3242_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3299_);
v___x_3301_ = v___x_3271_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
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
}
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v_env_3248_);
lean_dec(v_declHint_3243_);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_msg_3242_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3305_, lean_object* v_declHint_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3305_, v_declHint_3306_, v___y_3307_);
lean_dec(v___y_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3310_, lean_object* v_declHint_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3325_; 
v___x_3315_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3310_, v_declHint_3311_, v___y_3313_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3325_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3325_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3320_ = l_Lean_unknownIdentifierMessageTag;
v___x_3321_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v_a_3316_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3321_);
v___x_3323_ = v___x_3318_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3326_, lean_object* v_declHint_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3326_, v_declHint_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3332_, lean_object* v_msg_3333_, lean_object* v_declHint_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; lean_object* v_a_3339_; lean_object* v___x_3340_; 
v___x_3338_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3333_, v_declHint_3334_, v___y_3335_, v___y_3336_);
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3332_, v_a_3339_, v___y_3335_, v___y_3336_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3341_, lean_object* v_msg_3342_, lean_object* v_declHint_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3341_, v_msg_3342_, v_declHint_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v_ref_3341_);
return v_res_3347_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3352_ = l_Lean_stringToMessageData(v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3353_, lean_object* v_constName_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3358_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3359_ = 0;
lean_inc(v_constName_3354_);
v___x_3360_ = l_Lean_MessageData_ofConstName(v_constName_3354_, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3358_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3353_, v___x_3363_, v_constName_3354_, v___y_3355_, v___y_3356_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3365_, lean_object* v_constName_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3365_, v_constName_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v_ref_3365_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_ref_3375_; lean_object* v___x_3376_; 
v_ref_3375_ = lean_ctor_get(v___y_3372_, 2);
v___x_3376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3375_, v_constName_3371_, v___y_3372_, v___y_3373_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v_env_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; 
v___x_3386_ = lean_st_ref_get(v___y_3384_);
v_env_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc_ref(v_env_3387_);
lean_dec(v___x_3386_);
v___x_3388_ = 0;
lean_inc(v_constName_3382_);
v___x_3389_ = l_Lean_Environment_find_x3f(v_env_3387_, v_constName_3382_, v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3382_, v___y_3383_, v___y_3384_);
return v___x_3390_;
}
else
{
lean_object* v_val_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_constName_3382_);
v_val_3391_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3389_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_val_3391_);
lean_dec(v___x_3389_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set_tag(v___x_3393_, 0);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_val_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_box(0);
lean_inc(v_declName_3404_);
v___x_3409_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3409_, 0);
lean_dec(v_unused_3436_);
v___x_3411_ = v___x_3409_;
v_isShared_3412_ = v_isSharedCheck_3435_;
goto v_resetjp_3410_;
}
else
{
lean_dec(v___x_3409_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3435_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v_env_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_st_ref_get(v___y_3406_);
v_env_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc_ref(v_env_3414_);
lean_dec(v___x_3413_);
v___x_3415_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3414_, v_declName_3404_);
lean_dec(v_declName_3404_);
lean_dec_ref(v_env_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3416_);
v___x_3418_ = v___x_3411_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
else
{
lean_object* v_val_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3434_; 
v_val_3420_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3422_ = v___x_3415_;
v_isShared_3423_ = v_isSharedCheck_3434_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_val_3420_);
lean_dec(v___x_3415_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3434_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v_env_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3424_ = lean_st_ref_get(v___y_3406_);
v_env_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc_ref(v_env_3425_);
lean_dec(v___x_3424_);
v___x_3426_ = l_Lean_Environment_allImportedModuleNames(v_env_3425_);
lean_dec_ref(v_env_3425_);
v___x_3427_ = lean_array_get(v___x_3408_, v___x_3426_, v_val_3420_);
lean_dec(v_val_3420_);
lean_dec_ref(v___x_3426_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3427_);
v___x_3429_ = v___x_3422_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3431_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3429_);
v___x_3431_ = v___x_3411_;
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
}
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_declName_3404_);
v_a_3437_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3409_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3409_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
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
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3451_, lean_object* v_sp_3452_, lean_object* v___x_3453_, lean_object* v_as_3454_, size_t v_sz_3455_, size_t v_i_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_a_3462_; uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3456_, v_sz_3455_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_b_3457_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v_fst_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3597_; 
v_a_3468_ = lean_array_uget(v_as_3454_, v_i_3456_);
v_fst_3469_ = lean_ctor_get(v_a_3468_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3468_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v_a_3468_, 1);
lean_dec(v_unused_3598_);
v___x_3471_ = v_a_3468_;
v_isShared_3472_ = v_isSharedCheck_3597_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_fst_3469_);
lean_dec(v_a_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3597_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_fst_3473_; lean_object* v_snd_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3596_; 
v_fst_3473_ = lean_ctor_get(v_b_3457_, 0);
v_snd_3474_ = lean_ctor_get(v_b_3457_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_b_3457_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3476_ = v_b_3457_;
v_isShared_3477_ = v_isSharedCheck_3596_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_snd_3474_);
lean_inc(v_fst_3473_);
lean_dec(v_b_3457_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3596_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; 
lean_inc(v_fst_3469_);
v___x_3478_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3469_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
if (lean_obj_tag(v_a_3479_) == 0)
{
lean_object* v_optName_3480_; lean_object* v_ref_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec(v_snd_3474_);
v_optName_3480_ = lean_ctor_get(v_fst_3451_, 1);
v_ref_3481_ = lean_ctor_get(v___y_3458_, 2);
v___x_3482_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3469_, v___x_3466_);
v___x_3483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3484_ = lean_string_append(v___x_3483_, v___x_3482_);
lean_dec_ref(v___x_3482_);
v___x_3485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
lean_inc(v_optName_3480_);
v___x_3487_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3480_, v___x_3466_);
v___x_3488_ = lean_string_append(v___x_3486_, v___x_3487_);
lean_dec_ref(v___x_3487_);
v___x_3489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3490_ = lean_string_append(v___x_3488_, v___x_3489_);
v___x_3491_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3490_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
lean_dec_ref_known(v___x_3491_, 1);
lean_del_object(v___x_3471_);
v___x_3492_ = lean_box(v___x_3466_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v___x_3492_);
v___x_3494_ = v___x_3476_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_fst_3473_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
v_a_3462_ = v___x_3494_;
goto v___jp_3461_;
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3509_; 
lean_del_object(v___x_3476_);
lean_dec(v_fst_3473_);
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v_a_3496_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3498_ = v___x_3491_;
v_isShared_3499_ = v_isSharedCheck_3509_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3491_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3509_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3500_ = lean_io_error_to_string(v_a_3496_);
v___x_3501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
v___x_3502_ = l_Lean_MessageData_ofFormat(v___x_3501_);
lean_inc(v_ref_3481_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3502_);
lean_ctor_set(v___x_3471_, 0, v_ref_3481_);
v___x_3504_ = v___x_3471_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_ref_3481_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3504_);
v___x_3506_ = v___x_3498_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3587_; 
v_val_3510_ = lean_ctor_get(v_a_3479_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_a_3479_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3512_ = v_a_3479_;
v_isShared_3513_ = v_isSharedCheck_3587_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v_a_3479_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3587_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3469_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___y_3517_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
if (lean_obj_tag(v_a_3515_) == 0)
{
lean_inc(v___x_3453_);
v___y_3517_ = v___x_3453_;
goto v___jp_3516_;
}
else
{
lean_object* v_val_3578_; 
v_val_3578_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v_a_3515_, 1);
v___y_3517_ = v_val_3578_;
goto v___jp_3516_;
}
v___jp_3516_:
{
lean_object* v_ref_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_ref_3518_ = lean_ctor_get(v___y_3458_, 2);
v___x_3519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v___y_3517_);
lean_inc(v_sp_3452_);
v___x_3520_ = l_Lean_SearchPath_findWithExt(v_sp_3452_, v___x_3519_, v___y_3517_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
if (lean_obj_tag(v_a_3521_) == 0)
{
lean_object* v_optName_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec(v_val_3510_);
lean_dec(v_snd_3474_);
v_optName_3522_ = lean_ctor_get(v_fst_3451_, 1);
v___x_3523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
v___x_3524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3517_, v___x_3466_);
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
lean_inc(v_optName_3522_);
v___x_3528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3522_, v___x_3466_);
v___x_3529_ = lean_string_append(v___x_3527_, v___x_3528_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3531_ = lean_string_append(v___x_3529_, v___x_3530_);
v___x_3532_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
lean_dec_ref_known(v___x_3532_, 1);
lean_del_object(v___x_3512_);
lean_del_object(v___x_3471_);
v___x_3533_ = lean_box(v___x_3466_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v___x_3533_);
v___x_3535_ = v___x_3476_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_fst_3473_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
v_a_3462_ = v___x_3535_;
goto v___jp_3461_;
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3552_; 
lean_del_object(v___x_3476_);
lean_dec(v_fst_3473_);
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v_a_3537_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3539_ = v___x_3532_;
v_isShared_3540_ = v_isSharedCheck_3552_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3532_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3552_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = lean_io_error_to_string(v_a_3537_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 3);
lean_ctor_set(v___x_3512_, 0, v___x_3541_);
v___x_3543_ = v___x_3512_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = l_Lean_MessageData_ofFormat(v___x_3543_);
lean_inc(v_ref_3518_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3544_);
lean_ctor_set(v___x_3471_, 0, v_ref_3518_);
v___x_3546_ = v___x_3471_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_ref_3518_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3546_);
v___x_3548_ = v___x_3539_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
}
else
{
lean_object* v_range_3553_; lean_object* v_val_3554_; lean_object* v_pos_3555_; lean_object* v_optName_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
lean_dec(v___y_3517_);
lean_del_object(v___x_3512_);
lean_del_object(v___x_3471_);
v_range_3553_ = lean_ctor_get(v_val_3510_, 0);
lean_inc_ref(v_range_3553_);
lean_dec(v_val_3510_);
v_val_3554_ = lean_ctor_get(v_a_3521_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_a_3521_, 1);
v_pos_3555_ = lean_ctor_get(v_range_3553_, 0);
lean_inc_ref(v_pos_3555_);
lean_dec_ref(v_range_3553_);
v_optName_3556_ = lean_ctor_get(v_fst_3451_, 1);
lean_inc(v_optName_3556_);
v___x_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3557_, 0, v_val_3554_);
lean_ctor_set(v___x_3557_, 1, v_pos_3555_);
lean_ctor_set(v___x_3557_, 2, v_optName_3556_);
v___x_3558_ = lean_array_push(v_fst_3473_, v___x_3557_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3558_);
v___x_3560_ = v___x_3476_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_snd_3474_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
v_a_3462_ = v___x_3560_;
goto v___jp_3461_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v___y_3517_);
lean_dec(v_val_3510_);
lean_del_object(v___x_3476_);
lean_dec(v_snd_3474_);
lean_dec(v_fst_3473_);
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v_a_3562_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3564_ = v___x_3520_;
v_isShared_3565_ = v_isSharedCheck_3577_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3520_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3577_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = lean_io_error_to_string(v_a_3562_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 3);
lean_ctor_set(v___x_3512_, 0, v___x_3566_);
v___x_3568_ = v___x_3512_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = l_Lean_MessageData_ofFormat(v___x_3568_);
lean_inc(v_ref_3518_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3569_);
lean_ctor_set(v___x_3471_, 0, v_ref_3518_);
v___x_3571_ = v___x_3471_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_ref_3518_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3571_);
v___x_3573_ = v___x_3564_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_del_object(v___x_3476_);
lean_dec(v_snd_3474_);
lean_dec(v_fst_3473_);
lean_del_object(v___x_3471_);
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v_a_3579_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3514_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3514_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
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
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_del_object(v___x_3476_);
lean_dec(v_snd_3474_);
lean_dec(v_fst_3473_);
lean_del_object(v___x_3471_);
lean_dec(v_fst_3469_);
lean_dec(v___x_3453_);
lean_dec(v_sp_3452_);
lean_dec_ref(v_fst_3451_);
v_a_3588_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3478_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3478_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
v___jp_3461_:
{
size_t v___x_3463_; size_t v___x_3464_; 
v___x_3463_ = ((size_t)1ULL);
v___x_3464_ = lean_usize_add(v_i_3456_, v___x_3463_);
v_i_3456_ = v___x_3464_;
v_b_3457_ = v_a_3462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3599_, lean_object* v_sp_3600_, lean_object* v___x_3601_, lean_object* v_as_3602_, lean_object* v_sz_3603_, lean_object* v_i_3604_, lean_object* v_b_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
size_t v_sz_boxed_3609_; size_t v_i_boxed_3610_; lean_object* v_res_3611_; 
v_sz_boxed_3609_ = lean_unbox_usize(v_sz_3603_);
lean_dec(v_sz_3603_);
v_i_boxed_3610_ = lean_unbox_usize(v_i_3604_);
lean_dec(v_i_3604_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3599_, v_sp_3600_, v___x_3601_, v_as_3602_, v_sz_boxed_3609_, v_i_boxed_3610_, v_b_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_as_3602_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
if (lean_obj_tag(v_x_3613_) == 0)
{
return v_x_3612_;
}
else
{
lean_object* v_key_3614_; lean_object* v_value_3615_; lean_object* v_tail_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_key_3614_ = lean_ctor_get(v_x_3613_, 0);
v_value_3615_ = lean_ctor_get(v_x_3613_, 1);
v_tail_3616_ = lean_ctor_get(v_x_3613_, 2);
lean_inc(v_value_3615_);
lean_inc(v_key_3614_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v_key_3614_);
lean_ctor_set(v___x_3617_, 1, v_value_3615_);
v___x_3618_ = lean_array_push(v_x_3612_, v___x_3617_);
v_x_3612_ = v___x_3618_;
v_x_3613_ = v_tail_3616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3620_, v_x_3621_);
lean_dec(v_x_3621_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3623_, size_t v_i_3624_, size_t v_stop_3625_, lean_object* v_b_3626_){
_start:
{
uint8_t v___x_3627_; 
v___x_3627_ = lean_usize_dec_eq(v_i_3624_, v_stop_3625_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; size_t v___x_3630_; size_t v___x_3631_; 
v___x_3628_ = lean_array_uget_borrowed(v_as_3623_, v_i_3624_);
v___x_3629_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3626_, v___x_3628_);
v___x_3630_ = ((size_t)1ULL);
v___x_3631_ = lean_usize_add(v_i_3624_, v___x_3630_);
v_i_3624_ = v___x_3631_;
v_b_3626_ = v___x_3629_;
goto _start;
}
else
{
return v_b_3626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3633_, lean_object* v_i_3634_, lean_object* v_stop_3635_, lean_object* v_b_3636_){
_start:
{
size_t v_i_boxed_3637_; size_t v_stop_boxed_3638_; lean_object* v_res_3639_; 
v_i_boxed_3637_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_stop_boxed_3638_ = lean_unbox_usize(v_stop_3635_);
lean_dec(v_stop_3635_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3633_, v_i_boxed_3637_, v_stop_boxed_3638_, v_b_3636_);
lean_dec_ref(v_as_3633_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3640_, lean_object* v___x_3641_, lean_object* v_as_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_usize_dec_lt(v_i_3644_, v_sz_3643_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec(v___x_3641_);
lean_dec(v_sp_3640_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_b_3645_);
return v___x_3650_;
}
else
{
lean_object* v_a_3651_; lean_object* v_fst_3652_; lean_object* v_snd_3653_; lean_object* v_fst_3654_; lean_object* v_snd_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3689_; 
v_a_3651_ = lean_array_uget_borrowed(v_as_3642_, v_i_3644_);
v_fst_3652_ = lean_ctor_get(v_a_3651_, 0);
v_snd_3653_ = lean_ctor_get(v_a_3651_, 1);
v_fst_3654_ = lean_ctor_get(v_b_3645_, 0);
v_snd_3655_ = lean_ctor_get(v_b_3645_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_b_3645_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3657_ = v_b_3645_;
v_isShared_3658_ = v_isSharedCheck_3689_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_snd_3655_);
lean_inc(v_fst_3654_);
lean_dec(v_b_3645_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3689_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___y_3660_; lean_object* v_size_3680_; lean_object* v_buckets_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_size_3680_ = lean_ctor_get(v_snd_3653_, 0);
v_buckets_3681_ = lean_ctor_get(v_snd_3653_, 1);
v___x_3682_ = lean_mk_empty_array_with_capacity(v_size_3680_);
v___x_3683_ = lean_unsigned_to_nat(0u);
v___x_3684_ = lean_array_get_size(v_buckets_3681_);
v___x_3685_ = lean_nat_dec_lt(v___x_3683_, v___x_3684_);
if (v___x_3685_ == 0)
{
v___y_3660_ = v___x_3682_;
goto v___jp_3659_;
}
else
{
size_t v___x_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = ((size_t)0ULL);
v___x_3687_ = lean_usize_of_nat(v___x_3684_);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3681_, v___x_3686_, v___x_3687_, v___x_3682_);
v___y_3660_ = v___x_3688_;
goto v___jp_3659_;
}
v___jp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3658_ == 0)
{
v___x_3662_ = v___x_3657_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_fst_3654_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_snd_3655_);
v___x_3662_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
size_t v_sz_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v_sz_3663_ = lean_array_size(v___y_3660_);
v___x_3664_ = ((size_t)0ULL);
lean_inc(v___x_3641_);
lean_inc(v_sp_3640_);
lean_inc(v_fst_3652_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3652_, v_sp_3640_, v___x_3641_, v___y_3660_, v_sz_3663_, v___x_3664_, v___x_3662_, v___y_3646_, v___y_3647_);
lean_dec_ref(v___y_3660_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v_fst_3667_; lean_object* v_snd_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3678_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v_fst_3667_ = lean_ctor_get(v_a_3666_, 0);
v_snd_3668_ = lean_ctor_get(v_a_3666_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3666_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3670_ = v_a_3666_;
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_snd_3668_);
lean_inc(v_fst_3667_);
lean_dec(v_a_3666_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_fst_3667_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_snd_3668_);
v___x_3673_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
size_t v___x_3674_; size_t v___x_3675_; 
v___x_3674_ = ((size_t)1ULL);
v___x_3675_ = lean_usize_add(v_i_3644_, v___x_3674_);
v_i_3644_ = v___x_3675_;
v_b_3645_ = v___x_3673_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3641_);
lean_dec(v_sp_3640_);
return v___x_3665_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3690_, lean_object* v___x_3691_, lean_object* v_as_3692_, lean_object* v_sz_3693_, lean_object* v_i_3694_, lean_object* v_b_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
size_t v_sz_boxed_3699_; size_t v_i_boxed_3700_; lean_object* v_res_3701_; 
v_sz_boxed_3699_ = lean_unbox_usize(v_sz_3693_);
lean_dec(v_sz_3693_);
v_i_boxed_3700_ = lean_unbox_usize(v_i_3694_);
lean_dec(v_i_3694_);
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3690_, v___x_3691_, v_as_3692_, v_sz_boxed_3699_, v_i_boxed_3700_, v_b_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v_as_3692_);
return v_res_3701_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3702_, lean_object* v_as_3703_, size_t v_i_3704_, size_t v_stop_3705_){
_start:
{
uint8_t v___x_3706_; 
v___x_3706_ = lean_usize_dec_eq(v_i_3704_, v_stop_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v_snd_3708_; lean_object* v_size_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3707_ = lean_array_uget_borrowed(v_as_3703_, v_i_3704_);
v_snd_3708_ = lean_ctor_get(v___x_3707_, 1);
v_size_3709_ = lean_ctor_get(v_snd_3708_, 0);
v___x_3710_ = 1;
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_nat_dec_eq(v_size_3709_, v___x_3711_);
if (v___x_3712_ == 0)
{
return v___x_3710_;
}
else
{
if (v___y_3702_ == 0)
{
size_t v___x_3713_; size_t v___x_3714_; 
v___x_3713_ = ((size_t)1ULL);
v___x_3714_ = lean_usize_add(v_i_3704_, v___x_3713_);
v_i_3704_ = v___x_3714_;
goto _start;
}
else
{
return v___x_3710_;
}
}
}
else
{
uint8_t v___x_3716_; 
v___x_3716_ = 0;
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3717_, lean_object* v_as_3718_, lean_object* v_i_3719_, lean_object* v_stop_3720_){
_start:
{
uint8_t v___y_17342__boxed_3721_; size_t v_i_boxed_3722_; size_t v_stop_boxed_3723_; uint8_t v_res_3724_; lean_object* v_r_3725_; 
v___y_17342__boxed_3721_ = lean_unbox(v___y_3717_);
v_i_boxed_3722_ = lean_unbox_usize(v_i_3719_);
lean_dec(v_i_3719_);
v_stop_boxed_3723_ = lean_unbox_usize(v_stop_3720_);
lean_dec(v_stop_3720_);
v_res_3724_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_17342__boxed_3721_, v_as_3718_, v_i_boxed_3722_, v_stop_boxed_3723_);
lean_dec_ref(v_as_3718_);
v_r_3725_ = lean_box(v_res_3724_);
return v_r_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3726_, lean_object* v_v_3727_, lean_object* v_t_3728_){
_start:
{
lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; 
if (lean_obj_tag(v_t_3728_) == 0)
{
lean_object* v_size_3743_; lean_object* v_k_3744_; lean_object* v_v_3745_; lean_object* v_l_3746_; lean_object* v_r_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_4007_; 
v_size_3743_ = lean_ctor_get(v_t_3728_, 0);
v_k_3744_ = lean_ctor_get(v_t_3728_, 1);
v_v_3745_ = lean_ctor_get(v_t_3728_, 2);
v_l_3746_ = lean_ctor_get(v_t_3728_, 3);
v_r_3747_ = lean_ctor_get(v_t_3728_, 4);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_t_3728_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3749_ = v_t_3728_;
v_isShared_3750_ = v_isSharedCheck_4007_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_r_3747_);
lean_inc(v_l_3746_);
lean_inc(v_v_3745_);
lean_inc(v_k_3744_);
lean_inc(v_size_3743_);
lean_dec(v_t_3728_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_4007_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; uint8_t v___y_3801_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v_fst_4003_; lean_object* v_snd_4004_; uint8_t v___x_4005_; 
v_fst_4001_ = lean_ctor_get(v_k_3726_, 0);
v_snd_4002_ = lean_ctor_get(v_k_3726_, 1);
v_fst_4003_ = lean_ctor_get(v_k_3744_, 0);
v_snd_4004_ = lean_ctor_get(v_k_3744_, 1);
v___x_4005_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4001_, v_fst_4003_);
if (v___x_4005_ == 1)
{
uint8_t v___x_4006_; 
v___x_4006_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4002_, v_snd_4004_);
v___y_3801_ = v___x_4006_;
goto v___jp_3800_;
}
else
{
v___y_3801_ = v___x_4005_;
goto v___jp_3800_;
}
v___jp_3751_:
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
v___x_3759_ = lean_nat_add(v___y_3752_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec(v___y_3752_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 3, v___y_3755_);
lean_ctor_set(v___x_3749_, 0, v___x_3759_);
v___x_3761_ = v___x_3749_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v___y_3755_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_r_3747_);
v___x_3761_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3762_, 0, v___y_3756_);
lean_ctor_set(v___x_3762_, 1, v___y_3753_);
lean_ctor_set(v___x_3762_, 2, v___y_3757_);
lean_ctor_set(v___x_3762_, 3, v___y_3754_);
lean_ctor_set(v___x_3762_, 4, v___x_3761_);
return v___x_3762_;
}
}
v___jp_3764_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3777_ = lean_nat_add(v___y_3774_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec(v___y_3774_);
v___x_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___y_3772_);
lean_ctor_set(v___x_3778_, 2, v___y_3767_);
lean_ctor_set(v___x_3778_, 3, v___y_3765_);
lean_ctor_set(v___x_3778_, 4, v___y_3769_);
v___x_3779_ = lean_nat_add(v___y_3771_, v___y_3768_);
lean_dec(v___y_3768_);
if (lean_obj_tag(v___y_3770_) == 0)
{
lean_object* v_size_3780_; 
v_size_3780_ = lean_ctor_get(v___y_3770_, 0);
lean_inc(v_size_3780_);
v___y_3752_ = v___x_3779_;
v___y_3753_ = v___y_3766_;
v___y_3754_ = v___x_3778_;
v___y_3755_ = v___y_3770_;
v___y_3756_ = v___y_3773_;
v___y_3757_ = v___y_3775_;
v___y_3758_ = v_size_3780_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_unsigned_to_nat(0u);
v___y_3752_ = v___x_3779_;
v___y_3753_ = v___y_3766_;
v___y_3754_ = v___x_3778_;
v___y_3755_ = v___y_3770_;
v___y_3756_ = v___y_3773_;
v___y_3757_ = v___y_3775_;
v___y_3758_ = v___x_3781_;
goto v___jp_3751_;
}
}
v___jp_3782_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_nat_add(v___y_3783_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec(v___y_3783_);
v___x_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v_k_3744_);
lean_ctor_set(v___x_3796_, 2, v_v_3745_);
lean_ctor_set(v___x_3796_, 3, v_l_3746_);
lean_ctor_set(v___x_3796_, 4, v___y_3785_);
v___x_3797_ = lean_nat_add(v___y_3788_, v___y_3784_);
lean_dec(v___y_3784_);
if (lean_obj_tag(v___y_3789_) == 0)
{
lean_object* v_size_3798_; 
v_size_3798_ = lean_ctor_get(v___y_3789_, 0);
lean_inc(v_size_3798_);
v___y_3730_ = v___y_3787_;
v___y_3731_ = v___y_3786_;
v___y_3732_ = v___x_3796_;
v___y_3733_ = v___y_3789_;
v___y_3734_ = v___y_3791_;
v___y_3735_ = v___y_3790_;
v___y_3736_ = v___y_3792_;
v___y_3737_ = v___x_3797_;
v___y_3738_ = v___y_3793_;
v___y_3739_ = v_size_3798_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
v___y_3730_ = v___y_3787_;
v___y_3731_ = v___y_3786_;
v___y_3732_ = v___x_3796_;
v___y_3733_ = v___y_3789_;
v___y_3734_ = v___y_3791_;
v___y_3735_ = v___y_3790_;
v___y_3736_ = v___y_3792_;
v___y_3737_ = v___x_3797_;
v___y_3738_ = v___y_3793_;
v___y_3739_ = v___x_3799_;
goto v___jp_3729_;
}
}
v___jp_3800_:
{
switch(v___y_3801_)
{
case 0:
{
lean_object* v_impl_3802_; lean_object* v___x_3803_; 
lean_dec(v_size_3743_);
v_impl_3802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3726_, v_v_3727_, v_l_3746_);
v___x_3803_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3747_) == 0)
{
lean_object* v_size_3804_; lean_object* v_size_3805_; lean_object* v_k_3806_; lean_object* v_v_3807_; lean_object* v_l_3808_; lean_object* v_r_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v_size_3804_ = lean_ctor_get(v_r_3747_, 0);
v_size_3805_ = lean_ctor_get(v_impl_3802_, 0);
v_k_3806_ = lean_ctor_get(v_impl_3802_, 1);
v_v_3807_ = lean_ctor_get(v_impl_3802_, 2);
v_l_3808_ = lean_ctor_get(v_impl_3802_, 3);
v_r_3809_ = lean_ctor_get(v_impl_3802_, 4);
v___x_3810_ = lean_unsigned_to_nat(3u);
v___x_3811_ = lean_nat_mul(v___x_3810_, v_size_3804_);
v___x_3812_ = lean_nat_dec_lt(v___x_3811_, v_size_3805_);
lean_dec(v___x_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_del_object(v___x_3749_);
v___x_3813_ = lean_nat_add(v___x_3803_, v_size_3805_);
v___x_3814_ = lean_nat_add(v___x_3813_, v_size_3804_);
lean_dec(v___x_3813_);
v___x_3815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v_k_3744_);
lean_ctor_set(v___x_3815_, 2, v_v_3745_);
lean_ctor_set(v___x_3815_, 3, v_impl_3802_);
lean_ctor_set(v___x_3815_, 4, v_r_3747_);
return v___x_3815_;
}
else
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3852_; 
lean_inc(v_r_3809_);
lean_inc(v_l_3808_);
lean_inc(v_v_3807_);
lean_inc(v_k_3806_);
lean_inc(v_size_3805_);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_impl_3802_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; 
v_unused_3853_ = lean_ctor_get(v_impl_3802_, 4);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_impl_3802_, 3);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_impl_3802_, 2);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_impl_3802_, 1);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_impl_3802_, 0);
lean_dec(v_unused_3857_);
v___x_3817_ = v_impl_3802_;
v_isShared_3818_ = v_isSharedCheck_3852_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v_impl_3802_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3852_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v_size_3819_; lean_object* v_size_3820_; lean_object* v_k_3821_; lean_object* v_v_3822_; lean_object* v_l_3823_; lean_object* v_r_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_size_3819_ = lean_ctor_get(v_l_3808_, 0);
v_size_3820_ = lean_ctor_get(v_r_3809_, 0);
v_k_3821_ = lean_ctor_get(v_r_3809_, 1);
v_v_3822_ = lean_ctor_get(v_r_3809_, 2);
v_l_3823_ = lean_ctor_get(v_r_3809_, 3);
v_r_3824_ = lean_ctor_get(v_r_3809_, 4);
v___x_3825_ = lean_unsigned_to_nat(2u);
v___x_3826_ = lean_nat_mul(v___x_3825_, v_size_3819_);
v___x_3827_ = lean_nat_dec_lt(v_size_3820_, v___x_3826_);
lean_dec(v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_inc(v_r_3824_);
lean_inc(v_l_3823_);
lean_inc(v_v_3822_);
lean_inc(v_k_3821_);
lean_del_object(v___x_3817_);
lean_dec(v_r_3809_);
v___x_3828_ = lean_nat_add(v___x_3803_, v_size_3805_);
lean_dec(v_size_3805_);
v___x_3829_ = lean_nat_add(v___x_3828_, v_size_3804_);
lean_dec(v___x_3828_);
v___x_3830_ = lean_nat_add(v___x_3803_, v_size_3819_);
if (lean_obj_tag(v_l_3823_) == 0)
{
lean_object* v_size_3831_; 
v_size_3831_ = lean_ctor_get(v_l_3823_, 0);
lean_inc(v_size_3831_);
lean_inc(v_size_3804_);
v___y_3765_ = v_l_3808_;
v___y_3766_ = v_k_3821_;
v___y_3767_ = v_v_3807_;
v___y_3768_ = v_size_3804_;
v___y_3769_ = v_l_3823_;
v___y_3770_ = v_r_3824_;
v___y_3771_ = v___x_3803_;
v___y_3772_ = v_k_3806_;
v___y_3773_ = v___x_3829_;
v___y_3774_ = v___x_3830_;
v___y_3775_ = v_v_3822_;
v___y_3776_ = v_size_3831_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3804_);
v___y_3765_ = v_l_3808_;
v___y_3766_ = v_k_3821_;
v___y_3767_ = v_v_3807_;
v___y_3768_ = v_size_3804_;
v___y_3769_ = v_l_3823_;
v___y_3770_ = v_r_3824_;
v___y_3771_ = v___x_3803_;
v___y_3772_ = v_k_3806_;
v___y_3773_ = v___x_3829_;
v___y_3774_ = v___x_3830_;
v___y_3775_ = v_v_3822_;
v___y_3776_ = v___x_3832_;
goto v___jp_3764_;
}
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_del_object(v___x_3749_);
v___x_3833_ = lean_nat_add(v___x_3803_, v_size_3805_);
lean_dec(v_size_3805_);
v___x_3834_ = lean_nat_add(v___x_3833_, v_size_3804_);
lean_dec(v___x_3833_);
v___x_3835_ = lean_nat_add(v___x_3803_, v_size_3804_);
v___x_3836_ = lean_nat_add(v___x_3835_, v_size_3820_);
lean_dec(v___x_3835_);
lean_inc_ref(v_r_3747_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 4, v_r_3747_);
lean_ctor_set(v___x_3817_, 3, v_r_3809_);
lean_ctor_set(v___x_3817_, 2, v_v_3745_);
lean_ctor_set(v___x_3817_, 1, v_k_3744_);
lean_ctor_set(v___x_3817_, 0, v___x_3836_);
v___x_3838_ = v___x_3817_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3851_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3851_, 3, v_r_3809_);
lean_ctor_set(v_reuseFailAlloc_3851_, 4, v_r_3747_);
v___x_3838_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
v_isSharedCheck_3845_ = !lean_is_exclusive(v_r_3747_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; lean_object* v_unused_3847_; lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3846_ = lean_ctor_get(v_r_3747_, 4);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_r_3747_, 3);
lean_dec(v_unused_3847_);
v_unused_3848_ = lean_ctor_get(v_r_3747_, 2);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_r_3747_, 1);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_r_3747_, 0);
lean_dec(v_unused_3850_);
v___x_3840_ = v_r_3747_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_dec(v_r_3747_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 4, v___x_3838_);
lean_ctor_set(v___x_3840_, 3, v_l_3808_);
lean_ctor_set(v___x_3840_, 2, v_v_3807_);
lean_ctor_set(v___x_3840_, 1, v_k_3806_);
lean_ctor_set(v___x_3840_, 0, v___x_3834_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_k_3806_);
lean_ctor_set(v_reuseFailAlloc_3844_, 2, v_v_3807_);
lean_ctor_set(v_reuseFailAlloc_3844_, 3, v_l_3808_);
lean_ctor_set(v_reuseFailAlloc_3844_, 4, v___x_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3858_; 
lean_del_object(v___x_3749_);
v_l_3858_ = lean_ctor_get(v_impl_3802_, 3);
if (lean_obj_tag(v_l_3858_) == 0)
{
lean_object* v_r_3859_; lean_object* v_k_3860_; lean_object* v_v_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3870_; 
lean_inc_ref(v_l_3858_);
v_r_3859_ = lean_ctor_get(v_impl_3802_, 4);
v_k_3860_ = lean_ctor_get(v_impl_3802_, 1);
v_v_3861_ = lean_ctor_get(v_impl_3802_, 2);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_impl_3802_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3871_ = lean_ctor_get(v_impl_3802_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_impl_3802_, 0);
lean_dec(v_unused_3872_);
v___x_3863_ = v_impl_3802_;
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_r_3859_);
lean_inc(v_v_3861_);
lean_inc(v_k_3860_);
lean_dec(v_impl_3802_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3859_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 3, v_r_3859_);
lean_ctor_set(v___x_3863_, 2, v_v_3745_);
lean_ctor_set(v___x_3863_, 1, v_k_3744_);
lean_ctor_set(v___x_3863_, 0, v___x_3803_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_r_3859_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v_r_3859_);
v___x_3867_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3865_);
lean_ctor_set(v___x_3868_, 1, v_k_3860_);
lean_ctor_set(v___x_3868_, 2, v_v_3861_);
lean_ctor_set(v___x_3868_, 3, v_l_3858_);
lean_ctor_set(v___x_3868_, 4, v___x_3867_);
return v___x_3868_;
}
}
}
else
{
lean_object* v_r_3873_; 
v_r_3873_ = lean_ctor_get(v_impl_3802_, 4);
lean_inc(v_r_3873_);
if (lean_obj_tag(v_r_3873_) == 0)
{
lean_object* v_k_3874_; lean_object* v_v_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3896_; 
lean_inc(v_l_3858_);
v_k_3874_ = lean_ctor_get(v_impl_3802_, 1);
v_v_3875_ = lean_ctor_get(v_impl_3802_, 2);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_impl_3802_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3897_ = lean_ctor_get(v_impl_3802_, 4);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3802_, 3);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_impl_3802_, 0);
lean_dec(v_unused_3899_);
v___x_3877_ = v_impl_3802_;
v_isShared_3878_ = v_isSharedCheck_3896_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_v_3875_);
lean_inc(v_k_3874_);
lean_dec(v_impl_3802_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3896_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_k_3879_; lean_object* v_v_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3892_; 
v_k_3879_ = lean_ctor_get(v_r_3873_, 1);
v_v_3880_ = lean_ctor_get(v_r_3873_, 2);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_r_3873_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3893_ = lean_ctor_get(v_r_3873_, 4);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_r_3873_, 3);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_r_3873_, 0);
lean_dec(v_unused_3895_);
v___x_3882_ = v_r_3873_;
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_v_3880_);
lean_inc(v_k_3879_);
lean_dec(v_r_3873_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = lean_unsigned_to_nat(3u);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 4, v_l_3858_);
lean_ctor_set(v___x_3882_, 3, v_l_3858_);
lean_ctor_set(v___x_3882_, 2, v_v_3875_);
lean_ctor_set(v___x_3882_, 1, v_k_3874_);
lean_ctor_set(v___x_3882_, 0, v___x_3803_);
v___x_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_k_3874_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_v_3875_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_l_3858_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v_l_3858_);
v___x_3886_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 4, v_l_3858_);
lean_ctor_set(v___x_3877_, 2, v_v_3745_);
lean_ctor_set(v___x_3877_, 1, v_k_3744_);
lean_ctor_set(v___x_3877_, 0, v___x_3803_);
v___x_3888_ = v___x_3877_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v_l_3858_);
lean_ctor_set(v_reuseFailAlloc_3890_, 4, v_l_3858_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3884_);
lean_ctor_set(v___x_3889_, 1, v_k_3879_);
lean_ctor_set(v___x_3889_, 2, v_v_3880_);
lean_ctor_set(v___x_3889_, 3, v___x_3886_);
lean_ctor_set(v___x_3889_, 4, v___x_3888_);
return v___x_3889_;
}
}
}
}
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_unsigned_to_nat(2u);
v___x_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v_k_3744_);
lean_ctor_set(v___x_3901_, 2, v_v_3745_);
lean_ctor_set(v___x_3901_, 3, v_impl_3802_);
lean_ctor_set(v___x_3901_, 4, v_r_3873_);
return v___x_3901_;
}
}
}
}
case 1:
{
lean_object* v___x_3902_; 
lean_del_object(v___x_3749_);
lean_dec(v_v_3745_);
lean_dec(v_k_3744_);
v___x_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3902_, 0, v_size_3743_);
lean_ctor_set(v___x_3902_, 1, v_k_3726_);
lean_ctor_set(v___x_3902_, 2, v_v_3727_);
lean_ctor_set(v___x_3902_, 3, v_l_3746_);
lean_ctor_set(v___x_3902_, 4, v_r_3747_);
return v___x_3902_;
}
default: 
{
lean_object* v_impl_3903_; lean_object* v___x_3904_; 
lean_del_object(v___x_3749_);
lean_dec(v_size_3743_);
v_impl_3903_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3726_, v_v_3727_, v_r_3747_);
v___x_3904_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3746_) == 0)
{
lean_object* v_size_3905_; lean_object* v_size_3906_; lean_object* v_k_3907_; lean_object* v_v_3908_; lean_object* v_l_3909_; lean_object* v_r_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v_size_3905_ = lean_ctor_get(v_l_3746_, 0);
v_size_3906_ = lean_ctor_get(v_impl_3903_, 0);
v_k_3907_ = lean_ctor_get(v_impl_3903_, 1);
v_v_3908_ = lean_ctor_get(v_impl_3903_, 2);
v_l_3909_ = lean_ctor_get(v_impl_3903_, 3);
v_r_3910_ = lean_ctor_get(v_impl_3903_, 4);
v___x_3911_ = lean_unsigned_to_nat(3u);
v___x_3912_ = lean_nat_mul(v___x_3911_, v_size_3905_);
v___x_3913_ = lean_nat_dec_lt(v___x_3912_, v_size_3906_);
lean_dec(v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3914_ = lean_nat_add(v___x_3904_, v_size_3905_);
v___x_3915_ = lean_nat_add(v___x_3914_, v_size_3906_);
lean_dec(v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v_k_3744_);
lean_ctor_set(v___x_3916_, 2, v_v_3745_);
lean_ctor_set(v___x_3916_, 3, v_l_3746_);
lean_ctor_set(v___x_3916_, 4, v_impl_3903_);
return v___x_3916_;
}
else
{
lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3951_; 
lean_inc(v_r_3910_);
lean_inc(v_l_3909_);
lean_inc(v_v_3908_);
lean_inc(v_k_3907_);
lean_inc(v_size_3906_);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_impl_3903_);
if (v_isSharedCheck_3951_ == 0)
{
lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3952_ = lean_ctor_get(v_impl_3903_, 4);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_impl_3903_, 3);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_impl_3903_, 2);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_impl_3903_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_impl_3903_, 0);
lean_dec(v_unused_3956_);
v___x_3918_ = v_impl_3903_;
v_isShared_3919_ = v_isSharedCheck_3951_;
goto v_resetjp_3917_;
}
else
{
lean_dec(v_impl_3903_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3951_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v_size_3920_; lean_object* v_k_3921_; lean_object* v_v_3922_; lean_object* v_l_3923_; lean_object* v_r_3924_; lean_object* v_size_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; 
v_size_3920_ = lean_ctor_get(v_l_3909_, 0);
v_k_3921_ = lean_ctor_get(v_l_3909_, 1);
v_v_3922_ = lean_ctor_get(v_l_3909_, 2);
v_l_3923_ = lean_ctor_get(v_l_3909_, 3);
v_r_3924_ = lean_ctor_get(v_l_3909_, 4);
v_size_3925_ = lean_ctor_get(v_r_3910_, 0);
v___x_3926_ = lean_unsigned_to_nat(2u);
v___x_3927_ = lean_nat_mul(v___x_3926_, v_size_3925_);
v___x_3928_ = lean_nat_dec_lt(v_size_3920_, v___x_3927_);
lean_dec(v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_inc(v_size_3925_);
lean_inc(v_r_3924_);
lean_inc(v_l_3923_);
lean_inc(v_v_3922_);
lean_inc(v_k_3921_);
lean_del_object(v___x_3918_);
lean_dec(v_l_3909_);
v___x_3929_ = lean_nat_add(v___x_3904_, v_size_3905_);
v___x_3930_ = lean_nat_add(v___x_3929_, v_size_3906_);
lean_dec(v_size_3906_);
if (lean_obj_tag(v_l_3923_) == 0)
{
lean_object* v_size_3931_; 
v_size_3931_ = lean_ctor_get(v_l_3923_, 0);
lean_inc(v_size_3931_);
v___y_3783_ = v___x_3929_;
v___y_3784_ = v_size_3925_;
v___y_3785_ = v_l_3923_;
v___y_3786_ = v___x_3930_;
v___y_3787_ = v_v_3922_;
v___y_3788_ = v___x_3904_;
v___y_3789_ = v_r_3924_;
v___y_3790_ = v_v_3908_;
v___y_3791_ = v_r_3910_;
v___y_3792_ = v_k_3921_;
v___y_3793_ = v_k_3907_;
v___y_3794_ = v_size_3931_;
goto v___jp_3782_;
}
else
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_unsigned_to_nat(0u);
v___y_3783_ = v___x_3929_;
v___y_3784_ = v_size_3925_;
v___y_3785_ = v_l_3923_;
v___y_3786_ = v___x_3930_;
v___y_3787_ = v_v_3922_;
v___y_3788_ = v___x_3904_;
v___y_3789_ = v_r_3924_;
v___y_3790_ = v_v_3908_;
v___y_3791_ = v_r_3910_;
v___y_3792_ = v_k_3921_;
v___y_3793_ = v_k_3907_;
v___y_3794_ = v___x_3932_;
goto v___jp_3782_;
}
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3933_ = lean_nat_add(v___x_3904_, v_size_3905_);
v___x_3934_ = lean_nat_add(v___x_3933_, v_size_3906_);
lean_dec(v_size_3906_);
v___x_3935_ = lean_nat_add(v___x_3933_, v_size_3920_);
lean_dec(v___x_3933_);
lean_inc_ref(v_l_3746_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 4, v_l_3909_);
lean_ctor_set(v___x_3918_, 3, v_l_3746_);
lean_ctor_set(v___x_3918_, 2, v_v_3745_);
lean_ctor_set(v___x_3918_, 1, v_k_3744_);
lean_ctor_set(v___x_3918_, 0, v___x_3935_);
v___x_3937_ = v___x_3918_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3950_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3950_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3950_, 4, v_l_3909_);
v___x_3937_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
v_isSharedCheck_3944_ = !lean_is_exclusive(v_l_3746_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3945_ = lean_ctor_get(v_l_3746_, 4);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_l_3746_, 3);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_l_3746_, 2);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_l_3746_, 1);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_l_3746_, 0);
lean_dec(v_unused_3949_);
v___x_3939_ = v_l_3746_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_dec(v_l_3746_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 4, v_r_3910_);
lean_ctor_set(v___x_3939_, 3, v___x_3937_);
lean_ctor_set(v___x_3939_, 2, v_v_3908_);
lean_ctor_set(v___x_3939_, 1, v_k_3907_);
lean_ctor_set(v___x_3939_, 0, v___x_3934_);
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_k_3907_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_v_3908_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v_r_3910_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3957_; 
v_l_3957_ = lean_ctor_get(v_impl_3903_, 3);
lean_inc(v_l_3957_);
if (lean_obj_tag(v_l_3957_) == 0)
{
lean_object* v_r_3958_; lean_object* v_k_3959_; lean_object* v_v_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3981_; 
v_r_3958_ = lean_ctor_get(v_impl_3903_, 4);
v_k_3959_ = lean_ctor_get(v_impl_3903_, 1);
v_v_3960_ = lean_ctor_get(v_impl_3903_, 2);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_impl_3903_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; lean_object* v_unused_3983_; 
v_unused_3982_ = lean_ctor_get(v_impl_3903_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_impl_3903_, 0);
lean_dec(v_unused_3983_);
v___x_3962_ = v_impl_3903_;
v_isShared_3963_ = v_isSharedCheck_3981_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_r_3958_);
lean_inc(v_v_3960_);
lean_inc(v_k_3959_);
lean_dec(v_impl_3903_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3981_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v_k_3964_; lean_object* v_v_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3977_; 
v_k_3964_ = lean_ctor_get(v_l_3957_, 1);
v_v_3965_ = lean_ctor_get(v_l_3957_, 2);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_l_3957_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; 
v_unused_3978_ = lean_ctor_get(v_l_3957_, 4);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_l_3957_, 3);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_l_3957_, 0);
lean_dec(v_unused_3980_);
v___x_3967_ = v_l_3957_;
v_isShared_3968_ = v_isSharedCheck_3977_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_v_3965_);
lean_inc(v_k_3964_);
lean_dec(v_l_3957_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3977_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
v___x_3969_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3958_, 2);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 4, v_r_3958_);
lean_ctor_set(v___x_3967_, 3, v_r_3958_);
lean_ctor_set(v___x_3967_, 2, v_v_3745_);
lean_ctor_set(v___x_3967_, 1, v_k_3744_);
lean_ctor_set(v___x_3967_, 0, v___x_3904_);
v___x_3971_ = v___x_3967_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v_r_3958_);
lean_ctor_set(v_reuseFailAlloc_3976_, 4, v_r_3958_);
v___x_3971_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3973_; 
lean_inc(v_r_3958_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 3, v_r_3958_);
lean_ctor_set(v___x_3962_, 0, v___x_3904_);
v___x_3973_ = v___x_3962_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_k_3959_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_v_3960_);
lean_ctor_set(v_reuseFailAlloc_3975_, 3, v_r_3958_);
lean_ctor_set(v_reuseFailAlloc_3975_, 4, v_r_3958_);
v___x_3973_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3969_);
lean_ctor_set(v___x_3974_, 1, v_k_3964_);
lean_ctor_set(v___x_3974_, 2, v_v_3965_);
lean_ctor_set(v___x_3974_, 3, v___x_3971_);
lean_ctor_set(v___x_3974_, 4, v___x_3973_);
return v___x_3974_;
}
}
}
}
}
else
{
lean_object* v_r_3984_; 
v_r_3984_ = lean_ctor_get(v_impl_3903_, 4);
lean_inc(v_r_3984_);
if (lean_obj_tag(v_r_3984_) == 0)
{
lean_object* v_k_3985_; lean_object* v_v_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3995_; 
v_k_3985_ = lean_ctor_get(v_impl_3903_, 1);
v_v_3986_ = lean_ctor_get(v_impl_3903_, 2);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_impl_3903_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; lean_object* v_unused_3997_; lean_object* v_unused_3998_; 
v_unused_3996_ = lean_ctor_get(v_impl_3903_, 4);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v_impl_3903_, 3);
lean_dec(v_unused_3997_);
v_unused_3998_ = lean_ctor_get(v_impl_3903_, 0);
lean_dec(v_unused_3998_);
v___x_3988_ = v_impl_3903_;
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_v_3986_);
lean_inc(v_k_3985_);
lean_dec(v_impl_3903_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_unsigned_to_nat(3u);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 4, v_l_3957_);
lean_ctor_set(v___x_3988_, 2, v_v_3745_);
lean_ctor_set(v___x_3988_, 1, v_k_3744_);
lean_ctor_set(v___x_3988_, 0, v___x_3904_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_l_3957_);
lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_l_3957_);
v___x_3992_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3990_);
lean_ctor_set(v___x_3993_, 1, v_k_3985_);
lean_ctor_set(v___x_3993_, 2, v_v_3986_);
lean_ctor_set(v___x_3993_, 3, v___x_3992_);
lean_ctor_set(v___x_3993_, 4, v_r_3984_);
return v___x_3993_;
}
}
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_unsigned_to_nat(2u);
v___x_4000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v_k_3744_);
lean_ctor_set(v___x_4000_, 2, v_v_3745_);
lean_ctor_set(v___x_4000_, 3, v_r_3984_);
lean_ctor_set(v___x_4000_, 4, v_impl_3903_);
return v___x_4000_;
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
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_unsigned_to_nat(1u);
v___x_4009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
lean_ctor_set(v___x_4009_, 1, v_k_3726_);
lean_ctor_set(v___x_4009_, 2, v_v_3727_);
lean_ctor_set(v___x_4009_, 3, v_t_3728_);
lean_ctor_set(v___x_4009_, 4, v_t_3728_);
return v___x_4009_;
}
v___jp_3729_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3740_ = lean_nat_add(v___y_3737_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec(v___y_3737_);
v___x_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set(v___x_3741_, 1, v___y_3738_);
lean_ctor_set(v___x_3741_, 2, v___y_3735_);
lean_ctor_set(v___x_3741_, 3, v___y_3733_);
lean_ctor_set(v___x_3741_, 4, v___y_3734_);
v___x_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3742_, 0, v___y_3731_);
lean_ctor_set(v___x_3742_, 1, v___y_3736_);
lean_ctor_set(v___x_3742_, 2, v___y_3730_);
lean_ctor_set(v___x_3742_, 3, v___y_3732_);
lean_ctor_set(v___x_3742_, 4, v___x_3741_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4010_, lean_object* v_k_4011_, lean_object* v_fallback_4012_){
_start:
{
if (lean_obj_tag(v_t_4010_) == 0)
{
lean_object* v_k_4013_; lean_object* v_v_4014_; lean_object* v_l_4015_; lean_object* v_r_4016_; uint8_t v___y_4018_; lean_object* v_fst_4021_; lean_object* v_snd_4022_; lean_object* v_fst_4023_; lean_object* v_snd_4024_; uint8_t v___x_4025_; 
v_k_4013_ = lean_ctor_get(v_t_4010_, 1);
v_v_4014_ = lean_ctor_get(v_t_4010_, 2);
v_l_4015_ = lean_ctor_get(v_t_4010_, 3);
v_r_4016_ = lean_ctor_get(v_t_4010_, 4);
v_fst_4021_ = lean_ctor_get(v_k_4011_, 0);
v_snd_4022_ = lean_ctor_get(v_k_4011_, 1);
v_fst_4023_ = lean_ctor_get(v_k_4013_, 0);
v_snd_4024_ = lean_ctor_get(v_k_4013_, 1);
v___x_4025_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4021_, v_fst_4023_);
if (v___x_4025_ == 1)
{
uint8_t v___x_4026_; 
v___x_4026_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4022_, v_snd_4024_);
v___y_4018_ = v___x_4026_;
goto v___jp_4017_;
}
else
{
v___y_4018_ = v___x_4025_;
goto v___jp_4017_;
}
v___jp_4017_:
{
switch(v___y_4018_)
{
case 0:
{
v_t_4010_ = v_l_4015_;
goto _start;
}
case 1:
{
lean_inc(v_v_4014_);
return v_v_4014_;
}
default: 
{
v_t_4010_ = v_r_4016_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4012_);
return v_fallback_4012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4027_, lean_object* v_k_4028_, lean_object* v_fallback_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4027_, v_k_4028_, v_fallback_4029_);
lean_dec(v_fallback_4029_);
lean_dec_ref(v_k_4028_);
lean_dec(v_t_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4031_, lean_object* v_as_4032_, size_t v_sz_4033_, size_t v_i_4034_, lean_object* v_b_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
uint8_t v___x_4039_; 
v___x_4039_ = lean_usize_dec_lt(v_i_4034_, v_sz_4033_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; 
lean_dec(v___x_4031_);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v_b_4035_);
return v___x_4040_;
}
else
{
lean_object* v_a_4041_; lean_object* v_fst_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4070_; 
v_a_4041_ = lean_array_uget(v_as_4032_, v_i_4034_);
v_fst_4042_ = lean_ctor_get(v_a_4041_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_a_4041_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v_a_4041_, 1);
lean_dec(v_unused_4071_);
v___x_4044_ = v_a_4041_;
v_isShared_4045_ = v_isSharedCheck_4070_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_fst_4042_);
lean_dec(v_a_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4070_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4042_);
v___x_4047_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4042_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___y_4050_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
if (lean_obj_tag(v_a_4048_) == 0)
{
lean_inc(v___x_4031_);
v___y_4050_ = v___x_4031_;
goto v___jp_4049_;
}
else
{
lean_object* v_val_4061_; 
v_val_4061_ = lean_ctor_get(v_a_4048_, 0);
lean_inc(v_val_4061_);
lean_dec_ref_known(v_a_4048_, 1);
v___y_4050_ = v_val_4061_;
goto v___jp_4049_;
}
v___jp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 1, v_fst_4042_);
lean_ctor_set(v___x_4044_, 0, v___y_4050_);
v___x_4052_ = v___x_4044_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___y_4050_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_fst_4042_);
v___x_4052_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; size_t v___x_4057_; size_t v___x_4058_; 
v___x_4053_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4035_, v___x_4052_, v___x_4046_);
v___x_4054_ = lean_unsigned_to_nat(1u);
v___x_4055_ = lean_nat_add(v___x_4053_, v___x_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4052_, v___x_4055_, v_b_4035_);
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_add(v_i_4034_, v___x_4057_);
v_i_4034_ = v___x_4058_;
v_b_4035_ = v___x_4056_;
goto _start;
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_del_object(v___x_4044_);
lean_dec(v_fst_4042_);
lean_dec(v_b_4035_);
lean_dec(v___x_4031_);
v_a_4062_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4047_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4047_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4072_, lean_object* v_as_4073_, lean_object* v_sz_4074_, lean_object* v_i_4075_, lean_object* v_b_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
size_t v_sz_boxed_4080_; size_t v_i_boxed_4081_; lean_object* v_res_4082_; 
v_sz_boxed_4080_ = lean_unbox_usize(v_sz_4074_);
lean_dec(v_sz_4074_);
v_i_boxed_4081_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_res_4082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4072_, v_as_4073_, v_sz_boxed_4080_, v_i_boxed_4081_, v_b_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v_as_4073_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4083_, lean_object* v_init_4084_, lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 0)
{
lean_object* v_k_4087_; lean_object* v_v_4088_; lean_object* v_l_4089_; lean_object* v_r_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v_a_4093_; lean_object* v_a_4094_; lean_object* v_fst_4095_; lean_object* v_snd_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4110_; 
v_k_4087_ = lean_ctor_get(v_x_4085_, 1);
lean_inc(v_k_4087_);
v_v_4088_ = lean_ctor_get(v_x_4085_, 2);
lean_inc(v_v_4088_);
v_l_4089_ = lean_ctor_get(v_x_4085_, 3);
lean_inc(v_l_4089_);
v_r_4090_ = lean_ctor_get(v_x_4085_, 4);
lean_inc(v_r_4090_);
lean_dec_ref_known(v_x_4085_, 5);
v___x_4091_ = 1;
lean_inc_ref(v_fst_4083_);
v___x_4092_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4083_, v_init_4084_, v_l_4089_);
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref(v___x_4092_);
v_a_4094_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_a_4094_);
lean_dec(v_a_4093_);
v_fst_4095_ = lean_ctor_get(v_k_4087_, 0);
v_snd_4096_ = lean_ctor_get(v_k_4087_, 1);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_k_4087_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4098_ = v_k_4087_;
v_isShared_4099_ = v_isSharedCheck_4110_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_snd_4096_);
lean_inc(v_fst_4095_);
lean_dec(v_k_4087_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4110_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v_optName_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v_optName_4100_ = lean_ctor_get(v_fst_4083_, 1);
lean_inc(v_optName_4100_);
v___x_4101_ = l_Lean_Name_toString(v_optName_4100_, v___x_4091_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set_tag(v___x_4098_, 1);
v___x_4103_ = v___x_4098_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_fst_4095_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_snd_4096_);
v___x_4103_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
double v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4104_ = lean_float_of_nat(v_v_4088_);
v___x_4105_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4105_, 0, v___x_4104_);
v___x_4106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4101_);
lean_ctor_set(v___x_4106_, 1, v___x_4103_);
lean_ctor_set(v___x_4106_, 2, v___x_4105_);
v___x_4107_ = lean_array_push(v_a_4094_, v___x_4106_);
v_init_4084_ = v___x_4107_;
v_x_4085_ = v_r_4090_;
goto _start;
}
}
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec_ref(v_fst_4083_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_init_4084_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4113_, lean_object* v_init_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4113_, v_init_4114_, v_x_4115_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4118_, lean_object* v_as_4119_, size_t v_sz_4120_, size_t v_i_4121_, lean_object* v_b_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_a_4127_; uint8_t v___x_4131_; 
v___x_4131_ = lean_usize_dec_lt(v_i_4121_, v_sz_4120_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
lean_dec(v___x_4118_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_b_4122_);
return v___x_4132_;
}
else
{
lean_object* v_a_4133_; lean_object* v_snd_4134_; lean_object* v_fst_4135_; lean_object* v_size_4136_; lean_object* v_buckets_4137_; lean_object* v___x_4138_; lean_object* v___y_4140_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v_a_4133_ = lean_array_uget_borrowed(v_as_4119_, v_i_4121_);
v_snd_4134_ = lean_ctor_get(v_a_4133_, 1);
v_fst_4135_ = lean_ctor_get(v_a_4133_, 0);
v_size_4136_ = lean_ctor_get(v_snd_4134_, 0);
v_buckets_4137_ = lean_ctor_get(v_snd_4134_, 1);
v___x_4138_ = lean_box(1);
v___x_4174_ = lean_mk_empty_array_with_capacity(v_size_4136_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = lean_array_get_size(v_buckets_4137_);
v___x_4177_ = lean_nat_dec_lt(v___x_4175_, v___x_4176_);
if (v___x_4177_ == 0)
{
v___y_4140_ = v___x_4174_;
goto v___jp_4139_;
}
else
{
size_t v___x_4178_; size_t v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = ((size_t)0ULL);
v___x_4179_ = lean_usize_of_nat(v___x_4176_);
v___x_4180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4137_, v___x_4178_, v___x_4179_, v___x_4174_);
v___y_4140_ = v___x_4180_;
goto v___jp_4139_;
}
v___jp_4139_:
{
size_t v_sz_4141_; size_t v___x_4142_; lean_object* v___x_4143_; 
v_sz_4141_ = lean_array_size(v___y_4140_);
v___x_4142_ = ((size_t)0ULL);
lean_inc(v___x_4118_);
v___x_4143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4118_, v___y_4140_, v_sz_4141_, v___x_4142_, v___x_4138_, v___y_4123_, v___y_4124_);
lean_dec_ref(v___y_4140_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
lean_inc(v_fst_4135_);
v___x_4145_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4135_, v_b_4122_, v_a_4144_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v_a_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v_a_4147_ = lean_ctor_get(v_a_4146_, 0);
lean_inc(v_a_4147_);
lean_dec(v_a_4146_);
v_a_4127_ = v_a_4147_;
goto v___jp_4126_;
}
else
{
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4157_; 
v_a_4148_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4150_ = v___x_4145_;
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4145_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
if (lean_obj_tag(v_a_4148_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; 
lean_dec(v___x_4118_);
v_a_4152_ = lean_ctor_get(v_a_4148_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v_a_4148_, 1);
if (v_isShared_4151_ == 0)
{
lean_ctor_set_tag(v___x_4150_, 0);
lean_ctor_set(v___x_4150_, 0, v_a_4152_);
v___x_4154_ = v___x_4150_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
else
{
lean_object* v_a_4156_; 
lean_del_object(v___x_4150_);
v_a_4156_ = lean_ctor_get(v_a_4148_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v_a_4148_, 1);
v_a_4127_ = v_a_4156_;
goto v___jp_4126_;
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v___x_4118_);
v_a_4158_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4145_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4145_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v_b_4122_);
lean_dec(v___x_4118_);
v_a_4166_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4143_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4143_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
v___jp_4126_:
{
size_t v___x_4128_; size_t v___x_4129_; 
v___x_4128_ = ((size_t)1ULL);
v___x_4129_ = lean_usize_add(v_i_4121_, v___x_4128_);
v_i_4121_ = v___x_4129_;
v_b_4122_ = v_a_4127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4181_, lean_object* v_as_4182_, lean_object* v_sz_4183_, lean_object* v_i_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
size_t v_sz_boxed_4189_; size_t v_i_boxed_4190_; lean_object* v_res_4191_; 
v_sz_boxed_4189_ = lean_unbox_usize(v_sz_4183_);
lean_dec(v_sz_4183_);
v_i_boxed_4190_ = lean_unbox_usize(v_i_4184_);
lean_dec(v_i_4184_);
v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4181_, v_as_4182_, v_sz_boxed_4189_, v_i_boxed_4190_, v_b_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec_ref(v_as_4182_);
return v_res_4191_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = l_Lean_maxRecDepth;
v___x_4199_ = l_Lean_Options_empty;
v___x_4200_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_4199_, v___x_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4201_, lean_object* v_linterOpts_4202_, lean_object* v_sp_4203_, lean_object* v_env_4204_, lean_object* v_mod_4205_){
_start:
{
lean_object* v_a_4208_; lean_object* v_msg_4212_; lean_object* v_a_4217_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint16_t v___x_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v_a_4258_; lean_object* v___y_4262_; uint8_t v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; uint8_t v___y_4271_; uint8_t v___y_4272_; uint8_t v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; uint8_t v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v_fileName_4387_; lean_object* v_fileMap_4388_; lean_object* v_currNamespace_4389_; lean_object* v_openDecls_4390_; lean_object* v_initHeartbeats_4391_; lean_object* v_maxHeartbeats_4392_; lean_object* v_quotContext_4393_; lean_object* v_currMacroScope_4394_; lean_object* v_cancelTk_x3f_4395_; lean_object* v_inheritedTraceOptions_4396_; lean_object* v_currRecDepth_4397_; lean_object* v_ref_4398_; uint8_t v_suppressElabErrors_4399_; uint8_t v_isRecordingDeps_4400_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___y_4422_; lean_object* v_env_4443_; uint8_t v___x_4444_; uint8_t v___x_4445_; 
v___x_4231_ = l_Lean_Name_getRoot(v_mod_4205_);
v___x_4232_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4233_ = l_Lean_instInhabitedFileMap_default;
v___x_4234_ = l_Lean_Options_empty;
v___x_4235_ = lean_box(0);
v___x_4236_ = lean_box(0);
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4239_ = l_Lean_firstFrontendMacroScope;
v___x_4240_ = lean_box(0);
v___x_4241_ = lean_box(0);
v___x_4242_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4243_ = 0;
v___x_4244_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4245_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4246_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4247_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4248_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4250_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4251_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4252_ = 1;
v___x_4253_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4254_, 0, v_env_4204_);
lean_ctor_set(v___x_4254_, 1, v___x_4244_);
lean_ctor_set(v___x_4254_, 2, v___x_4245_);
lean_ctor_set(v___x_4254_, 3, v___x_4246_);
lean_ctor_set(v___x_4254_, 4, v___x_4247_);
lean_ctor_set(v___x_4254_, 5, v___x_4248_);
lean_ctor_set(v___x_4254_, 6, v___x_4250_);
lean_ctor_set(v___x_4254_, 7, v___x_4251_);
lean_ctor_set(v___x_4254_, 8, v___x_4253_);
lean_ctor_set(v___x_4254_, 9, v___x_4249_);
v___x_4255_ = lean_io_get_num_heartbeats();
v___x_4256_ = lean_st_mk_ref(v___x_4254_);
v___x_4418_ = l_Lean_inheritedTraceOptions;
v___x_4419_ = lean_st_ref_get(v___x_4418_);
v___x_4420_ = lean_st_ref_get(v___x_4256_);
v_env_4443_ = lean_ctor_get(v___x_4420_, 0);
lean_inc_ref(v_env_4443_);
lean_dec(v___x_4420_);
v___x_4444_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4443_);
lean_dec_ref(v_env_4443_);
v___x_4445_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4445_ == 0)
{
if (v___x_4444_ == 0)
{
v___y_4422_ = v___x_4252_;
goto v___jp_4421_;
}
else
{
v_fileName_4387_ = v___x_4232_;
v_fileMap_4388_ = v___x_4233_;
v_currNamespace_4389_ = v___x_4235_;
v_openDecls_4390_ = v___x_4236_;
v_initHeartbeats_4391_ = v___x_4255_;
v_maxHeartbeats_4392_ = v___x_4238_;
v_quotContext_4393_ = v___x_4235_;
v_currMacroScope_4394_ = v___x_4239_;
v_cancelTk_x3f_4395_ = v___x_4240_;
v_inheritedTraceOptions_4396_ = v___x_4419_;
v_currRecDepth_4397_ = v___x_4237_;
v_ref_4398_ = v___x_4241_;
v_suppressElabErrors_4399_ = v___x_4243_;
v_isRecordingDeps_4400_ = v___x_4243_;
goto v___jp_4386_;
}
}
else
{
if (v___x_4444_ == 0)
{
v_fileName_4387_ = v___x_4232_;
v_fileMap_4388_ = v___x_4233_;
v_currNamespace_4389_ = v___x_4235_;
v_openDecls_4390_ = v___x_4236_;
v_initHeartbeats_4391_ = v___x_4255_;
v_maxHeartbeats_4392_ = v___x_4238_;
v_quotContext_4393_ = v___x_4235_;
v_currMacroScope_4394_ = v___x_4239_;
v_cancelTk_x3f_4395_ = v___x_4240_;
v_inheritedTraceOptions_4396_ = v___x_4419_;
v_currRecDepth_4397_ = v___x_4237_;
v_ref_4398_ = v___x_4241_;
v_suppressElabErrors_4399_ = v___x_4243_;
v_isRecordingDeps_4400_ = v___x_4243_;
goto v___jp_4386_;
}
else
{
v___y_4422_ = v___x_4243_;
goto v___jp_4421_;
}
}
v___jp_4207_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = lean_mk_io_user_error(v_a_4208_);
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
v___jp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = l_Lean_MessageData_toString(v_msg_4212_);
v___x_4214_ = lean_mk_io_user_error(v___x_4213_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
v___jp_4216_:
{
if (lean_obj_tag(v_a_4217_) == 0)
{
lean_object* v_msg_4218_; 
v_msg_4218_ = lean_ctor_get(v_a_4217_, 1);
lean_inc_ref(v_msg_4218_);
lean_dec_ref_known(v_a_4217_, 2);
v_msg_4212_ = v_msg_4218_;
goto v___jp_4211_;
}
else
{
lean_object* v_id_4219_; lean_object* v___x_4220_; 
v_id_4219_ = lean_ctor_get(v_a_4217_, 0);
lean_inc(v_id_4219_);
lean_dec_ref_known(v_a_4217_, 2);
v___x_4220_ = l_Lean_InternalExceptionId_getName(v_id_4219_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_dec(v_id_4219_);
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4223_ = 1;
v___x_4224_ = l_Lean_Name_toString(v_a_4221_, v___x_4223_);
v___x_4225_ = lean_string_append(v___x_4222_, v___x_4224_);
lean_dec_ref(v___x_4224_);
v_a_4208_ = v___x_4225_;
goto v___jp_4207_;
}
else
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
lean_dec_ref_known(v___x_4220_, 1);
v___x_4226_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4227_ = l_Nat_reprFast(v_id_4219_);
v___x_4228_ = lean_string_append(v___x_4226_, v___x_4227_);
lean_dec_ref(v___x_4227_);
v___x_4229_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4230_ = lean_string_append(v___x_4228_, v___x_4229_);
v_a_4208_ = v___x_4230_;
goto v___jp_4207_;
}
}
}
v___jp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4259_ = lean_st_ref_get(v___x_4256_);
lean_dec(v___x_4256_);
lean_dec(v___x_4259_);
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v_a_4258_);
return v___x_4260_;
}
v___jp_4261_:
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___y_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___y_4262_);
v_a_4258_ = v_a_4263_;
goto v___jp_4257_;
}
v___jp_4264_:
{
switch(v___y_4265_)
{
case 0:
{
lean_dec(v_sp_4203_);
if (v___y_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
v___x_4273_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4274_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4205_, v___x_4252_);
v___x_4275_ = lean_string_append(v___x_4273_, v___x_4274_);
lean_dec_ref(v___x_4274_);
v___x_4276_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4277_ = lean_string_append(v___x_4275_, v___x_4276_);
v___x_4278_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4277_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4280_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
v___x_4280_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4272_, v_a_4279_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
v___y_4262_ = v___x_4280_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___x_4256_);
v_a_4281_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4283_ = v___x_4278_;
v_isShared_4284_ = v_isSharedCheck_4290_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4278_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4290_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4285_ = lean_io_error_to_string(v_a_4281_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 3);
lean_ctor_set(v___x_4283_, 0, v___x_4285_);
v___x_4287_ = v___x_4283_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_MessageData_ofFormat(v___x_4287_);
v_msg_4212_ = v___x_4288_;
goto v___jp_4211_;
}
}
}
}
else
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4291_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4205_, v___y_4272_);
v___x_4293_ = lean_string_append(v___x_4291_, v___x_4292_);
lean_dec_ref(v___x_4292_);
v___x_4294_ = lean_array_get_size(v___y_4270_);
lean_dec_ref(v___y_4270_);
v___x_4295_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4268_, v___y_4269_, v___x_4252_, v___x_4293_, v___x_4294_, v___x_4252_, v___y_4266_, v___y_4267_);
lean_dec_ref(v___y_4269_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = l_Lean_MessageData_toString(v_a_4296_);
v___x_4298_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4297_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4300_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v___x_4300_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4272_, v_a_4299_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
v___y_4262_ = v___x_4300_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4310_; 
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___x_4256_);
v_a_4301_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4303_ = v___x_4298_;
v_isShared_4304_ = v_isSharedCheck_4310_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4298_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4310_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4305_ = lean_io_error_to_string(v_a_4301_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 3);
lean_ctor_set(v___x_4303_, 0, v___x_4305_);
v___x_4307_ = v___x_4303_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_MessageData_ofFormat(v___x_4307_);
v_msg_4212_ = v___x_4308_;
goto v___jp_4211_;
}
}
}
}
else
{
lean_object* v_a_4311_; 
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___x_4256_);
v_a_4311_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4295_, 1);
v_a_4217_ = v_a_4311_;
goto v___jp_4216_;
}
}
}
case 1:
{
lean_object* v___x_4312_; lean_object* v_env_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; size_t v_sz_4317_; size_t v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v_mod_4205_);
v___x_4312_ = lean_st_ref_get(v___y_4267_);
v_env_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc_ref(v_env_4313_);
lean_dec(v___x_4312_);
v___x_4314_ = l_Lean_Environment_mainModule(v_env_4313_);
lean_dec_ref(v_env_4313_);
v___x_4315_ = lean_box(v___y_4271_);
v___x_4316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4249_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v_sz_4317_ = lean_array_size(v___y_4268_);
v___x_4318_ = ((size_t)0ULL);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4203_, v___x_4314_, v___y_4268_, v_sz_4317_, v___x_4318_, v___x_4316_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v___y_4268_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v_fst_4321_; lean_object* v_snd_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v_fst_4321_ = lean_ctor_get(v_a_4320_, 0);
lean_inc(v_fst_4321_);
v_snd_4322_ = lean_ctor_get(v_a_4320_, 1);
lean_inc(v_snd_4322_);
lean_dec(v_a_4320_);
v___x_4323_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4323_, 0, v_fst_4321_);
v___x_4324_ = lean_unbox(v_snd_4322_);
lean_dec(v_snd_4322_);
lean_ctor_set_uint8(v___x_4323_, sizeof(void*)*1, v___x_4324_);
v_a_4258_ = v___x_4323_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4325_; 
lean_dec(v___x_4256_);
v_a_4325_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4319_, 1);
v_a_4217_ = v_a_4325_;
goto v___jp_4216_;
}
}
default: 
{
lean_object* v___x_4326_; lean_object* v_env_4327_; lean_object* v___x_4328_; size_t v_sz_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v_mod_4205_);
lean_dec(v_sp_4203_);
v___x_4326_ = lean_st_ref_get(v___y_4267_);
v_env_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc_ref(v_env_4327_);
lean_dec(v___x_4326_);
v___x_4328_ = l_Lean_Environment_mainModule(v_env_4327_);
lean_dec_ref(v_env_4327_);
v_sz_4329_ = lean_array_size(v___y_4268_);
v___x_4330_ = ((size_t)0ULL);
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4328_, v___y_4268_, v_sz_4329_, v___x_4330_, v___x_4249_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v___y_4268_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4331_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4331_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
lean_ctor_set_tag(v___x_4334_, 2);
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
v_a_4258_ = v___x_4337_;
goto v___jp_4257_;
}
}
}
else
{
lean_object* v_a_4340_; 
lean_dec(v___x_4256_);
v_a_4340_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4331_, 1);
v_a_4217_ = v_a_4340_;
goto v___jp_4216_;
}
}
}
}
v___jp_4341_:
{
lean_object* v___x_4348_; 
lean_inc_ref(v___y_4346_);
v___x_4348_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4345_, v___y_4346_, v___y_4343_, v___y_4344_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
v___x_4350_ = lean_array_get_size(v_a_4349_);
v___x_4351_ = lean_nat_dec_lt(v___x_4237_, v___x_4350_);
if (v___x_4351_ == 0)
{
v___y_4265_ = v___y_4342_;
v___y_4266_ = v___y_4343_;
v___y_4267_ = v___y_4344_;
v___y_4268_ = v_a_4349_;
v___y_4269_ = v___y_4345_;
v___y_4270_ = v___y_4346_;
v___y_4271_ = v___y_4347_;
v___y_4272_ = v___x_4351_;
goto v___jp_4264_;
}
else
{
if (v___x_4351_ == 0)
{
v___y_4265_ = v___y_4342_;
v___y_4266_ = v___y_4343_;
v___y_4267_ = v___y_4344_;
v___y_4268_ = v_a_4349_;
v___y_4269_ = v___y_4345_;
v___y_4270_ = v___y_4346_;
v___y_4271_ = v___y_4347_;
v___y_4272_ = v___x_4351_;
goto v___jp_4264_;
}
else
{
size_t v___x_4352_; size_t v___x_4353_; uint8_t v___x_4354_; 
v___x_4352_ = ((size_t)0ULL);
v___x_4353_ = lean_usize_of_nat(v___x_4350_);
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4347_, v_a_4349_, v___x_4352_, v___x_4353_);
v___y_4265_ = v___y_4342_;
v___y_4266_ = v___y_4343_;
v___y_4267_ = v___y_4344_;
v___y_4268_ = v_a_4349_;
v___y_4269_ = v___y_4345_;
v___y_4270_ = v___y_4346_;
v___y_4271_ = v___y_4347_;
v___y_4272_ = v___x_4354_;
goto v___jp_4264_;
}
}
}
else
{
lean_object* v_a_4355_; 
lean_dec_ref(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___x_4256_);
lean_dec(v_mod_4205_);
lean_dec(v_sp_4203_);
v_a_4355_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4348_, 1);
v_a_4217_ = v_a_4355_;
goto v___jp_4216_;
}
}
v___jp_4356_:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4361_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4361_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v___x_4364_ = lean_array_get_size(v_a_4363_);
v___x_4365_ = lean_nat_dec_eq(v___x_4364_, v___x_4237_);
if (v___x_4365_ == 0)
{
v___y_4342_ = v___y_4357_;
v___y_4343_ = v___y_4358_;
v___y_4344_ = v___y_4359_;
v___y_4345_ = v___y_4360_;
v___y_4346_ = v_a_4363_;
v___y_4347_ = v___x_4365_;
goto v___jp_4341_;
}
else
{
uint8_t v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = 0;
v___x_4367_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4357_, v___x_4366_);
if (v___x_4367_ == 0)
{
v___y_4342_ = v___y_4357_;
v___y_4343_ = v___y_4358_;
v___y_4344_ = v___y_4359_;
v___y_4345_ = v___y_4360_;
v___y_4346_ = v_a_4363_;
v___y_4347_ = v___x_4367_;
goto v___jp_4341_;
}
else
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
lean_dec(v_a_4363_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v_sp_4203_);
v___x_4368_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4205_, v___x_4367_);
v___x_4370_ = lean_string_append(v___x_4368_, v___x_4369_);
lean_dec_ref(v___x_4369_);
v___x_4371_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
v___x_4373_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4372_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v___x_4374_; 
lean_dec_ref_known(v___x_4373_, 1);
v___x_4374_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4258_ = v___x_4374_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v___x_4256_);
v_a_4375_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4377_ = v___x_4373_;
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4373_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_io_error_to_string(v_a_4375_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 3);
lean_ctor_set(v___x_4377_, 0, v___x_4379_);
v___x_4381_ = v___x_4377_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_MessageData_ofFormat(v___x_4381_);
v_msg_4212_ = v___x_4382_;
goto v___jp_4211_;
}
}
}
}
}
}
else
{
lean_object* v_a_4385_; 
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___x_4256_);
lean_dec(v_mod_4205_);
lean_dec(v_sp_4203_);
v_a_4385_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4362_, 1);
v_a_4217_ = v_a_4385_;
goto v___jp_4216_;
}
}
v___jp_4386_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4401_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4394_);
lean_inc(v_quotContext_4393_);
lean_inc(v_maxHeartbeats_4392_);
lean_inc(v_openDecls_4390_);
lean_inc(v_currNamespace_4389_);
lean_inc_ref(v_fileMap_4388_);
lean_inc_ref(v_fileName_4387_);
v___x_4402_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4402_, 0, v_fileName_4387_);
lean_ctor_set(v___x_4402_, 1, v_fileMap_4388_);
lean_ctor_set(v___x_4402_, 2, v___x_4234_);
lean_ctor_set(v___x_4402_, 3, v___x_4401_);
lean_ctor_set(v___x_4402_, 4, v_currNamespace_4389_);
lean_ctor_set(v___x_4402_, 5, v_openDecls_4390_);
lean_ctor_set(v___x_4402_, 6, v_initHeartbeats_4391_);
lean_ctor_set(v___x_4402_, 7, v_maxHeartbeats_4392_);
lean_ctor_set(v___x_4402_, 8, v_quotContext_4393_);
lean_ctor_set(v___x_4402_, 9, v_currMacroScope_4394_);
lean_ctor_set(v___x_4402_, 10, v_cancelTk_x3f_4395_);
lean_ctor_set(v___x_4402_, 11, v_inheritedTraceOptions_4396_);
lean_inc(v_ref_4398_);
v___x_4403_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4403_, 0, v___x_4402_);
lean_ctor_set(v___x_4403_, 1, v_currRecDepth_4397_);
lean_ctor_set(v___x_4403_, 2, v_ref_4398_);
lean_ctor_set_uint16(v___x_4403_, sizeof(void*)*3, v___x_4242_);
lean_ctor_set_uint8(v___x_4403_, sizeof(void*)*3 + 2, v_suppressElabErrors_4399_);
lean_ctor_set_uint8(v___x_4403_, sizeof(void*)*3 + 3, v_isRecordingDeps_4400_);
v___x_4404_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4231_, v___x_4256_);
lean_dec(v___x_4231_);
if (lean_obj_tag(v___x_4404_) == 0)
{
uint8_t v_lintOnly_4405_; 
v_lintOnly_4405_ = lean_ctor_get_uint8(v_args_4201_, sizeof(void*)*4);
if (v_lintOnly_4405_ == 0)
{
lean_object* v_a_4406_; uint8_t v_mode_4407_; 
lean_dec_ref(v_linterOpts_4202_);
v_a_4406_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4404_, 1);
v_mode_4407_ = lean_ctor_get_uint8(v_args_4201_, sizeof(void*)*4 + 1);
lean_inc(v___x_4256_);
v___y_4357_ = v_mode_4407_;
v___y_4358_ = v___x_4403_;
v___y_4359_ = v___x_4256_;
v___y_4360_ = v_a_4406_;
v___y_4361_ = v___x_4240_;
goto v___jp_4356_;
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4416_; 
v_a_4408_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4410_ = v___x_4404_;
v_isShared_4411_ = v_isSharedCheck_4416_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4404_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4416_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
uint8_t v_mode_4412_; lean_object* v___x_4414_; 
v_mode_4412_ = lean_ctor_get_uint8(v_args_4201_, sizeof(void*)*4 + 1);
if (v_isShared_4411_ == 0)
{
lean_ctor_set_tag(v___x_4410_, 1);
lean_ctor_set(v___x_4410_, 0, v_linterOpts_4202_);
v___x_4414_ = v___x_4410_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_linterOpts_4202_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_inc(v___x_4256_);
v___y_4357_ = v_mode_4412_;
v___y_4358_ = v___x_4403_;
v___y_4359_ = v___x_4256_;
v___y_4360_ = v_a_4408_;
v___y_4361_ = v___x_4414_;
goto v___jp_4356_;
}
}
}
}
else
{
lean_object* v_a_4417_; 
lean_dec_ref_known(v___x_4403_, 3);
lean_dec(v___x_4256_);
lean_dec(v_mod_4205_);
lean_dec(v_sp_4203_);
lean_dec_ref(v_linterOpts_4202_);
v_a_4417_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4404_, 1);
v_a_4217_ = v_a_4417_;
goto v___jp_4216_;
}
}
v___jp_4421_:
{
lean_object* v___x_4423_; lean_object* v_env_4424_; lean_object* v_nextMacroScope_4425_; lean_object* v_ngen_4426_; lean_object* v_auxDeclNGen_4427_; lean_object* v_traceState_4428_; lean_object* v_recordedDeps_4429_; lean_object* v_messages_4430_; lean_object* v_infoState_4431_; lean_object* v_snapshotTasks_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4441_; 
v___x_4423_ = lean_st_ref_take(v___x_4256_);
v_env_4424_ = lean_ctor_get(v___x_4423_, 0);
v_nextMacroScope_4425_ = lean_ctor_get(v___x_4423_, 1);
v_ngen_4426_ = lean_ctor_get(v___x_4423_, 2);
v_auxDeclNGen_4427_ = lean_ctor_get(v___x_4423_, 3);
v_traceState_4428_ = lean_ctor_get(v___x_4423_, 4);
v_recordedDeps_4429_ = lean_ctor_get(v___x_4423_, 6);
v_messages_4430_ = lean_ctor_get(v___x_4423_, 7);
v_infoState_4431_ = lean_ctor_get(v___x_4423_, 8);
v_snapshotTasks_4432_ = lean_ctor_get(v___x_4423_, 9);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; 
v_unused_4442_ = lean_ctor_get(v___x_4423_, 5);
lean_dec(v_unused_4442_);
v___x_4434_ = v___x_4423_;
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_snapshotTasks_4432_);
lean_inc(v_infoState_4431_);
lean_inc(v_messages_4430_);
lean_inc(v_recordedDeps_4429_);
lean_inc(v_traceState_4428_);
lean_inc(v_auxDeclNGen_4427_);
lean_inc(v_ngen_4426_);
lean_inc(v_nextMacroScope_4425_);
lean_inc(v_env_4424_);
lean_dec(v___x_4423_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4436_ = l_Lean_Kernel_enableDiag(v_env_4424_, v___y_4422_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 5, v___x_4248_);
lean_ctor_set(v___x_4434_, 0, v___x_4436_);
v___x_4438_ = v___x_4434_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_nextMacroScope_4425_);
lean_ctor_set(v_reuseFailAlloc_4440_, 2, v_ngen_4426_);
lean_ctor_set(v_reuseFailAlloc_4440_, 3, v_auxDeclNGen_4427_);
lean_ctor_set(v_reuseFailAlloc_4440_, 4, v_traceState_4428_);
lean_ctor_set(v_reuseFailAlloc_4440_, 5, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4440_, 6, v_recordedDeps_4429_);
lean_ctor_set(v_reuseFailAlloc_4440_, 7, v_messages_4430_);
lean_ctor_set(v_reuseFailAlloc_4440_, 8, v_infoState_4431_);
lean_ctor_set(v_reuseFailAlloc_4440_, 9, v_snapshotTasks_4432_);
v___x_4438_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_st_ref_put(v___x_4256_, v___x_4438_);
v_fileName_4387_ = v___x_4232_;
v_fileMap_4388_ = v___x_4233_;
v_currNamespace_4389_ = v___x_4235_;
v_openDecls_4390_ = v___x_4236_;
v_initHeartbeats_4391_ = v___x_4255_;
v_maxHeartbeats_4392_ = v___x_4238_;
v_quotContext_4393_ = v___x_4235_;
v_currMacroScope_4394_ = v___x_4239_;
v_cancelTk_x3f_4395_ = v___x_4240_;
v_inheritedTraceOptions_4396_ = v___x_4419_;
v_currRecDepth_4397_ = v___x_4237_;
v_ref_4398_ = v___x_4241_;
v_suppressElabErrors_4399_ = v___x_4243_;
v_isRecordingDeps_4400_ = v___x_4243_;
goto v___jp_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4446_, lean_object* v_linterOpts_4447_, lean_object* v_sp_4448_, lean_object* v_env_4449_, lean_object* v_mod_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4446_, v_linterOpts_4447_, v_sp_4448_, v_env_4449_, v_mod_4450_);
lean_dec_ref(v_args_4446_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4453_, lean_object* v_t_4454_, lean_object* v_k_4455_, lean_object* v_fallback_4456_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4454_, v_k_4455_, v_fallback_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4458_, lean_object* v_t_4459_, lean_object* v_k_4460_, lean_object* v_fallback_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4458_, v_t_4459_, v_k_4460_, v_fallback_4461_);
lean_dec(v_fallback_4461_);
lean_dec_ref(v_k_4460_);
lean_dec(v_t_4459_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4463_, lean_object* v_k_4464_, lean_object* v_v_4465_, lean_object* v_t_4466_, lean_object* v_hl_4467_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4464_, v_v_4465_, v_t_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4469_, lean_object* v_init_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4469_, v_init_4470_, v_x_4471_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4476_, lean_object* v_init_4477_, lean_object* v_x_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4476_, v_init_4477_, v_x_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4483_, lean_object* v_constName_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4484_, v___y_4485_, v___y_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4489_, lean_object* v_constName_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4489_, v_constName_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4495_, lean_object* v_ref_4496_, lean_object* v_constName_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4496_, v_constName_4497_, v___y_4498_, v___y_4499_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4502_, lean_object* v_ref_4503_, lean_object* v_constName_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4502_, v_ref_4503_, v_constName_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v_ref_4503_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4509_, lean_object* v_ref_4510_, lean_object* v_msg_4511_, lean_object* v_declHint_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4510_, v_msg_4511_, v_declHint_4512_, v___y_4513_, v___y_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4517_, lean_object* v_ref_4518_, lean_object* v_msg_4519_, lean_object* v_declHint_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4517_, v_ref_4518_, v_msg_4519_, v_declHint_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v_ref_4518_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4525_, lean_object* v_declHint_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4525_, v_declHint_4526_, v___y_4528_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4531_, lean_object* v_declHint_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4531_, v_declHint_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4537_, lean_object* v_ref_4538_, lean_object* v_msg_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4538_, v_msg_4539_, v___y_4540_, v___y_4541_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4544_, lean_object* v_ref_4545_, lean_object* v_msg_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4544_, v_ref_4545_, v_msg_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v_ref_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4551_, lean_object* v_msg_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4552_, v___y_4553_, v___y_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4557_, lean_object* v_msg_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4557_, v_msg_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4563_){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint32_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4565_ = l_Std_Format_defWidth;
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = l_Std_Format_pretty(v_s_4563_, v___x_4565_, v___x_4566_, v___x_4566_);
v___x_4568_ = 10;
v___x_4569_ = lean_string_push(v___x_4567_, v___x_4568_);
v___x_4570_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4571_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4574_, size_t v_sz_4575_, size_t v_i_4576_, lean_object* v_b_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_usize_dec_lt(v_i_4576_, v_sz_4575_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_b_4577_);
return v___x_4581_;
}
else
{
lean_object* v___x_4582_; lean_object* v_a_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v_ref_4586_; lean_object* v___x_4587_; 
v___x_4582_ = lean_box(0);
v_a_4583_ = lean_array_uget_borrowed(v_as_4574_, v_i_4576_);
v___x_4584_ = lean_box(0);
lean_inc(v_a_4583_);
v___x_4585_ = l_Lean_MessageData_format(v_a_4583_, v___x_4584_);
v_ref_4586_ = lean_ctor_get(v___y_4578_, 2);
v___x_4587_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4585_);
if (lean_obj_tag(v___x_4587_) == 0)
{
size_t v___x_4588_; size_t v___x_4589_; 
lean_dec_ref_known(v___x_4587_, 1);
v___x_4588_ = ((size_t)1ULL);
v___x_4589_ = lean_usize_add(v_i_4576_, v___x_4588_);
v_i_4576_ = v___x_4589_;
v_b_4577_ = v___x_4582_;
goto _start;
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4602_; 
v_a_4591_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4593_ = v___x_4587_;
v_isShared_4594_ = v_isSharedCheck_4602_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4602_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4595_ = lean_io_error_to_string(v_a_4591_);
v___x_4596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
v___x_4597_ = l_Lean_MessageData_ofFormat(v___x_4596_);
lean_inc(v_ref_4586_);
v___x_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4598_, 0, v_ref_4586_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4598_);
v___x_4600_ = v___x_4593_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4603_, lean_object* v_sz_4604_, lean_object* v_i_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4604_);
lean_dec(v_sz_4604_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4605_);
lean_dec(v_i_4605_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4603_, v_sz_boxed_4609_, v_i_boxed_4610_, v_b_4606_, v___y_4607_);
lean_dec_ref(v___y_4607_);
lean_dec_ref(v_as_4603_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4612_, lean_object* v_entries_4613_, lean_object* v_____r_4614_, uint8_t v_anyFailed_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; size_t v_sz_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v___x_4619_ = lean_box(0);
v_sz_4620_ = lean_array_size(v_errors_4612_);
v___x_4621_ = ((size_t)0ULL);
v___x_4622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4612_, v_sz_4620_, v___x_4621_, v___x_4619_, v___y_4616_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4631_; 
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v___x_4622_, 0);
lean_dec(v_unused_4632_);
v___x_4624_ = v___x_4622_;
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
else
{
lean_dec(v___x_4622_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4629_; 
v___x_4626_ = lean_box(v_anyFailed_4615_);
v___x_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4627_, 0, v_entries_4613_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4627_);
v___x_4629_ = v___x_4624_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_dec_ref(v_entries_4613_);
v_a_4633_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4622_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4622_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4641_, lean_object* v_entries_4642_, lean_object* v_____r_4643_, lean_object* v_anyFailed_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
uint8_t v_anyFailed_boxed_4648_; lean_object* v_res_4649_; 
v_anyFailed_boxed_4648_ = lean_unbox(v_anyFailed_4644_);
v_res_4649_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4641_, v_entries_4642_, v_____r_4643_, v_anyFailed_boxed_4648_, v___y_4645_, v___y_4646_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec_ref(v_errors_4641_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4650_, lean_object* v_env_4651_, lean_object* v_mod_4652_){
_start:
{
lean_object* v_a_4655_; lean_object* v_a_4659_; uint8_t v_anyFailed_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint16_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___y_4704_; lean_object* v_fileName_4720_; lean_object* v_fileMap_4721_; lean_object* v_currNamespace_4722_; lean_object* v_openDecls_4723_; lean_object* v_initHeartbeats_4724_; lean_object* v_maxHeartbeats_4725_; lean_object* v_quotContext_4726_; lean_object* v_currMacroScope_4727_; lean_object* v_cancelTk_x3f_4728_; lean_object* v_inheritedTraceOptions_4729_; lean_object* v_currRecDepth_4730_; lean_object* v_ref_4731_; uint8_t v_suppressElabErrors_4732_; uint8_t v_isRecordingDeps_4733_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; uint8_t v___y_4756_; lean_object* v_env_4777_; uint8_t v___x_4778_; uint8_t v___x_4779_; 
v_anyFailed_4676_ = 0;
v___x_4677_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4678_ = l_Lean_instInhabitedFileMap_default;
v___x_4679_ = l_Lean_Options_empty;
v___x_4680_ = lean_box(0);
v___x_4681_ = lean_box(0);
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4684_ = l_Lean_firstFrontendMacroScope;
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_box(0);
v___x_4687_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4688_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4689_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4690_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4691_ = lean_unsigned_to_nat(32u);
v___x_4692_ = lean_mk_empty_array_with_capacity(v___x_4691_);
lean_dec_ref(v___x_4692_);
v___x_4693_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4694_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4696_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4697_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4698_ = 1;
v___x_4699_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4700_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4700_, 0, v_env_4651_);
lean_ctor_set(v___x_4700_, 1, v___x_4688_);
lean_ctor_set(v___x_4700_, 2, v___x_4689_);
lean_ctor_set(v___x_4700_, 3, v___x_4690_);
lean_ctor_set(v___x_4700_, 4, v___x_4693_);
lean_ctor_set(v___x_4700_, 5, v___x_4694_);
lean_ctor_set(v___x_4700_, 6, v___x_4696_);
lean_ctor_set(v___x_4700_, 7, v___x_4697_);
lean_ctor_set(v___x_4700_, 8, v___x_4699_);
lean_ctor_set(v___x_4700_, 9, v___x_4695_);
v___x_4701_ = lean_io_get_num_heartbeats();
v___x_4702_ = lean_st_mk_ref(v___x_4700_);
v___x_4752_ = l_Lean_inheritedTraceOptions;
v___x_4753_ = lean_st_ref_get(v___x_4752_);
v___x_4754_ = lean_st_ref_get(v___x_4702_);
v_env_4777_ = lean_ctor_get(v___x_4754_, 0);
lean_inc_ref(v_env_4777_);
lean_dec(v___x_4754_);
v___x_4778_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4777_);
lean_dec_ref(v_env_4777_);
v___x_4779_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4779_ == 0)
{
if (v___x_4778_ == 0)
{
v___y_4756_ = v___x_4698_;
goto v___jp_4755_;
}
else
{
v_fileName_4720_ = v___x_4677_;
v_fileMap_4721_ = v___x_4678_;
v_currNamespace_4722_ = v___x_4680_;
v_openDecls_4723_ = v___x_4681_;
v_initHeartbeats_4724_ = v___x_4701_;
v_maxHeartbeats_4725_ = v___x_4683_;
v_quotContext_4726_ = v___x_4680_;
v_currMacroScope_4727_ = v___x_4684_;
v_cancelTk_x3f_4728_ = v___x_4685_;
v_inheritedTraceOptions_4729_ = v___x_4753_;
v_currRecDepth_4730_ = v___x_4682_;
v_ref_4731_ = v___x_4686_;
v_suppressElabErrors_4732_ = v_anyFailed_4676_;
v_isRecordingDeps_4733_ = v_anyFailed_4676_;
goto v___jp_4719_;
}
}
else
{
if (v___x_4778_ == 0)
{
v_fileName_4720_ = v___x_4677_;
v_fileMap_4721_ = v___x_4678_;
v_currNamespace_4722_ = v___x_4680_;
v_openDecls_4723_ = v___x_4681_;
v_initHeartbeats_4724_ = v___x_4701_;
v_maxHeartbeats_4725_ = v___x_4683_;
v_quotContext_4726_ = v___x_4680_;
v_currMacroScope_4727_ = v___x_4684_;
v_cancelTk_x3f_4728_ = v___x_4685_;
v_inheritedTraceOptions_4729_ = v___x_4753_;
v_currRecDepth_4730_ = v___x_4682_;
v_ref_4731_ = v___x_4686_;
v_suppressElabErrors_4732_ = v_anyFailed_4676_;
v_isRecordingDeps_4733_ = v_anyFailed_4676_;
goto v___jp_4719_;
}
else
{
v___y_4756_ = v_anyFailed_4676_;
goto v___jp_4755_;
}
}
v___jp_4654_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_mk_io_user_error(v_a_4655_);
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
v___jp_4658_:
{
if (lean_obj_tag(v_a_4659_) == 0)
{
lean_object* v_msg_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v_msg_4660_ = lean_ctor_get(v_a_4659_, 1);
lean_inc_ref(v_msg_4660_);
lean_dec_ref_known(v_a_4659_, 2);
v___x_4661_ = l_Lean_MessageData_toString(v_msg_4660_);
v___x_4662_ = lean_mk_io_user_error(v___x_4661_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
else
{
lean_object* v_id_4664_; lean_object* v___x_4665_; 
v_id_4664_ = lean_ctor_get(v_a_4659_, 0);
lean_inc(v_id_4664_);
lean_dec_ref_known(v_a_4659_, 2);
v___x_4665_ = l_Lean_InternalExceptionId_getName(v_id_4664_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
lean_dec(v_id_4664_);
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v___x_4667_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4668_ = 1;
v___x_4669_ = l_Lean_Name_toString(v_a_4666_, v___x_4668_);
v___x_4670_ = lean_string_append(v___x_4667_, v___x_4669_);
lean_dec_ref(v___x_4669_);
v_a_4655_ = v___x_4670_;
goto v___jp_4654_;
}
else
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
lean_dec_ref_known(v___x_4665_, 1);
v___x_4671_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4672_ = l_Nat_reprFast(v_id_4664_);
v___x_4673_ = lean_string_append(v___x_4671_, v___x_4672_);
lean_dec_ref(v___x_4672_);
v___x_4674_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4675_ = lean_string_append(v___x_4673_, v___x_4674_);
v_a_4655_ = v___x_4675_;
goto v___jp_4654_;
}
}
}
v___jp_4703_:
{
if (lean_obj_tag(v___y_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4717_; 
v_a_4705_ = lean_ctor_get(v___y_4704_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___y_4704_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4707_ = v___y_4704_;
v_isShared_4708_ = v_isSharedCheck_4717_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___y_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4717_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4709_; lean_object* v_fst_4710_; lean_object* v_snd_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4715_; 
v___x_4709_ = lean_st_ref_get(v___x_4702_);
lean_dec(v___x_4702_);
lean_dec(v___x_4709_);
v_fst_4710_ = lean_ctor_get(v_a_4705_, 0);
lean_inc(v_fst_4710_);
v_snd_4711_ = lean_ctor_get(v_a_4705_, 1);
lean_inc(v_snd_4711_);
lean_dec(v_a_4705_);
v___x_4712_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4712_, 0, v_fst_4710_);
v___x_4713_ = lean_unbox(v_snd_4711_);
lean_dec(v_snd_4711_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*1, v___x_4713_);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4712_);
v___x_4715_ = v___x_4707_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4712_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
else
{
lean_object* v_a_4718_; 
lean_dec(v___x_4702_);
v_a_4718_ = lean_ctor_get(v___y_4704_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___y_4704_, 1);
v_a_4659_ = v_a_4718_;
goto v___jp_4658_;
}
}
v___jp_4719_:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4734_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4728_);
lean_inc(v_currMacroScope_4727_);
lean_inc(v_quotContext_4726_);
lean_inc(v_maxHeartbeats_4725_);
lean_inc(v_openDecls_4723_);
lean_inc(v_currNamespace_4722_);
lean_inc_ref(v_fileMap_4721_);
lean_inc_ref(v_fileName_4720_);
v___x_4735_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4735_, 0, v_fileName_4720_);
lean_ctor_set(v___x_4735_, 1, v_fileMap_4721_);
lean_ctor_set(v___x_4735_, 2, v___x_4679_);
lean_ctor_set(v___x_4735_, 3, v___x_4734_);
lean_ctor_set(v___x_4735_, 4, v_currNamespace_4722_);
lean_ctor_set(v___x_4735_, 5, v_openDecls_4723_);
lean_ctor_set(v___x_4735_, 6, v_initHeartbeats_4724_);
lean_ctor_set(v___x_4735_, 7, v_maxHeartbeats_4725_);
lean_ctor_set(v___x_4735_, 8, v_quotContext_4726_);
lean_ctor_set(v___x_4735_, 9, v_currMacroScope_4727_);
lean_ctor_set(v___x_4735_, 10, v_cancelTk_x3f_4728_);
lean_ctor_set(v___x_4735_, 11, v_inheritedTraceOptions_4729_);
lean_inc(v_ref_4731_);
v___x_4736_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
lean_ctor_set(v___x_4736_, 1, v_currRecDepth_4730_);
lean_ctor_set(v___x_4736_, 2, v_ref_4731_);
lean_ctor_set_uint16(v___x_4736_, sizeof(void*)*3, v___x_4687_);
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*3 + 2, v_suppressElabErrors_4732_);
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*3 + 3, v_isRecordingDeps_4733_);
v___x_4737_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4736_, v___x_4702_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4739_, 0, v_sp_4650_);
lean_ctor_set(v___x_4739_, 1, v_mod_4652_);
v___x_4740_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4738_, v___x_4739_, v___x_4736_, v___x_4702_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v_entries_4742_; lean_object* v_errors_4743_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4740_, 1);
v_entries_4742_ = lean_ctor_get(v_a_4741_, 0);
lean_inc_ref(v_entries_4742_);
v_errors_4743_ = lean_ctor_get(v_a_4741_, 1);
lean_inc_ref(v_errors_4743_);
lean_dec(v_a_4741_);
v___x_4744_ = lean_array_get_size(v_errors_4743_);
v___x_4745_ = lean_nat_dec_eq(v___x_4744_, v___x_4682_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = lean_box(0);
v___x_4747_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4743_, v_entries_4742_, v___x_4746_, v___x_4698_, v___x_4736_, v___x_4702_);
lean_dec_ref_known(v___x_4736_, 3);
lean_dec_ref(v_errors_4743_);
v___y_4704_ = v___x_4747_;
goto v___jp_4703_;
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
v___x_4748_ = lean_box(0);
v___x_4749_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4743_, v_entries_4742_, v___x_4748_, v_anyFailed_4676_, v___x_4736_, v___x_4702_);
lean_dec_ref_known(v___x_4736_, 3);
lean_dec_ref(v_errors_4743_);
v___y_4704_ = v___x_4749_;
goto v___jp_4703_;
}
}
else
{
lean_object* v_a_4750_; 
lean_dec_ref_known(v___x_4736_, 3);
lean_dec(v___x_4702_);
v_a_4750_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4750_);
lean_dec_ref_known(v___x_4740_, 1);
v_a_4659_ = v_a_4750_;
goto v___jp_4658_;
}
}
else
{
lean_object* v_a_4751_; 
lean_dec_ref_known(v___x_4736_, 3);
lean_dec(v___x_4702_);
lean_dec(v_mod_4652_);
lean_dec(v_sp_4650_);
v_a_4751_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4751_);
lean_dec_ref_known(v___x_4737_, 1);
v_a_4659_ = v_a_4751_;
goto v___jp_4658_;
}
}
v___jp_4755_:
{
lean_object* v___x_4757_; lean_object* v_env_4758_; lean_object* v_nextMacroScope_4759_; lean_object* v_ngen_4760_; lean_object* v_auxDeclNGen_4761_; lean_object* v_traceState_4762_; lean_object* v_recordedDeps_4763_; lean_object* v_messages_4764_; lean_object* v_infoState_4765_; lean_object* v_snapshotTasks_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4775_; 
v___x_4757_ = lean_st_ref_take(v___x_4702_);
v_env_4758_ = lean_ctor_get(v___x_4757_, 0);
v_nextMacroScope_4759_ = lean_ctor_get(v___x_4757_, 1);
v_ngen_4760_ = lean_ctor_get(v___x_4757_, 2);
v_auxDeclNGen_4761_ = lean_ctor_get(v___x_4757_, 3);
v_traceState_4762_ = lean_ctor_get(v___x_4757_, 4);
v_recordedDeps_4763_ = lean_ctor_get(v___x_4757_, 6);
v_messages_4764_ = lean_ctor_get(v___x_4757_, 7);
v_infoState_4765_ = lean_ctor_get(v___x_4757_, 8);
v_snapshotTasks_4766_ = lean_ctor_get(v___x_4757_, 9);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; 
v_unused_4776_ = lean_ctor_get(v___x_4757_, 5);
lean_dec(v_unused_4776_);
v___x_4768_ = v___x_4757_;
v_isShared_4769_ = v_isSharedCheck_4775_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_snapshotTasks_4766_);
lean_inc(v_infoState_4765_);
lean_inc(v_messages_4764_);
lean_inc(v_recordedDeps_4763_);
lean_inc(v_traceState_4762_);
lean_inc(v_auxDeclNGen_4761_);
lean_inc(v_ngen_4760_);
lean_inc(v_nextMacroScope_4759_);
lean_inc(v_env_4758_);
lean_dec(v___x_4757_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4775_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4770_; lean_object* v___x_4772_; 
v___x_4770_ = l_Lean_Kernel_enableDiag(v_env_4758_, v___y_4756_);
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 5, v___x_4694_);
lean_ctor_set(v___x_4768_, 0, v___x_4770_);
v___x_4772_ = v___x_4768_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4770_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_nextMacroScope_4759_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_ngen_4760_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_auxDeclNGen_4761_);
lean_ctor_set(v_reuseFailAlloc_4774_, 4, v_traceState_4762_);
lean_ctor_set(v_reuseFailAlloc_4774_, 5, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4774_, 6, v_recordedDeps_4763_);
lean_ctor_set(v_reuseFailAlloc_4774_, 7, v_messages_4764_);
lean_ctor_set(v_reuseFailAlloc_4774_, 8, v_infoState_4765_);
lean_ctor_set(v_reuseFailAlloc_4774_, 9, v_snapshotTasks_4766_);
v___x_4772_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
lean_object* v___x_4773_; 
v___x_4773_ = lean_st_ref_put(v___x_4702_, v___x_4772_);
v_fileName_4720_ = v___x_4677_;
v_fileMap_4721_ = v___x_4678_;
v_currNamespace_4722_ = v___x_4680_;
v_openDecls_4723_ = v___x_4681_;
v_initHeartbeats_4724_ = v___x_4701_;
v_maxHeartbeats_4725_ = v___x_4683_;
v_quotContext_4726_ = v___x_4680_;
v_currMacroScope_4727_ = v___x_4684_;
v_cancelTk_x3f_4728_ = v___x_4685_;
v_inheritedTraceOptions_4729_ = v___x_4753_;
v_currRecDepth_4730_ = v___x_4682_;
v_ref_4731_ = v___x_4686_;
v_suppressElabErrors_4732_ = v_anyFailed_4676_;
v_isRecordingDeps_4733_ = v_anyFailed_4676_;
goto v___jp_4719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4780_, lean_object* v_env_4781_, lean_object* v_mod_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4780_, v_env_4781_, v_mod_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4785_, size_t v_sz_4786_, size_t v_i_4787_, lean_object* v_b_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4785_, v_sz_4786_, v_i_4787_, v_b_4788_, v___y_4789_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4793_, lean_object* v_sz_4794_, lean_object* v_i_4795_, lean_object* v_b_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
size_t v_sz_boxed_4800_; size_t v_i_boxed_4801_; lean_object* v_res_4802_; 
v_sz_boxed_4800_ = lean_unbox_usize(v_sz_4794_);
lean_dec(v_sz_4794_);
v_i_boxed_4801_ = lean_unbox_usize(v_i_4795_);
lean_dec(v_i_4795_);
v_res_4802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4793_, v_sz_boxed_4800_, v_i_boxed_4801_, v_b_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec_ref(v_as_4793_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4804_; 
v___x_4804_ = lean_enable_initializer_execution();
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4807_){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_compacted_region_free(v_region_4807_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4810_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4816_, lean_object* v_k_4817_, uint8_t v_v_4818_){
_start:
{
lean_object* v_map_4819_; uint8_t v_hasTrace_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4834_; 
v_map_4819_ = lean_ctor_get(v_o_4816_, 0);
v_hasTrace_4820_ = lean_ctor_get_uint8(v_o_4816_, sizeof(void*)*1);
v_isSharedCheck_4834_ = !lean_is_exclusive(v_o_4816_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4822_ = v_o_4816_;
v_isShared_4823_ = v_isSharedCheck_4834_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_map_4819_);
lean_dec(v_o_4816_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4834_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4824_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4824_, 0, v_v_4818_);
lean_inc(v_k_4817_);
v___x_4825_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4817_, v___x_4824_, v_map_4819_);
if (v_hasTrace_4820_ == 0)
{
lean_object* v___x_4826_; uint8_t v___x_4827_; lean_object* v___x_4829_; 
v___x_4826_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4827_ = l_Lean_Name_isPrefixOf(v___x_4826_, v_k_4817_);
lean_dec(v_k_4817_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4825_);
v___x_4829_ = v___x_4822_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4825_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_ctor_set_uint8(v___x_4829_, sizeof(void*)*1, v___x_4827_);
return v___x_4829_;
}
}
else
{
lean_object* v___x_4832_; 
lean_dec(v_k_4817_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4825_);
v___x_4832_ = v___x_4822_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4825_);
lean_ctor_set_uint8(v_reuseFailAlloc_4833_, sizeof(void*)*1, v_hasTrace_4820_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4835_, lean_object* v_k_4836_, lean_object* v_v_4837_){
_start:
{
uint8_t v_v_boxed_4838_; lean_object* v_res_4839_; 
v_v_boxed_4838_ = lean_unbox(v_v_4837_);
v_res_4839_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4835_, v_k_4836_, v_v_boxed_4838_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4840_){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; uint32_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4842_ = lean_unsigned_to_nat(80u);
v___x_4843_ = l_Lean_Json_pretty(v_s_4840_, v___x_4842_);
v___x_4844_ = 10;
v___x_4845_ = lean_string_push(v___x_4843_, v___x_4844_);
v___x_4846_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4847_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4850_, size_t v_sz_4851_, size_t v_i_4852_, lean_object* v_b_4853_){
_start:
{
uint8_t v___x_4855_; 
v___x_4855_ = lean_usize_dec_lt(v_i_4852_, v_sz_4851_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v_b_4853_);
return v___x_4856_;
}
else
{
lean_object* v___x_4857_; lean_object* v_a_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4857_ = lean_box(0);
v_a_4858_ = lean_array_uget_borrowed(v_as_4850_, v_i_4852_);
lean_inc(v_a_4858_);
v___x_4859_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4858_);
v___x_4860_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4859_);
if (lean_obj_tag(v___x_4860_) == 0)
{
size_t v___x_4861_; size_t v___x_4862_; 
lean_dec_ref_known(v___x_4860_, 1);
v___x_4861_ = ((size_t)1ULL);
v___x_4862_ = lean_usize_add(v_i_4852_, v___x_4861_);
v_i_4852_ = v___x_4862_;
v_b_4853_ = v___x_4857_;
goto _start;
}
else
{
return v___x_4860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4864_, lean_object* v_sz_4865_, lean_object* v_i_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_){
_start:
{
size_t v_sz_boxed_4869_; size_t v_i_boxed_4870_; lean_object* v_res_4871_; 
v_sz_boxed_4869_ = lean_unbox_usize(v_sz_4865_);
lean_dec(v_sz_4865_);
v_i_boxed_4870_ = lean_unbox_usize(v_i_4866_);
lean_dec(v_i_4866_);
v_res_4871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4864_, v_sz_boxed_4869_, v_i_boxed_4870_, v_b_4867_);
lean_dec_ref(v_as_4864_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4872_, size_t v_sz_4873_, size_t v_i_4874_, lean_object* v_bs_4875_){
_start:
{
uint8_t v_anyUnlocated_4876_; 
v_anyUnlocated_4876_ = lean_usize_dec_lt(v_i_4874_, v_sz_4873_);
if (v_anyUnlocated_4876_ == 0)
{
return v_bs_4875_;
}
else
{
lean_object* v___x_4877_; uint8_t v_anyFailed_4878_; lean_object* v_v_4879_; lean_object* v_bs_x27_4880_; lean_object* v___x_4881_; size_t v___x_4882_; size_t v___x_4883_; lean_object* v___x_4884_; 
v___x_4877_ = lean_unsigned_to_nat(0u);
v_anyFailed_4878_ = lean_nat_dec_eq(v___x_4872_, v___x_4877_);
v_v_4879_ = lean_array_uget(v_bs_4875_, v_i_4874_);
v_bs_x27_4880_ = lean_array_uset(v_bs_4875_, v_i_4874_, v___x_4877_);
v___x_4881_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4881_, 0, v_v_4879_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*1, v_anyFailed_4878_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*1 + 1, v_anyUnlocated_4876_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*1 + 2, v_anyFailed_4878_);
v___x_4882_ = ((size_t)1ULL);
v___x_4883_ = lean_usize_add(v_i_4874_, v___x_4882_);
v___x_4884_ = lean_array_uset(v_bs_x27_4880_, v_i_4874_, v___x_4881_);
v_i_4874_ = v___x_4883_;
v_bs_4875_ = v___x_4884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4886_, lean_object* v_sz_4887_, lean_object* v_i_4888_, lean_object* v_bs_4889_){
_start:
{
size_t v_sz_boxed_4890_; size_t v_i_boxed_4891_; lean_object* v_res_4892_; 
v_sz_boxed_4890_ = lean_unbox_usize(v_sz_4887_);
lean_dec(v_sz_4887_);
v_i_boxed_4891_ = lean_unbox_usize(v_i_4888_);
lean_dec(v_i_4888_);
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4886_, v_sz_boxed_4890_, v_i_boxed_4891_, v_bs_4889_);
lean_dec(v___x_4886_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4893_, size_t v_i_4894_, size_t v_stop_4895_, lean_object* v_b_4896_){
_start:
{
uint8_t v___x_4897_; 
v___x_4897_ = lean_usize_dec_eq(v_i_4894_, v_stop_4895_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; lean_object* v_fst_4899_; lean_object* v_snd_4900_; uint8_t v___x_4901_; lean_object* v___x_4902_; size_t v___x_4903_; size_t v___x_4904_; 
v___x_4898_ = lean_array_uget_borrowed(v_as_4893_, v_i_4894_);
v_fst_4899_ = lean_ctor_get(v___x_4898_, 0);
v_snd_4900_ = lean_ctor_get(v___x_4898_, 1);
v___x_4901_ = lean_unbox(v_snd_4900_);
lean_inc(v_fst_4899_);
v___x_4902_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4896_, v_fst_4899_, v___x_4901_);
v___x_4903_ = ((size_t)1ULL);
v___x_4904_ = lean_usize_add(v_i_4894_, v___x_4903_);
v_i_4894_ = v___x_4904_;
v_b_4896_ = v___x_4902_;
goto _start;
}
else
{
return v_b_4896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4906_, lean_object* v_i_4907_, lean_object* v_stop_4908_, lean_object* v_b_4909_){
_start:
{
size_t v_i_boxed_4910_; size_t v_stop_boxed_4911_; lean_object* v_res_4912_; 
v_i_boxed_4910_ = lean_unbox_usize(v_i_4907_);
lean_dec(v_i_4907_);
v_stop_boxed_4911_ = lean_unbox_usize(v_stop_4908_);
lean_dec(v_stop_4908_);
v_res_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4906_, v_i_boxed_4910_, v_stop_boxed_4911_, v_b_4909_);
lean_dec_ref(v_as_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4922_, lean_object* v_checkImports_4923_, lean_object* v_args_4924_, lean_object* v___x_4925_, lean_object* v_as_4926_, size_t v_sz_4927_, size_t v_i_4928_, lean_object* v_b_4929_){
_start:
{
lean_object* v_a_4932_; lean_object* v___x_4936_; uint8_t v_anyFailed_4937_; uint8_t v_anyUnlocated_4938_; lean_object* v___x_4939_; lean_object* v_envLinterModule_4940_; uint8_t v___x_4941_; 
v___x_4936_ = lean_unsigned_to_nat(0u);
v_anyFailed_4937_ = lean_nat_dec_eq(v___x_4922_, v___x_4936_);
v_anyUnlocated_4938_ = 1;
v___x_4939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4940_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4940_, 0, v___x_4939_);
lean_ctor_set_uint8(v_envLinterModule_4940_, sizeof(void*)*1, v_anyFailed_4937_);
lean_ctor_set_uint8(v_envLinterModule_4940_, sizeof(void*)*1 + 1, v_anyUnlocated_4938_);
lean_ctor_set_uint8(v_envLinterModule_4940_, sizeof(void*)*1 + 2, v_anyFailed_4937_);
v___x_4941_ = lean_usize_dec_lt(v_i_4928_, v_sz_4927_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref_known(v_envLinterModule_4940_, 1);
lean_dec(v___x_4925_);
v___x_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4942_, 0, v_b_4929_);
return v___x_4942_;
}
else
{
lean_object* v_snd_4943_; lean_object* v_snd_4944_; lean_object* v_snd_4945_; lean_object* v_snd_4946_; lean_object* v_fst_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_5260_; 
v_snd_4943_ = lean_ctor_get(v_b_4929_, 1);
lean_inc(v_snd_4943_);
v_snd_4944_ = lean_ctor_get(v_snd_4943_, 1);
lean_inc(v_snd_4944_);
v_snd_4945_ = lean_ctor_get(v_snd_4944_, 1);
lean_inc(v_snd_4945_);
v_snd_4946_ = lean_ctor_get(v_snd_4945_, 1);
lean_inc(v_snd_4946_);
v_fst_4947_ = lean_ctor_get(v_b_4929_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v_b_4929_);
if (v_isSharedCheck_5260_ == 0)
{
lean_object* v_unused_5261_; 
v_unused_5261_ = lean_ctor_get(v_b_4929_, 1);
lean_dec(v_unused_5261_);
v___x_4949_ = v_b_4929_;
v_isShared_4950_ = v_isSharedCheck_5260_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_fst_4947_);
lean_dec(v_b_4929_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_5260_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v_fst_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_5258_; 
v_fst_4951_ = lean_ctor_get(v_snd_4943_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_snd_4943_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_snd_4943_, 1);
lean_dec(v_unused_5259_);
v___x_4953_ = v_snd_4943_;
v_isShared_4954_ = v_isSharedCheck_5258_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_fst_4951_);
lean_dec(v_snd_4943_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_5258_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v_fst_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_5256_; 
v_fst_4955_ = lean_ctor_get(v_snd_4944_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_snd_4944_);
if (v_isSharedCheck_5256_ == 0)
{
lean_object* v_unused_5257_; 
v_unused_5257_ = lean_ctor_get(v_snd_4944_, 1);
lean_dec(v_unused_5257_);
v___x_4957_ = v_snd_4944_;
v_isShared_4958_ = v_isSharedCheck_5256_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_fst_4955_);
lean_dec(v_snd_4944_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_5256_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v_fst_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_5254_; 
v_fst_4959_ = lean_ctor_get(v_snd_4945_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v_snd_4945_);
if (v_isSharedCheck_5254_ == 0)
{
lean_object* v_unused_5255_; 
v_unused_5255_ = lean_ctor_get(v_snd_4945_, 1);
lean_dec(v_unused_5255_);
v___x_4961_ = v_snd_4945_;
v_isShared_4962_ = v_isSharedCheck_5254_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_fst_4959_);
lean_dec(v_snd_4945_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_5254_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v_fst_4963_; lean_object* v_snd_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5253_; 
v_fst_4963_ = lean_ctor_get(v_snd_4946_, 0);
v_snd_4964_ = lean_ctor_get(v_snd_4946_, 1);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_snd_4946_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_4966_ = v_snd_4946_;
v_isShared_4967_ = v_isSharedCheck_5253_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_snd_4964_);
lean_inc(v_fst_4963_);
lean_dec(v_snd_4946_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5253_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; lean_object* v_a_4969_; lean_object* v___y_4971_; lean_object* v___y_4972_; uint8_t v_anyFailed_4973_; uint8_t v_anyUnlocated_4974_; lean_object* v_records_4975_; lean_object* v_codeQualityEntries_4976_; lean_object* v___y_5123_; lean_object* v___y_5124_; uint8_t v_anyFailed_5125_; uint8_t v_anyUnlocated_5126_; lean_object* v_records_5127_; lean_object* v_codeQualityEntries_5128_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_4968_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_4969_ = lean_array_uget_borrowed(v_as_4926_, v_i_4928_);
v___x_5186_ = lean_enable_initializer_execution();
lean_inc(v_a_4969_);
v___x_5187_ = l_Lean_findOLean(v_a_4969_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5189_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref_known(v___x_5187_, 1);
v___x_5189_ = l_Lean_readModuleData(v_a_5188_);
lean_dec(v_a_5188_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v_fst_5191_; lean_object* v_snd_5192_; uint8_t v___x_5193_; uint8_t v___y_5195_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___x_5189_, 1);
v_fst_5191_ = lean_ctor_get(v_a_5190_, 0);
lean_inc(v_fst_5191_);
v_snd_5192_ = lean_ctor_get(v_a_5190_, 1);
lean_inc(v_snd_5192_);
lean_dec(v_a_5190_);
v___x_5193_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5191_);
lean_dec(v_fst_5191_);
if (v___x_5193_ == 0)
{
uint8_t v___x_5235_; 
v___x_5235_ = 2;
v___y_5195_ = v___x_5235_;
goto v___jp_5194_;
}
else
{
uint8_t v___x_5236_; 
v___x_5236_ = 1;
v___y_5195_ = v___x_5236_;
goto v___jp_5194_;
}
v___jp_5194_:
{
lean_object* v___x_5196_; 
v___x_5196_ = lean_compacted_region_free(v_snd_5192_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; uint32_t v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
lean_dec_ref_known(v___x_5196_, 1);
lean_inc(v_a_4969_);
v___x_5197_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5197_, 0, v_a_4969_);
lean_ctor_set_uint8(v___x_5197_, sizeof(void*)*1, v_anyFailed_4937_);
lean_ctor_set_uint8(v___x_5197_, sizeof(void*)*1 + 1, v_anyUnlocated_4938_);
lean_ctor_set_uint8(v___x_5197_, sizeof(void*)*1 + 2, v_anyFailed_4937_);
v___x_5198_ = lean_unsigned_to_nat(2u);
v___x_5199_ = lean_mk_empty_array_with_capacity(v___x_5198_);
v___x_5200_ = lean_array_push(v___x_5199_, v___x_5197_);
v___x_5201_ = lean_array_push(v___x_5200_, v_envLinterModule_4940_);
v___x_5202_ = l_Array_append___redArg(v___x_5201_, v_checkImports_4923_);
v___x_5203_ = l_Lean_Options_empty;
v___x_5204_ = 1024;
v___x_5205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5206_ = lean_box(1);
v___x_5207_ = l_Lean_importModules(v___x_5202_, v___x_5203_, v___x_5204_, v___x_5205_, v_anyFailed_4937_, v_anyUnlocated_4938_, v___y_5195_, v___x_5206_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v_linterOverrides_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v_linterOverrides_5209_ = lean_ctor_get(v_args_4924_, 0);
v___x_5210_ = lean_array_get_size(v_linterOverrides_5209_);
v___x_5211_ = lean_nat_dec_lt(v___x_4936_, v___x_5210_);
if (v___x_5211_ == 0)
{
v___y_5146_ = v_a_5208_;
v___y_5147_ = v___x_5203_;
goto v___jp_5145_;
}
else
{
uint8_t v___x_5212_; 
v___x_5212_ = lean_nat_dec_le(v___x_5210_, v___x_5210_);
if (v___x_5212_ == 0)
{
if (v___x_5211_ == 0)
{
v___y_5146_ = v_a_5208_;
v___y_5147_ = v___x_5203_;
goto v___jp_5145_;
}
else
{
size_t v___x_5213_; size_t v___x_5214_; lean_object* v___x_5215_; 
v___x_5213_ = ((size_t)0ULL);
v___x_5214_ = lean_usize_of_nat(v___x_5210_);
v___x_5215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5209_, v___x_5213_, v___x_5214_, v___x_5203_);
v___y_5146_ = v_a_5208_;
v___y_5147_ = v___x_5215_;
goto v___jp_5145_;
}
}
else
{
size_t v___x_5216_; size_t v___x_5217_; lean_object* v___x_5218_; 
v___x_5216_ = ((size_t)0ULL);
v___x_5217_ = lean_usize_of_nat(v___x_5210_);
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5209_, v___x_5216_, v___x_5217_, v___x_5203_);
v___y_5146_ = v_a_5208_;
v___y_5147_ = v___x_5218_;
goto v___jp_5145_;
}
}
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4959_);
lean_del_object(v___x_4957_);
lean_dec(v_fst_4955_);
lean_del_object(v___x_4953_);
lean_dec(v_fst_4951_);
lean_del_object(v___x_4949_);
lean_dec(v_fst_4947_);
lean_dec(v___x_4925_);
v_a_5219_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5207_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5207_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5234_; 
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4959_);
lean_del_object(v___x_4957_);
lean_dec(v_fst_4955_);
lean_del_object(v___x_4953_);
lean_dec(v_fst_4951_);
lean_del_object(v___x_4949_);
lean_dec(v_fst_4947_);
lean_dec_ref_known(v_envLinterModule_4940_, 1);
lean_dec(v___x_4925_);
v_a_5227_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5196_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5196_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4959_);
lean_del_object(v___x_4957_);
lean_dec(v_fst_4955_);
lean_del_object(v___x_4953_);
lean_dec(v_fst_4951_);
lean_del_object(v___x_4949_);
lean_dec(v_fst_4947_);
lean_dec_ref_known(v_envLinterModule_4940_, 1);
lean_dec(v___x_4925_);
v_a_5237_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5189_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5189_);
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
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4959_);
lean_del_object(v___x_4957_);
lean_dec(v_fst_4955_);
lean_del_object(v___x_4953_);
lean_dec(v_fst_4951_);
lean_del_object(v___x_4949_);
lean_dec(v_fst_4947_);
lean_dec_ref_known(v_envLinterModule_4940_, 1);
lean_dec(v___x_4925_);
v_a_5245_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5187_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5187_);
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
v___jp_4970_:
{
uint8_t v_mode_4977_; uint8_t v___x_4978_; uint8_t v___x_4979_; 
v_mode_4977_ = lean_ctor_get_uint8(v_args_4924_, sizeof(void*)*4 + 1);
v___x_4978_ = 2;
v___x_4979_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4977_, v___x_4978_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = l_Lean_Name_getRoot(v_a_4969_);
lean_inc(v___x_4925_);
v___x_4981_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4924_, v___y_4972_, v___x_4925_, v___y_4971_, v___x_4980_, v_fst_4963_);
lean_dec_ref(v___y_4972_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v_outcome_4983_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v_outcome_4983_ = lean_ctor_get(v_a_4982_, 0);
if (lean_obj_tag(v_outcome_4983_) == 0)
{
uint8_t v_failed_4984_; 
v_failed_4984_ = lean_ctor_get_uint8(v_outcome_4983_, 0);
if (v_failed_4984_ == 0)
{
lean_object* v_checkedModules_4985_; lean_object* v___x_4987_; 
v_checkedModules_4985_ = lean_ctor_get(v_a_4982_, 1);
lean_inc(v_checkedModules_4985_);
lean_dec(v_a_4982_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v_checkedModules_4985_);
v___x_4987_ = v___x_4966_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_checkedModules_4985_);
lean_ctor_set(v_reuseFailAlloc_5002_, 1, v_snd_4964_);
v___x_4987_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4989_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_4987_);
lean_ctor_set(v___x_4961_, 0, v_codeQualityEntries_4976_);
v___x_4989_ = v___x_4961_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_codeQualityEntries_4976_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4991_; 
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_4989_);
lean_ctor_set(v___x_4957_, 0, v_records_4975_);
v___x_4991_ = v___x_4957_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_records_4975_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4992_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_4991_);
lean_ctor_set(v___x_4953_, 0, v___x_4992_);
v___x_4994_ = v___x_4953_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___x_4991_);
v___x_4994_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; lean_object* v___x_4997_; 
v___x_4995_ = lean_box(v_anyFailed_4973_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___x_4994_);
lean_ctor_set(v___x_4949_, 0, v___x_4995_);
v___x_4997_ = v___x_4949_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4995_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v___x_4994_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
v_a_4932_ = v___x_4997_;
goto v___jp_4931_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5003_; lean_object* v___x_5005_; 
v_checkedModules_5003_ = lean_ctor_get(v_a_4982_, 1);
lean_inc(v_checkedModules_5003_);
lean_dec(v_a_4982_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v_checkedModules_5003_);
v___x_5005_ = v___x_4966_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_checkedModules_5003_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v_snd_4964_);
v___x_5005_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5007_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5005_);
lean_ctor_set(v___x_4961_, 0, v_codeQualityEntries_4976_);
v___x_5007_ = v___x_4961_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_codeQualityEntries_4976_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5009_; 
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_5007_);
lean_ctor_set(v___x_4957_, 0, v_records_4975_);
v___x_5009_ = v___x_4957_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_records_4975_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_5009_);
lean_ctor_set(v___x_4953_, 0, v___x_5010_);
v___x_5012_ = v___x_4953_;
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
v___x_5013_ = lean_box(v_anyUnlocated_4938_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___x_5012_);
lean_ctor_set(v___x_4949_, 0, v___x_5013_);
v___x_5015_ = v___x_4949_;
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
v_a_4932_ = v___x_5015_;
goto v___jp_4931_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5021_; lean_object* v_records_5022_; uint8_t v_unlocated_5023_; lean_object* v___x_5024_; 
lean_inc_ref(v_outcome_4983_);
v_checkedModules_5021_ = lean_ctor_get(v_a_4982_, 1);
lean_inc(v_checkedModules_5021_);
lean_dec(v_a_4982_);
v_records_5022_ = lean_ctor_get(v_outcome_4983_, 0);
lean_inc_ref(v_records_5022_);
v_unlocated_5023_ = lean_ctor_get_uint8(v_outcome_4983_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4983_, 1);
v___x_5024_ = l_Array_append___redArg(v_records_4975_, v_records_5022_);
lean_dec_ref(v_records_5022_);
if (v_unlocated_5023_ == 0)
{
lean_object* v___x_5026_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v_checkedModules_5021_);
v___x_5026_ = v___x_4966_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_checkedModules_5021_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v_snd_4964_);
v___x_5026_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
lean_object* v___x_5028_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5026_);
lean_ctor_set(v___x_4961_, 0, v_codeQualityEntries_4976_);
v___x_5028_ = v___x_4961_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_codeQualityEntries_4976_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
lean_object* v___x_5030_; 
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_5028_);
lean_ctor_set(v___x_4957_, 0, v___x_5024_);
v___x_5030_ = v___x_4957_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5031_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_5030_);
lean_ctor_set(v___x_4953_, 0, v___x_5031_);
v___x_5033_ = v___x_4953_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5031_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5030_);
v___x_5033_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = lean_box(v_anyFailed_4973_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___x_5033_);
lean_ctor_set(v___x_4949_, 0, v___x_5034_);
v___x_5036_ = v___x_4949_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5033_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
v_a_4932_ = v___x_5036_;
goto v___jp_4931_;
}
}
}
}
}
}
else
{
lean_object* v___x_5043_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v_checkedModules_5021_);
v___x_5043_ = v___x_4966_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_checkedModules_5021_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v_snd_4964_);
v___x_5043_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5045_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5043_);
lean_ctor_set(v___x_4961_, 0, v_codeQualityEntries_4976_);
v___x_5045_ = v___x_4961_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_codeQualityEntries_4976_);
lean_ctor_set(v_reuseFailAlloc_5057_, 1, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5047_; 
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_5045_);
lean_ctor_set(v___x_4957_, 0, v___x_5024_);
v___x_5047_ = v___x_4957_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
lean_object* v___x_5048_; lean_object* v___x_5050_; 
v___x_5048_ = lean_box(v_anyUnlocated_4938_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_5047_);
lean_ctor_set(v___x_4953_, 0, v___x_5048_);
v___x_5050_ = v___x_4953_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5048_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5047_);
v___x_5050_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5051_; lean_object* v___x_5053_; 
v___x_5051_ = lean_box(v_anyFailed_4973_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 1, v___x_5050_);
lean_ctor_set(v___x_4949_, 0, v___x_5051_);
v___x_5053_ = v___x_4949_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5051_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5050_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
v_a_4932_ = v___x_5053_;
goto v___jp_4931_;
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
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec_ref(v_codeQualityEntries_4976_);
lean_dec_ref(v_records_4975_);
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_del_object(v___x_4961_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_del_object(v___x_4949_);
lean_dec(v___x_4925_);
v_a_5059_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_4981_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_4981_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v___x_5067_; lean_object* v_fst_5068_; lean_object* v_snd_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5121_; 
lean_del_object(v___x_4949_);
v___x_5067_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4924_, v___y_4972_, v___y_4971_, v_a_4969_, v_snd_4964_);
lean_dec_ref(v___y_4972_);
v_fst_5068_ = lean_ctor_get(v___x_5067_, 0);
v_snd_5069_ = lean_ctor_get(v___x_5067_, 1);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5071_ = v___x_5067_;
v_isShared_5072_ = v_isSharedCheck_5121_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_snd_5069_);
lean_inc(v_fst_5068_);
lean_dec(v___x_5067_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5121_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = l_Array_append___redArg(v_codeQualityEntries_4976_, v_fst_5068_);
lean_dec(v_fst_5068_);
lean_inc(v_a_4969_);
lean_inc(v___x_4925_);
v___x_5074_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4925_, v___y_4971_, v_a_4969_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v_entries_5076_; uint8_t v_failed_5077_; lean_object* v___x_5078_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5074_, 1);
v_entries_5076_ = lean_ctor_get(v_a_5075_, 0);
lean_inc_ref(v_entries_5076_);
v_failed_5077_ = lean_ctor_get_uint8(v_a_5075_, sizeof(void*)*1);
lean_dec(v_a_5075_);
v___x_5078_ = l_Array_append___redArg(v___x_5073_, v_entries_5076_);
lean_dec_ref(v_entries_5076_);
if (v_failed_5077_ == 0)
{
lean_object* v___x_5080_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v_fst_4963_);
v___x_5080_ = v___x_5071_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_fst_4963_);
lean_ctor_set(v_reuseFailAlloc_5095_, 1, v_snd_5069_);
v___x_5080_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5082_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 1, v___x_5080_);
lean_ctor_set(v___x_4966_, 0, v___x_5078_);
v___x_5082_ = v___x_4966_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___x_5084_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5082_);
lean_ctor_set(v___x_4961_, 0, v_records_4975_);
v___x_5084_ = v___x_4961_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_records_4975_);
lean_ctor_set(v_reuseFailAlloc_5093_, 1, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5085_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_5084_);
lean_ctor_set(v___x_4957_, 0, v___x_5085_);
v___x_5087_ = v___x_4957_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5085_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v___x_5084_);
v___x_5087_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5088_; lean_object* v___x_5090_; 
v___x_5088_ = lean_box(v_anyFailed_4973_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_5087_);
lean_ctor_set(v___x_4953_, 0, v___x_5088_);
v___x_5090_ = v___x_4953_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5088_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5087_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
v_a_4932_ = v___x_5090_;
goto v___jp_4931_;
}
}
}
}
}
}
else
{
lean_object* v___x_5097_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v_fst_4963_);
v___x_5097_ = v___x_5071_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_fst_4963_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_snd_5069_);
v___x_5097_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
lean_object* v___x_5099_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 1, v___x_5097_);
lean_ctor_set(v___x_4966_, 0, v___x_5078_);
v___x_5099_ = v___x_4966_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v___x_5097_);
v___x_5099_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5101_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5099_);
lean_ctor_set(v___x_4961_, 0, v_records_4975_);
v___x_5101_ = v___x_4961_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_records_4975_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v___x_5099_);
v___x_5101_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5102_; lean_object* v___x_5104_; 
v___x_5102_ = lean_box(v_anyUnlocated_4974_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 1, v___x_5101_);
lean_ctor_set(v___x_4957_, 0, v___x_5102_);
v___x_5104_ = v___x_4957_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5102_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5101_);
v___x_5104_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5105_; lean_object* v___x_5107_; 
v___x_5105_ = lean_box(v_anyUnlocated_4938_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_5104_);
lean_ctor_set(v___x_4953_, 0, v___x_5105_);
v___x_5107_ = v___x_4953_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___x_5104_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
v_a_4932_ = v___x_5107_;
goto v___jp_4931_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec_ref(v___x_5073_);
lean_del_object(v___x_5071_);
lean_dec(v_snd_5069_);
lean_dec_ref(v_records_4975_);
lean_del_object(v___x_4966_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_dec(v___x_4925_);
v_a_5113_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5074_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5074_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
}
}
v___jp_5122_:
{
lean_object* v___x_5129_; 
lean_inc(v_a_4969_);
lean_inc_ref(v___y_5123_);
lean_inc(v___x_4925_);
lean_inc_ref(v___y_5124_);
v___x_5129_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4924_, v___y_5124_, v___x_4925_, v___y_5123_, v_a_4969_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
switch(lean_obj_tag(v_a_5130_))
{
case 0:
{
uint8_t v_failed_5131_; 
v_failed_5131_ = lean_ctor_get_uint8(v_a_5130_, 0);
lean_dec_ref_known(v_a_5130_, 0);
if (v_failed_5131_ == 0)
{
v___y_4971_ = v___y_5123_;
v___y_4972_ = v___y_5124_;
v_anyFailed_4973_ = v_anyFailed_5125_;
v_anyUnlocated_4974_ = v_anyUnlocated_5126_;
v_records_4975_ = v_records_5127_;
v_codeQualityEntries_4976_ = v_codeQualityEntries_5128_;
goto v___jp_4970_;
}
else
{
v___y_4971_ = v___y_5123_;
v___y_4972_ = v___y_5124_;
v_anyFailed_4973_ = v_anyUnlocated_4938_;
v_anyUnlocated_4974_ = v_anyUnlocated_5126_;
v_records_4975_ = v_records_5127_;
v_codeQualityEntries_4976_ = v_codeQualityEntries_5128_;
goto v___jp_4970_;
}
}
case 1:
{
lean_object* v_records_5132_; uint8_t v_unlocated_5133_; lean_object* v___x_5134_; 
v_records_5132_ = lean_ctor_get(v_a_5130_, 0);
lean_inc_ref(v_records_5132_);
v_unlocated_5133_ = lean_ctor_get_uint8(v_a_5130_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5130_, 1);
v___x_5134_ = l_Array_append___redArg(v_records_5127_, v_records_5132_);
lean_dec_ref(v_records_5132_);
if (v_unlocated_5133_ == 0)
{
v___y_4971_ = v___y_5123_;
v___y_4972_ = v___y_5124_;
v_anyFailed_4973_ = v_anyFailed_5125_;
v_anyUnlocated_4974_ = v_anyUnlocated_5126_;
v_records_4975_ = v___x_5134_;
v_codeQualityEntries_4976_ = v_codeQualityEntries_5128_;
goto v___jp_4970_;
}
else
{
v___y_4971_ = v___y_5123_;
v___y_4972_ = v___y_5124_;
v_anyFailed_4973_ = v_anyFailed_5125_;
v_anyUnlocated_4974_ = v_anyUnlocated_4938_;
v_records_4975_ = v___x_5134_;
v_codeQualityEntries_4976_ = v_codeQualityEntries_5128_;
goto v___jp_4970_;
}
}
default: 
{
lean_object* v_entries_5135_; lean_object* v___x_5136_; 
v_entries_5135_ = lean_ctor_get(v_a_5130_, 0);
lean_inc_ref(v_entries_5135_);
lean_dec_ref_known(v_a_5130_, 1);
v___x_5136_ = l_Array_append___redArg(v_codeQualityEntries_5128_, v_entries_5135_);
lean_dec_ref(v_entries_5135_);
v___y_4971_ = v___y_5123_;
v___y_4972_ = v___y_5124_;
v_anyFailed_4973_ = v_anyFailed_5125_;
v_anyUnlocated_4974_ = v_anyUnlocated_5126_;
v_records_4975_ = v_records_5127_;
v_codeQualityEntries_4976_ = v___x_5136_;
goto v___jp_4970_;
}
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec_ref(v_codeQualityEntries_5128_);
lean_dec_ref(v_records_5127_);
lean_dec_ref(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_del_object(v___x_4957_);
lean_del_object(v___x_4953_);
lean_del_object(v___x_4949_);
lean_dec(v___x_4925_);
v_a_5137_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5129_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5129_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
v___jp_5145_:
{
lean_object* v___x_5148_; lean_object* v_toEnvExtension_5149_; lean_object* v_asyncMode_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v_merged_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5184_; 
v___x_5148_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5149_ = lean_ctor_get(v___x_5148_, 0);
v_asyncMode_5150_ = lean_ctor_get(v_toEnvExtension_5149_, 2);
v___x_5151_ = lean_box(0);
lean_inc_ref(v___y_5146_);
v___x_5152_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4968_, v___x_5148_, v___y_5146_, v_asyncMode_5150_, v___x_5151_);
v_merged_5153_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5184_ == 0)
{
lean_object* v_unused_5185_; 
v_unused_5185_ = lean_ctor_get(v___x_5152_, 1);
lean_dec(v_unused_5185_);
v___x_5155_ = v___x_5152_;
v_isShared_5156_ = v_isSharedCheck_5184_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_merged_5153_);
lean_dec(v___x_5152_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5184_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 1, v_merged_5153_);
lean_ctor_set(v___x_5155_, 0, v___y_5147_);
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___y_5147_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v_merged_5153_);
v___x_5158_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4924_, v___x_5158_, v___y_5146_, v_a_4969_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
switch(lean_obj_tag(v_a_5160_))
{
case 0:
{
uint8_t v___x_5161_; 
v___x_5161_ = lean_unbox(v_fst_4947_);
lean_dec(v_fst_4947_);
if (v___x_5161_ == 0)
{
uint8_t v_failed_5162_; uint8_t v___x_5163_; 
v_failed_5162_ = lean_ctor_get_uint8(v_a_5160_, 0);
lean_dec_ref_known(v_a_5160_, 0);
v___x_5163_ = lean_unbox(v_fst_4951_);
lean_dec(v_fst_4951_);
v___y_5123_ = v___y_5146_;
v___y_5124_ = v___x_5158_;
v_anyFailed_5125_ = v_failed_5162_;
v_anyUnlocated_5126_ = v___x_5163_;
v_records_5127_ = v_fst_4955_;
v_codeQualityEntries_5128_ = v_fst_4959_;
goto v___jp_5122_;
}
else
{
uint8_t v___x_5164_; 
lean_dec_ref_known(v_a_5160_, 0);
v___x_5164_ = lean_unbox(v_fst_4951_);
lean_dec(v_fst_4951_);
v___y_5123_ = v___y_5146_;
v___y_5124_ = v___x_5158_;
v_anyFailed_5125_ = v_anyUnlocated_4938_;
v_anyUnlocated_5126_ = v___x_5164_;
v_records_5127_ = v_fst_4955_;
v_codeQualityEntries_5128_ = v_fst_4959_;
goto v___jp_5122_;
}
}
case 1:
{
lean_object* v_records_5165_; uint8_t v_unlocated_5166_; lean_object* v___x_5167_; 
v_records_5165_ = lean_ctor_get(v_a_5160_, 0);
lean_inc_ref(v_records_5165_);
v_unlocated_5166_ = lean_ctor_get_uint8(v_a_5160_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5160_, 1);
v___x_5167_ = l_Array_append___redArg(v_fst_4955_, v_records_5165_);
lean_dec_ref(v_records_5165_);
if (v_unlocated_5166_ == 0)
{
uint8_t v___x_5168_; uint8_t v___x_5169_; 
v___x_5168_ = lean_unbox(v_fst_4947_);
lean_dec(v_fst_4947_);
v___x_5169_ = lean_unbox(v_fst_4951_);
lean_dec(v_fst_4951_);
v___y_5123_ = v___y_5146_;
v___y_5124_ = v___x_5158_;
v_anyFailed_5125_ = v___x_5168_;
v_anyUnlocated_5126_ = v___x_5169_;
v_records_5127_ = v___x_5167_;
v_codeQualityEntries_5128_ = v_fst_4959_;
goto v___jp_5122_;
}
else
{
uint8_t v___x_5170_; 
lean_dec(v_fst_4951_);
v___x_5170_ = lean_unbox(v_fst_4947_);
lean_dec(v_fst_4947_);
v___y_5123_ = v___y_5146_;
v___y_5124_ = v___x_5158_;
v_anyFailed_5125_ = v___x_5170_;
v_anyUnlocated_5126_ = v_anyUnlocated_4938_;
v_records_5127_ = v___x_5167_;
v_codeQualityEntries_5128_ = v_fst_4959_;
goto v___jp_5122_;
}
}
default: 
{
lean_object* v_entries_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; uint8_t v___x_5174_; 
v_entries_5171_ = lean_ctor_get(v_a_5160_, 0);
lean_inc_ref(v_entries_5171_);
lean_dec_ref_known(v_a_5160_, 1);
v___x_5172_ = l_Array_append___redArg(v_fst_4959_, v_entries_5171_);
lean_dec_ref(v_entries_5171_);
v___x_5173_ = lean_unbox(v_fst_4947_);
lean_dec(v_fst_4947_);
v___x_5174_ = lean_unbox(v_fst_4951_);
lean_dec(v_fst_4951_);
v___y_5123_ = v___y_5146_;
v___y_5124_ = v___x_5158_;
v_anyFailed_5125_ = v___x_5173_;
v_anyUnlocated_5126_ = v___x_5174_;
v_records_5127_ = v_fst_4955_;
v_codeQualityEntries_5128_ = v___x_5172_;
goto v___jp_5122_;
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___y_5146_);
lean_del_object(v___x_4966_);
lean_dec(v_snd_4964_);
lean_dec(v_fst_4963_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4959_);
lean_del_object(v___x_4957_);
lean_dec(v_fst_4955_);
lean_del_object(v___x_4953_);
lean_dec(v_fst_4951_);
lean_del_object(v___x_4949_);
lean_dec(v_fst_4947_);
lean_dec(v___x_4925_);
v_a_5175_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5159_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5159_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
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
v___jp_4931_:
{
size_t v___x_4933_; size_t v___x_4934_; 
v___x_4933_ = ((size_t)1ULL);
v___x_4934_ = lean_usize_add(v_i_4928_, v___x_4933_);
v_i_4928_ = v___x_4934_;
v_b_4929_ = v_a_4932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5262_, lean_object* v_checkImports_5263_, lean_object* v_args_5264_, lean_object* v___x_5265_, lean_object* v_as_5266_, lean_object* v_sz_5267_, lean_object* v_i_5268_, lean_object* v_b_5269_, lean_object* v___y_5270_){
_start:
{
size_t v_sz_boxed_5271_; size_t v_i_boxed_5272_; lean_object* v_res_5273_; 
v_sz_boxed_5271_ = lean_unbox_usize(v_sz_5267_);
lean_dec(v_sz_5267_);
v_i_boxed_5272_ = lean_unbox_usize(v_i_5268_);
lean_dec(v_i_5268_);
v_res_5273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5262_, v_checkImports_5263_, v_args_5264_, v___x_5265_, v_as_5266_, v_sz_boxed_5271_, v_i_boxed_5272_, v_b_5269_);
lean_dec_ref(v_as_5266_);
lean_dec_ref(v_args_5264_);
lean_dec_ref(v_checkImports_5263_);
lean_dec(v___x_5262_);
return v_res_5273_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = l_Lean_NameSet_empty;
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
return v___x_5275_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5276_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5277_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
lean_ctor_set(v___x_5278_, 1, v___x_5276_);
return v___x_5278_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5279_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5280_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
lean_ctor_set(v___x_5281_, 1, v___x_5279_);
return v___x_5281_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5283_; lean_object* v___x_5284_; 
v___x_5283_ = 0;
v___x_5284_ = lean_box_uint32(v___x_5283_);
return v___x_5284_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5285_; lean_object* v___x_5286_; 
v___x_5285_ = 1;
v___x_5286_ = lean_box_uint32(v___x_5285_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5287_){
_start:
{
lean_object* v_mods_5289_; uint8_t v_mode_5290_; lean_object* v_checks_5291_; lean_object* v_srcSearchPath_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v_anyFailed_5295_; 
v_mods_5289_ = lean_ctor_get(v_args_5287_, 1);
lean_inc_ref(v_mods_5289_);
v_mode_5290_ = lean_ctor_get_uint8(v_args_5287_, sizeof(void*)*4 + 1);
v_checks_5291_ = lean_ctor_get(v_args_5287_, 2);
v_srcSearchPath_5292_ = lean_ctor_get(v_args_5287_, 3);
v___x_5293_ = lean_array_get_size(v_mods_5289_);
v___x_5294_ = lean_unsigned_to_nat(0u);
v_anyFailed_5295_ = lean_nat_dec_eq(v___x_5293_, v___x_5294_);
if (v_anyFailed_5295_ == 0)
{
size_t v_sz_5296_; size_t v___x_5297_; lean_object* v_checkImports_5298_; lean_object* v___x_5299_; 
v_sz_5296_ = lean_array_size(v_checks_5291_);
v___x_5297_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5291_);
v_checkImports_5298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5293_, v_sz_5296_, v___x_5297_, v_checks_5291_);
v___x_5299_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; size_t v_sz_5307_; lean_object* v___x_5308_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
lean_inc(v_a_5300_);
lean_dec_ref_known(v___x_5299_, 1);
lean_inc(v_srcSearchPath_5292_);
v___x_5301_ = l_List_appendTR___redArg(v_srcSearchPath_5292_, v_a_5300_);
v___x_5302_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5303_ = lean_box(v_anyFailed_5295_);
v___x_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5304_, 0, v___x_5303_);
lean_ctor_set(v___x_5304_, 1, v___x_5302_);
v___x_5305_ = lean_box(v_anyFailed_5295_);
v___x_5306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5305_);
lean_ctor_set(v___x_5306_, 1, v___x_5304_);
v_sz_5307_ = lean_array_size(v_mods_5289_);
v___x_5308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5293_, v_checkImports_5298_, v_args_5287_, v___x_5301_, v_mods_5289_, v_sz_5307_, v___x_5297_, v___x_5306_);
lean_dec_ref(v_mods_5289_);
lean_dec_ref(v_args_5287_);
lean_dec_ref(v_checkImports_5298_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5380_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5311_ = v___x_5308_;
v_isShared_5312_ = v_isSharedCheck_5380_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v___x_5308_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5380_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
switch(v_mode_5290_)
{
case 0:
{
lean_object* v_fst_5313_; uint8_t v___x_5314_; 
v_fst_5313_ = lean_ctor_get(v_a_5309_, 0);
lean_inc(v_fst_5313_);
lean_dec(v_a_5309_);
v___x_5314_ = lean_unbox(v_fst_5313_);
lean_dec(v_fst_5313_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; lean_object* v___x_5317_; 
v___x_5315_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 0, v___x_5315_);
v___x_5317_ = v___x_5311_;
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
else
{
lean_object* v___x_5319_; lean_object* v___x_5321_; 
v___x_5319_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 0, v___x_5319_);
v___x_5321_ = v___x_5311_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5319_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
case 1:
{
lean_object* v_snd_5323_; lean_object* v_snd_5324_; lean_object* v_fst_5325_; lean_object* v_fst_5326_; lean_object* v___x_5327_; 
v_snd_5323_ = lean_ctor_get(v_a_5309_, 1);
lean_inc(v_snd_5323_);
lean_del_object(v___x_5311_);
lean_dec(v_a_5309_);
v_snd_5324_ = lean_ctor_get(v_snd_5323_, 1);
lean_inc(v_snd_5324_);
v_fst_5325_ = lean_ctor_get(v_snd_5323_, 0);
lean_inc(v_fst_5325_);
lean_dec(v_snd_5323_);
v_fst_5326_ = lean_ctor_get(v_snd_5324_, 0);
lean_inc(v_fst_5326_);
lean_dec(v_snd_5324_);
v___x_5327_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5326_);
lean_dec(v_fst_5326_);
if (lean_obj_tag(v___x_5327_) == 0)
{
lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5340_; 
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5340_ == 0)
{
lean_object* v_unused_5341_; 
v_unused_5341_ = lean_ctor_get(v___x_5327_, 0);
lean_dec(v_unused_5341_);
v___x_5329_ = v___x_5327_;
v_isShared_5330_ = v_isSharedCheck_5340_;
goto v_resetjp_5328_;
}
else
{
lean_dec(v___x_5327_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5340_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
uint8_t v___x_5331_; 
v___x_5331_ = lean_unbox(v_fst_5325_);
lean_dec(v_fst_5325_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5334_; 
v___x_5332_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5332_);
v___x_5334_ = v___x_5329_;
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
else
{
lean_object* v___x_5336_; lean_object* v___x_5338_; 
v___x_5336_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5336_);
v___x_5338_ = v___x_5329_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_dec(v_fst_5325_);
v_a_5342_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5327_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5327_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
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
default: 
{
lean_object* v_snd_5350_; lean_object* v_snd_5351_; lean_object* v_snd_5352_; lean_object* v_fst_5353_; lean_object* v_fst_5354_; lean_object* v___x_5355_; size_t v_sz_5356_; lean_object* v___x_5357_; 
v_snd_5350_ = lean_ctor_get(v_a_5309_, 1);
lean_del_object(v___x_5311_);
v_snd_5351_ = lean_ctor_get(v_snd_5350_, 1);
v_snd_5352_ = lean_ctor_get(v_snd_5351_, 1);
lean_inc(v_snd_5352_);
v_fst_5353_ = lean_ctor_get(v_a_5309_, 0);
lean_inc(v_fst_5353_);
lean_dec(v_a_5309_);
v_fst_5354_ = lean_ctor_get(v_snd_5352_, 0);
lean_inc(v_fst_5354_);
lean_dec(v_snd_5352_);
v___x_5355_ = lean_box(0);
v_sz_5356_ = lean_array_size(v_fst_5354_);
v___x_5357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5354_, v_sz_5356_, v___x_5297_, v___x_5355_);
lean_dec(v_fst_5354_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5370_; 
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5370_ == 0)
{
lean_object* v_unused_5371_; 
v_unused_5371_ = lean_ctor_get(v___x_5357_, 0);
lean_dec(v_unused_5371_);
v___x_5359_ = v___x_5357_;
v_isShared_5360_ = v_isSharedCheck_5370_;
goto v_resetjp_5358_;
}
else
{
lean_dec(v___x_5357_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5370_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
uint8_t v___x_5361_; 
v___x_5361_ = lean_unbox(v_fst_5353_);
lean_dec(v_fst_5353_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5362_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 0, v___x_5362_);
v___x_5364_ = v___x_5359_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5362_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
v___x_5366_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 0, v___x_5366_);
v___x_5368_ = v___x_5359_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
else
{
lean_object* v_a_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5379_; 
lean_dec(v_fst_5353_);
v_a_5372_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5379_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5379_ == 0)
{
v___x_5374_ = v___x_5357_;
v_isShared_5375_ = v_isSharedCheck_5379_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_a_5372_);
lean_dec(v___x_5357_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5379_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5377_; 
if (v_isShared_5375_ == 0)
{
v___x_5377_ = v___x_5374_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_a_5372_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5388_; 
v_a_5381_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5308_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5308_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5386_; 
if (v_isShared_5384_ == 0)
{
v___x_5386_ = v___x_5383_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
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
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec_ref(v_checkImports_5298_);
lean_dec_ref(v_mods_5289_);
lean_dec_ref(v_args_5287_);
v_a_5389_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5299_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5299_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; 
lean_dec_ref(v_mods_5289_);
lean_dec_ref(v_args_5287_);
v___x_5397_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5398_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5397_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5406_; 
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5398_);
if (v_isSharedCheck_5406_ == 0)
{
lean_object* v_unused_5407_; 
v_unused_5407_ = lean_ctor_get(v___x_5398_, 0);
lean_dec(v_unused_5407_);
v___x_5400_ = v___x_5398_;
v_isShared_5401_ = v_isSharedCheck_5406_;
goto v_resetjp_5399_;
}
else
{
lean_dec(v___x_5398_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5406_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5402_; lean_object* v___x_5404_; 
v___x_5402_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5402_);
v___x_5404_ = v___x_5400_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
v_a_5408_ = lean_ctor_get(v___x_5398_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5398_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5398_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5398_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l_Lake_BuiltinLint_run(v_args_5416_);
return v_res_5418_;
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
