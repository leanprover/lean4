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
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Linter_CodeQuality_getPackageChecks(lean_object*, lean_object*);
lean_object* l_Lean_Linter_CodeQuality_runPackageChecks(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedPosition_default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21;
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
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_BuiltinLint_Mode_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_BuiltinLint_Mode_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_BuiltinLint_Mode_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg(lean_object* v_report_22_){
_start:
{
lean_inc(v_report_22_);
return v_report_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___redArg___boxed(lean_object* v_report_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_BuiltinLint_Mode_report_elim___redArg(v_report_23_);
lean_dec(v_report_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_report_28_){
_start:
{
lean_inc(v_report_28_);
return v_report_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_report_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_report_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_BuiltinLint_Mode_report_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_report_32_);
lean_dec(v_report_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(lean_object* v_recordExceptions_35_){
_start:
{
lean_inc(v_recordExceptions_35_);
return v_recordExceptions_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg___boxed(lean_object* v_recordExceptions_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim___redArg(v_recordExceptions_36_);
lean_dec(v_recordExceptions_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_recordExceptions_41_){
_start:
{
lean_inc(v_recordExceptions_41_);
return v_recordExceptions_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_recordExceptions_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_recordExceptions_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_BuiltinLint_Mode_recordExceptions_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_recordExceptions_45_);
lean_dec(v_recordExceptions_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(lean_object* v_codeQuality_48_){
_start:
{
lean_inc(v_codeQuality_48_);
return v_codeQuality_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg___boxed(lean_object* v_codeQuality_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_BuiltinLint_Mode_codeQuality_elim___redArg(v_codeQuality_49_);
lean_dec(v_codeQuality_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_codeQuality_54_){
_start:
{
lean_inc(v_codeQuality_54_);
return v_codeQuality_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_Mode_codeQuality_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_codeQuality_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lake_BuiltinLint_Mode_codeQuality_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_codeQuality_58_);
lean_dec(v_codeQuality_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuiltinLint_instBEqMode_beq(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_instBEqMode_beq___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_x_24__boxed_70_; uint8_t v_y_25__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_24__boxed_70_ = lean_unbox(v_x_68_);
v_y_25__boxed_71_ = lean_unbox(v_y_69_);
v_res_72_ = l_Lake_BuiltinLint_instBEqMode_beq(v_x_24__boxed_70_, v_y_25__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t v_sz_79_, size_t v_i_80_, lean_object* v_bs_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_usize_dec_lt(v_i_80_, v_sz_79_);
if (v___x_82_ == 0)
{
return v_bs_81_;
}
else
{
lean_object* v_v_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_102_; 
v_v_83_ = lean_array_uget(v_bs_81_, v_i_80_);
v_fst_84_ = lean_ctor_get(v_v_83_, 0);
v_snd_85_ = lean_ctor_get(v_v_83_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_v_83_);
if (v_isSharedCheck_102_ == 0)
{
v___x_87_ = v_v_83_;
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_snd_85_);
lean_inc(v_fst_84_);
lean_dec(v_v_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v_bs_x27_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_96_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v_bs_x27_90_ = lean_array_uset(v_bs_81_, v_i_80_, v___x_89_);
v___x_91_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1));
v___x_92_ = l_Lean_Name_append(v___x_91_, v_fst_84_);
v___x_93_ = lean_alloc_ctor(1, 0, 1);
v___x_94_ = lean_unbox(v_snd_85_);
lean_dec(v_snd_85_);
lean_ctor_set_uint8(v___x_93_, 0, v___x_94_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___x_93_);
lean_ctor_set(v___x_87_, 0, v___x_92_);
v___x_96_ = v___x_87_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_93_);
v___x_96_ = v_reuseFailAlloc_101_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_80_, v___x_97_);
v___x_99_ = lean_array_uset(v_bs_x27_90_, v_i_80_, v___x_96_);
v_i_80_ = v___x_98_;
v_bs_81_ = v___x_99_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object* v_sz_103_, lean_object* v_i_104_, lean_object* v_bs_105_){
_start:
{
size_t v_sz_boxed_106_; size_t v_i_boxed_107_; lean_object* v_res_108_; 
v_sz_boxed_106_ = lean_unbox_usize(v_sz_103_);
lean_dec(v_sz_103_);
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_boxed_106_, v_i_boxed_107_, v_bs_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object* v_as_109_, size_t v_i_110_, size_t v_stop_111_, lean_object* v_b_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_usize_dec_eq(v_i_110_, v_stop_111_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_117_; size_t v___x_118_; size_t v___x_119_; 
v___x_114_ = lean_array_uget_borrowed(v_as_109_, v_i_110_);
v_fst_115_ = lean_ctor_get(v___x_114_, 0);
v_snd_116_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_115_, v_snd_116_, v_b_112_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_110_, v___x_118_);
v_i_110_ = v___x_119_;
v_b_112_ = v___x_117_;
goto _start;
}
else
{
return v_b_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object* v_as_121_, lean_object* v_i_122_, lean_object* v_stop_123_, lean_object* v_b_124_){
_start:
{
size_t v_i_boxed_125_; size_t v_stop_boxed_126_; lean_object* v_res_127_; 
v_i_boxed_125_ = lean_unbox_usize(v_i_122_);
lean_dec(v_i_122_);
v_stop_boxed_126_ = lean_unbox_usize(v_stop_123_);
lean_dec(v_stop_123_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_121_, v_i_boxed_125_, v_stop_boxed_126_, v_b_124_);
lean_dec_ref(v_as_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object* v_init_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v_k_130_; lean_object* v_v_131_; lean_object* v_l_132_; lean_object* v_r_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_k_130_ = lean_ctor_get(v_x_129_, 1);
v_v_131_ = lean_ctor_get(v_x_129_, 2);
v_l_132_ = lean_ctor_get(v_x_129_, 3);
v_r_133_ = lean_ctor_get(v_x_129_, 4);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_128_, v_l_132_);
lean_inc(v_v_131_);
lean_inc(v_k_130_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_k_130_);
lean_ctor_set(v___x_135_, 1, v_v_131_);
v___x_136_ = lean_array_push(v___x_134_, v___x_135_);
v_init_128_ = v___x_136_;
v_x_129_ = v_r_133_;
goto _start;
}
else
{
return v_init_128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object* v_init_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_138_, v_x_139_);
lean_dec(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_153_){
_start:
{
lean_object* v_linterOverrides_154_; uint8_t v_mode_155_; lean_object* v___y_157_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_linterOverrides_154_ = lean_ctor_get(v_args_153_, 0);
v_mode_155_ = lean_ctor_get_uint8(v_args_153_, sizeof(void*)*4 + 1);
v___x_169_ = lean_box(1);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_array_get_size(v_linterOverrides_154_);
v___x_172_ = lean_nat_dec_lt(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
v___y_157_ = v___x_169_;
goto v___jp_156_;
}
else
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_171_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_154_, v___x_173_, v___x_174_, v___x_169_);
v___y_157_ = v___x_175_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; size_t v_sz_160_; size_t v___x_161_; lean_object* v_base_162_; uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_158_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__0));
v___x_159_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v___x_158_, v___y_157_);
lean_dec(v___y_157_);
v_sz_160_ = lean_array_size(v___x_159_);
v___x_161_ = ((size_t)0ULL);
v_base_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_160_, v___x_161_, v___x_159_);
v___x_163_ = 1;
v___x_164_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_155_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_LeanOptions_ofArray(v_base_162_);
lean_dec_ref(v_base_162_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__5));
v___x_167_ = lean_array_push(v_base_162_, v___x_166_);
v___x_168_ = l_Lean_LeanOptions_ofArray(v___x_167_);
lean_dec_ref(v___x_167_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_176_);
lean_dec_ref(v_args_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_178_, lean_object* v_t_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_178_, v_t_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_181_, lean_object* v_t_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_181_, v_t_182_);
lean_dec(v_t_182_);
return v_res_183_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = lean_box(0);
v___x_186_ = l_Lean_instInhabitedPosition_default;
v___x_187_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_185_);
return v___x_188_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1, &l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1_once, _init_l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__1);
return v___x_189_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_instInhabitedExceptionRecord(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lake_BuiltinLint_instInhabitedExceptionRecord_default;
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_tag_nat(v_x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl___boxed(lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorIdx___impl(v_x_193_);
lean_dec_ref(v_x_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(lean_object* v_t_195_, lean_object* v_k_196_){
_start:
{
switch(lean_obj_tag(v_t_195_))
{
case 0:
{
uint8_t v_failed_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_failed_197_ = lean_ctor_get_uint8(v_t_195_, 0);
lean_dec_ref_known(v_t_195_, 0);
v___x_198_ = lean_box(v_failed_197_);
v___x_199_ = lean_apply_1(v_k_196_, v___x_198_);
return v___x_199_;
}
case 1:
{
lean_object* v_records_200_; uint8_t v_unlocated_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_records_200_ = lean_ctor_get(v_t_195_, 0);
lean_inc_ref(v_records_200_);
v_unlocated_201_ = lean_ctor_get_uint8(v_t_195_, sizeof(void*)*1);
lean_dec_ref_known(v_t_195_, 1);
v___x_202_ = lean_box(v_unlocated_201_);
v___x_203_ = lean_apply_2(v_k_196_, v_records_200_, v___x_202_);
return v___x_203_;
}
default: 
{
lean_object* v_entries_204_; lean_object* v___x_205_; 
v_entries_204_ = lean_ctor_get(v_t_195_, 0);
lean_inc_ref(v_entries_204_);
lean_dec_ref_known(v_t_195_, 1);
v___x_205_ = lean_apply_1(v_k_196_, v_entries_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(lean_object* v_motive_206_, lean_object* v_ctorIdx_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_k_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_208_, v_k_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___boxed(lean_object* v_motive_212_, lean_object* v_ctorIdx_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim(v_motive_212_, v_ctorIdx_213_, v_t_214_, v_h_215_, v_k_216_);
lean_dec(v_ctorIdx_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim___redArg(lean_object* v_t_218_, lean_object* v_reported_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_218_, v_reported_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_reported_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_reported_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_222_, v_reported_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim___redArg(lean_object* v_t_226_, lean_object* v_recorded_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_226_, v_recorded_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_recorded_elim(lean_object* v_motive_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_recorded_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_230_, v_recorded_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim___redArg(lean_object* v_t_234_, lean_object* v_codeQualityChecks_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_234_, v_codeQualityChecks_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_codeQualityChecks_elim(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_codeQualityChecks_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_LintingOutcome_ctorElim___redArg(v_t_238_, v_codeQualityChecks_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_tag_nat(v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorIdx___impl(v_x_244_);
lean_dec_ref(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(lean_object* v_t_246_, lean_object* v_k_247_){
_start:
{
if (lean_obj_tag(v_t_246_) == 0)
{
uint8_t v_failed_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_failed_248_ = lean_ctor_get_uint8(v_t_246_, 0);
lean_dec_ref_known(v_t_246_, 0);
v___x_249_ = lean_box(v_failed_248_);
v___x_250_ = lean_apply_1(v_k_247_, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v_records_251_; uint8_t v_unlocated_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_records_251_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_records_251_);
v_unlocated_252_ = lean_ctor_get_uint8(v_t_246_, sizeof(void*)*1);
lean_dec_ref_known(v_t_246_, 1);
v___x_253_ = lean_box(v_unlocated_252_);
v___x_254_ = lean_apply_2(v_k_247_, v_records_251_, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_257_, v_k_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___boxed(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim(v_motive_261_, v_ctorIdx_262_, v_t_263_, v_h_264_, v_k_265_);
lean_dec(v_ctorIdx_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim___redArg(lean_object* v_t_267_, lean_object* v_reported_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_267_, v_reported_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_reported_elim(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_reported_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_271_, v_reported_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim___redArg(lean_object* v_t_275_, lean_object* v_recorded_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_275_, v_recorded_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_recorded_elim(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_recorded_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_DeferredCheckOutcome_ctorElim___redArg(v_t_279_, v_recorded_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_283_, lean_object* v_as_284_, size_t v_i_285_, size_t v_stop_286_, lean_object* v_b_287_){
_start:
{
lean_object* v___y_289_; uint8_t v___x_293_; 
v___x_293_ = lean_usize_dec_eq(v_i_285_, v_stop_286_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v_fst_295_; lean_object* v_snd_296_; uint8_t v___x_297_; 
v___x_294_ = lean_array_uget_borrowed(v_as_284_, v_i_285_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
v_snd_296_ = lean_ctor_get(v___x_294_, 1);
v___x_297_ = l_Lean_Name_isPrefixOf(v_pkgRoot_283_, v_fst_295_);
if (v___x_297_ == 0)
{
v___y_289_ = v_b_287_;
goto v___jp_288_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_array_get_size(v_snd_296_);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_nat_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_inc(v___x_294_);
v___x_301_ = lean_array_push(v_b_287_, v___x_294_);
v___y_289_ = v___x_301_;
goto v___jp_288_;
}
else
{
v___y_289_ = v_b_287_;
goto v___jp_288_;
}
}
}
else
{
return v_b_287_;
}
v___jp_288_:
{
size_t v___x_290_; size_t v___x_291_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_i_285_, v___x_290_);
v_i_285_ = v___x_291_;
v_b_287_ = v___y_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_302_, lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_, lean_object* v_b_306_){
_start:
{
size_t v_i_boxed_307_; size_t v_stop_boxed_308_; lean_object* v_res_309_; 
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_308_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_302_, v_as_303_, v_i_boxed_307_, v_stop_boxed_308_, v_b_306_);
lean_dec_ref(v_as_303_);
lean_dec(v_pkgRoot_302_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_312_, lean_object* v_pkgRoot_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_316_ = l_Lean_Linter_getAllLints(v_env_312_);
v___x_317_ = lean_array_get_size(v___x_316_);
v___x_318_ = lean_nat_dec_lt(v___x_314_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec_ref(v___x_316_);
return v___x_315_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_317_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_313_, v___x_316_, v___x_319_, v___x_320_, v___x_315_);
lean_dec_ref(v___x_316_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_322_, lean_object* v_pkgRoot_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_322_, v_pkgRoot_323_);
lean_dec(v_pkgRoot_323_);
lean_dec_ref(v_env_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(size_t v_sz_325_, size_t v_i_326_, lean_object* v_bs_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_328_ == 0)
{
return v_bs_327_;
}
else
{
lean_object* v_v_329_; lean_object* v_entry_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v_v_329_ = lean_array_uget_borrowed(v_bs_327_, v_i_326_);
v_entry_330_ = lean_ctor_get(v_v_329_, 1);
lean_inc_ref(v_entry_330_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_327_, v_i_326_, v___x_331_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_326_, v___x_333_);
v___x_335_ = lean_array_uset(v_bs_x27_332_, v_i_326_, v_entry_330_);
v_i_326_ = v___x_334_;
v_bs_327_ = v___x_335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0___boxed(lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_bs_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_boxed_340_, v_i_boxed_341_, v_bs_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(lean_object* v_linterOpts_343_, lean_object* v_as_344_, size_t v_i_345_, size_t v_stop_346_, lean_object* v_b_347_){
_start:
{
lean_object* v___y_349_; uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_eq(v_i_345_, v_stop_346_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v_linter_x3f_355_; 
v___x_354_ = lean_array_uget_borrowed(v_as_344_, v_i_345_);
v_linter_x3f_355_ = lean_ctor_get(v___x_354_, 0);
if (lean_obj_tag(v_linter_x3f_355_) == 0)
{
lean_object* v___x_356_; 
lean_inc(v___x_354_);
v___x_356_ = lean_array_push(v_b_347_, v___x_354_);
v___y_349_ = v___x_356_;
goto v___jp_348_;
}
else
{
lean_object* v_val_357_; uint8_t v___x_358_; 
v_val_357_ = lean_ctor_get(v_linter_x3f_355_, 0);
v___x_358_ = l_Lean_Linter_isLinterEnabledByOptions(v_val_357_, v_linterOpts_343_);
if (v___x_358_ == 0)
{
v___y_349_ = v_b_347_;
goto v___jp_348_;
}
else
{
lean_object* v___x_359_; 
lean_inc(v___x_354_);
v___x_359_ = lean_array_push(v_b_347_, v___x_354_);
v___y_349_ = v___x_359_;
goto v___jp_348_;
}
}
}
else
{
return v_b_347_;
}
v___jp_348_:
{
size_t v___x_350_; size_t v___x_351_; 
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_345_, v___x_350_);
v_i_345_ = v___x_351_;
v_b_347_ = v___y_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1___boxed(lean_object* v_linterOpts_360_, lean_object* v_as_361_, lean_object* v_i_362_, lean_object* v_stop_363_, lean_object* v_b_364_){
_start:
{
size_t v_i_boxed_365_; size_t v_stop_boxed_366_; lean_object* v_res_367_; 
v_i_boxed_365_ = lean_unbox_usize(v_i_362_);
lean_dec(v_i_362_);
v_stop_boxed_366_ = lean_unbox_usize(v_stop_363_);
lean_dec(v_stop_363_);
v_res_367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_360_, v_as_361_, v_i_boxed_365_, v_stop_boxed_366_, v_b_364_);
lean_dec_ref(v_as_361_);
lean_dec_ref(v_linterOpts_360_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(lean_object* v_mod_370_, lean_object* v_args_371_, lean_object* v_linterOpts_372_, lean_object* v_as_373_, size_t v_sz_374_, size_t v_i_375_, lean_object* v_b_376_){
_start:
{
lean_object* v_a_378_; uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_382_ == 0)
{
return v_b_376_;
}
else
{
lean_object* v_a_383_; lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_420_; 
v_a_383_ = lean_array_uget(v_as_373_, v_i_375_);
v_fst_384_ = lean_ctor_get(v_a_383_, 0);
v_snd_385_ = lean_ctor_get(v_a_383_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_420_ == 0)
{
v___x_387_ = v_a_383_;
v_isShared_388_ = v_isSharedCheck_420_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snd_385_);
lean_inc(v_fst_384_);
lean_dec(v_a_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_420_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_419_; 
v_fst_389_ = lean_ctor_get(v_b_376_, 0);
v_snd_390_ = lean_ctor_get(v_b_376_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_b_376_);
if (v_isSharedCheck_419_ == 0)
{
v___x_392_ = v_b_376_;
v_isShared_393_ = v_isSharedCheck_419_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_inc(v_fst_389_);
lean_dec(v_b_376_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_419_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = l_Lean_Name_getRoot(v_mod_370_);
v___x_399_ = l_Lean_Name_isPrefixOf(v___x_398_, v_fst_384_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
lean_del_object(v___x_387_);
lean_dec(v_snd_385_);
lean_dec(v_fst_384_);
goto v___jp_394_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_NameSet_contains(v_fst_389_, v_fst_384_);
if (v___x_400_ == 0)
{
uint8_t v_lintOnly_401_; lean_object* v___x_402_; lean_object* v___y_404_; 
lean_del_object(v___x_392_);
v_lintOnly_401_ = lean_ctor_get_uint8(v_args_371_, sizeof(void*)*4);
v___x_402_ = l_Lean_NameSet_insert(v_fst_389_, v_fst_384_);
if (v_lintOnly_401_ == 0)
{
v___y_404_ = v_snd_385_;
goto v___jp_403_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_array_get_size(v_snd_385_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___closed__0));
v___x_415_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_415_ == 0)
{
lean_dec(v_snd_385_);
v___y_404_ = v___x_414_;
goto v___jp_403_;
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = ((size_t)0ULL);
v___x_417_ = lean_usize_of_nat(v___x_413_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__1(v_linterOpts_372_, v_snd_385_, v___x_416_, v___x_417_, v___x_414_);
lean_dec(v_snd_385_);
v___y_404_ = v___x_418_;
goto v___jp_403_;
}
}
v___jp_403_:
{
size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v_sz_405_ = lean_array_size(v___y_404_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__0(v_sz_405_, v___x_406_, v___y_404_);
v___x_408_ = l_Array_append___redArg(v_snd_390_, v___x_407_);
lean_dec_ref(v___x_407_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_408_);
lean_ctor_set(v___x_387_, 0, v___x_402_);
v___x_410_ = v___x_387_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v_a_378_ = v___x_410_;
goto v___jp_377_;
}
}
}
else
{
lean_del_object(v___x_387_);
lean_dec(v_snd_385_);
lean_dec(v_fst_384_);
goto v___jp_394_;
}
}
v___jp_394_:
{
lean_object* v___x_396_; 
if (v_isShared_393_ == 0)
{
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_fst_389_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_snd_390_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
v_a_378_ = v___x_396_;
goto v___jp_377_;
}
}
}
}
}
v___jp_377_:
{
size_t v___x_379_; size_t v___x_380_; 
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_375_, v___x_379_);
v_i_375_ = v___x_380_;
v_b_376_ = v_a_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2___boxed(lean_object* v_mod_421_, lean_object* v_args_422_, lean_object* v_linterOpts_423_, lean_object* v_as_424_, lean_object* v_sz_425_, lean_object* v_i_426_, lean_object* v_b_427_){
_start:
{
size_t v_sz_boxed_428_; size_t v_i_boxed_429_; lean_object* v_res_430_; 
v_sz_boxed_428_ = lean_unbox_usize(v_sz_425_);
lean_dec(v_sz_425_);
v_i_boxed_429_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_mod_421_, v_args_422_, v_linterOpts_423_, v_as_424_, v_sz_boxed_428_, v_i_boxed_429_, v_b_427_);
lean_dec_ref(v_as_424_);
lean_dec_ref(v_linterOpts_423_);
lean_dec_ref(v_args_422_);
lean_dec(v_mod_421_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(lean_object* v_args_433_, lean_object* v_linterOpts_434_, lean_object* v_env_435_, lean_object* v_mod_436_, lean_object* v_collectedModules_437_){
_start:
{
lean_object* v_acc_438_; lean_object* v___x_439_; lean_object* v___x_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_acc_438_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v___x_439_ = l_Lean_Linter_getAllCodeQualityEntries(v_env_435_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_collectedModules_437_);
lean_ctor_set(v___x_440_, 1, v_acc_438_);
v_sz_441_ = lean_array_size(v___x_439_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality_spec__2(v_mod_436_, v_args_433_, v_linterOpts_434_, v___x_439_, v_sz_441_, v___x_442_, v___x_440_);
lean_dec_ref(v___x_439_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_443_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v___x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_fst_444_);
lean_ctor_set(v___x_447_, 0, v_snd_445_);
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_snd_445_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_fst_444_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___boxed(lean_object* v_args_453_, lean_object* v_linterOpts_454_, lean_object* v_env_455_, lean_object* v_mod_456_, lean_object* v_collectedModules_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_453_, v_linterOpts_454_, v_env_455_, v_mod_456_, v_collectedModules_457_);
lean_dec(v_mod_456_);
lean_dec_ref(v_env_455_);
lean_dec_ref(v_linterOpts_454_);
lean_dec_ref(v_args_453_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_459_){
_start:
{
uint8_t v_isModule_461_; 
v_isModule_461_ = lean_ctor_get_uint8(v_modData_459_, sizeof(void*)*7);
return v_isModule_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_462_, lean_object* v_a_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_462_);
lean_dec_ref(v_modData_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(uint32_t v_c_468_){
_start:
{
uint32_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 32;
v___x_470_ = lean_uint32_dec_eq(v_c_468_, v___x_469_);
if (v___x_470_ == 0)
{
uint32_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 9;
v___x_472_ = lean_uint32_dec_eq(v_c_468_, v___x_471_);
return v___x_472_;
}
else
{
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar___boxed(lean_object* v_c_473_){
_start:
{
uint32_t v_c_boxed_474_; uint8_t v_res_475_; lean_object* v_r_476_; 
v_c_boxed_474_ = lean_unbox_uint32(v_c_473_);
lean_dec(v_c_473_);
v_res_475_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v_c_boxed_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(lean_object* v_s_477_, lean_object* v_stopPos_478_, lean_object* v_i_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_i_479_, v___x_480_);
v___x_482_ = lean_nat_dec_le(v___x_481_, v_stopPos_478_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
return v_i_479_;
}
else
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_string_utf8_get(v_s_477_, v_i_479_);
v___x_484_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_isIndentChar(v___x_483_);
if (v___x_484_ == 0)
{
return v_i_479_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_string_utf8_next(v_s_477_, v_i_479_);
lean_dec(v_i_479_);
v_i_479_ = v___x_485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0___boxed(lean_object* v_s_487_, lean_object* v_stopPos_488_, lean_object* v_i_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_s_487_, v_stopPos_488_, v_i_489_);
lean_dec(v_stopPos_488_);
lean_dec_ref(v_s_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(lean_object* v_line_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_e_494_; lean_object* v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_string_utf8_byte_size(v_line_491_);
v_e_494_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace_spec__0(v_line_491_, v___x_493_, v___x_492_);
v___x_495_ = lean_string_utf8_extract(v_line_491_, v___x_492_, v_e_494_);
lean_dec(v_e_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace___boxed(lean_object* v_line_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v_line_496_);
lean_dec_ref(v_line_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg(){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___closed__0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg___boxed(lean_object* v___dummy_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v_res_503_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___redArg();
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(lean_object* v_s_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___boxed(lean_object* v_s_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7(v_s_507_);
lean_dec_ref(v_s_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_509_;
}
else
{
lean_object* v_key_511_; lean_object* v_value_512_; lean_object* v_tail_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_key_511_ = lean_ctor_get(v_x_510_, 0);
v_value_512_ = lean_ctor_get(v_x_510_, 1);
v_tail_513_ = lean_ctor_get(v_x_510_, 2);
lean_inc(v_value_512_);
lean_inc(v_key_511_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_key_511_);
lean_ctor_set(v___x_514_, 1, v_value_512_);
v___x_515_ = lean_array_push(v_x_509_, v___x_514_);
v_x_509_ = v___x_515_;
v_x_510_ = v_tail_513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19___boxed(lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_x_517_, v_x_518_);
lean_dec(v_x_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(lean_object* v_as_520_, size_t v_i_521_, size_t v_stop_522_, lean_object* v_b_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_521_, v_stop_522_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; 
v___x_525_ = lean_array_uget_borrowed(v_as_520_, v_i_521_);
v___x_526_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__19(v_b_523_, v___x_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_521_, v___x_527_);
v_i_521_ = v___x_528_;
v_b_523_ = v___x_526_;
goto _start;
}
else
{
return v_b_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20___boxed(lean_object* v_as_530_, lean_object* v_i_531_, lean_object* v_stop_532_, lean_object* v_b_533_){
_start:
{
size_t v_i_boxed_534_; size_t v_stop_boxed_535_; lean_object* v_res_536_; 
v_i_boxed_534_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_stop_boxed_535_ = lean_unbox_usize(v_stop_532_);
lean_dec(v_stop_532_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_as_530_, v_i_boxed_534_, v_stop_boxed_535_, v_b_533_);
lean_dec_ref(v_as_530_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(lean_object* v_s_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_putStr_540_; lean_object* v___x_541_; 
v___x_539_ = lean_get_stderr();
v_putStr_540_ = lean_ctor_get(v___x_539_, 4);
lean_inc_ref(v_putStr_540_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_apply_2(v_putStr_540_, v_s_537_, lean_box(0));
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29___boxed(lean_object* v_s_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v_s_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(lean_object* v_s_545_){
_start:
{
uint32_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = 10;
v___x_548_ = lean_string_push(v_s_545_, v___x_547_);
v___x_549_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17___boxed(lean_object* v_s_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v_s_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
return v_x_553_;
}
else
{
lean_object* v_key_555_; lean_object* v_value_556_; lean_object* v_tail_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_key_555_ = lean_ctor_get(v_x_554_, 0);
v_value_556_ = lean_ctor_get(v_x_554_, 1);
v_tail_557_ = lean_ctor_get(v_x_554_, 2);
lean_inc(v_value_556_);
lean_inc(v_key_555_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_key_555_);
lean_ctor_set(v___x_558_, 1, v_value_556_);
v___x_559_ = lean_array_push(v_x_553_, v___x_558_);
v_x_553_ = v___x_559_;
v_x_554_ = v_tail_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15___boxed(lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_x_561_, v_x_562_);
lean_dec(v_x_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(lean_object* v_as_564_, size_t v_i_565_, size_t v_stop_566_, lean_object* v_b_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_eq(v_i_565_, v_stop_566_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; 
v___x_569_ = lean_array_uget_borrowed(v_as_564_, v_i_565_);
v___x_570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__15(v_b_567_, v___x_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_565_, v___x_571_);
v_i_565_ = v___x_572_;
v_b_567_ = v___x_570_;
goto _start;
}
else
{
return v_b_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16___boxed(lean_object* v_as_574_, lean_object* v_i_575_, lean_object* v_stop_576_, lean_object* v_b_577_){
_start:
{
size_t v_i_boxed_578_; size_t v_stop_boxed_579_; lean_object* v_res_580_; 
v_i_boxed_578_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_stop_boxed_579_ = lean_unbox_usize(v_stop_576_);
lean_dec(v_stop_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_as_574_, v_i_boxed_578_, v_stop_boxed_579_, v_b_577_);
lean_dec_ref(v_as_574_);
return v_res_580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_fst_583_; lean_object* v_fst_584_; uint8_t v___x_585_; 
v_fst_583_ = lean_ctor_get(v_b_582_, 0);
v_fst_584_ = lean_ctor_get(v_a_581_, 0);
v___x_585_ = lean_nat_dec_lt(v_fst_583_, v_fst_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0___boxed(lean_object* v_a_586_, lean_object* v_b_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v_a_586_, v_b_587_);
lean_dec_ref(v_b_587_);
lean_dec_ref(v_a_586_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(lean_object* v_hi_590_, lean_object* v_pivot_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_k_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_lt(v_k_594_, v_hi_590_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_k_594_);
v___x_596_ = lean_array_fswap(v_as_592_, v_i_593_, v_hi_590_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_i_593_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v_fst_598_; lean_object* v___x_599_; lean_object* v_fst_600_; uint8_t v___x_601_; 
v_fst_598_ = lean_ctor_get(v_pivot_591_, 0);
v___x_599_ = lean_array_fget_borrowed(v_as_592_, v_k_594_);
v_fst_600_ = lean_ctor_get(v___x_599_, 0);
v___x_601_ = lean_nat_dec_lt(v_fst_598_, v_fst_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_k_594_, v___x_602_);
lean_dec(v_k_594_);
v_k_594_ = v___x_603_;
goto _start;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_array_fswap(v_as_592_, v_i_593_, v_k_594_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_i_593_, v___x_606_);
lean_dec(v_i_593_);
v___x_608_ = lean_nat_add(v_k_594_, v___x_606_);
lean_dec(v_k_594_);
v_as_592_ = v___x_605_;
v_i_593_ = v___x_607_;
v_k_594_ = v___x_608_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg___boxed(lean_object* v_hi_610_, lean_object* v_pivot_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_k_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_610_, v_pivot_611_, v_as_612_, v_i_613_, v_k_614_);
lean_dec_ref(v_pivot_611_);
lean_dec(v_hi_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(lean_object* v_n_616_, lean_object* v_as_617_, lean_object* v_lo_618_, lean_object* v_hi_619_){
_start:
{
lean_object* v___y_621_; uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_lt(v_lo_618_, v_hi_619_);
if (v___x_631_ == 0)
{
lean_dec(v_lo_618_);
return v_as_617_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_mid_634_; lean_object* v___y_636_; lean_object* v___y_642_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_632_ = lean_nat_add(v_lo_618_, v_hi_619_);
v___x_633_ = lean_unsigned_to_nat(1u);
v_mid_634_ = lean_nat_shiftr(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
v___x_647_ = lean_array_fget_borrowed(v_as_617_, v_mid_634_);
v___x_648_ = lean_array_fget_borrowed(v_as_617_, v_lo_618_);
v___x_649_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
v___y_642_ = v_as_617_;
goto v___jp_641_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_array_fswap(v_as_617_, v_lo_618_, v_mid_634_);
v___y_642_ = v___x_650_;
goto v___jp_641_;
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_array_fget_borrowed(v___y_636_, v_mid_634_);
v___x_638_ = lean_array_fget_borrowed(v___y_636_, v_hi_619_);
v___x_639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_dec(v_mid_634_);
v___y_621_ = v___y_636_;
goto v___jp_620_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_array_fswap(v___y_636_, v_mid_634_, v_hi_619_);
lean_dec(v_mid_634_);
v___y_621_ = v___x_640_;
goto v___jp_620_;
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_array_fget_borrowed(v___y_642_, v_hi_619_);
v___x_644_ = lean_array_fget_borrowed(v___y_642_, v_lo_618_);
v___x_645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___lam__0(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_636_ = v___y_642_;
goto v___jp_635_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_fswap(v___y_642_, v_lo_618_, v_hi_619_);
v___y_636_ = v___x_646_;
goto v___jp_635_;
}
}
}
v___jp_620_:
{
lean_object* v_pivot_622_; lean_object* v___x_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; uint8_t v___x_626_; 
v_pivot_622_ = lean_array_fget(v___y_621_, v_hi_619_);
lean_inc_n(v_lo_618_, 2);
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_619_, v_pivot_622_, v___y_621_, v_lo_618_, v_lo_618_);
lean_dec(v_pivot_622_);
v_fst_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_fst_624_);
v_snd_625_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_snd_625_);
lean_dec_ref(v___x_623_);
v___x_626_ = lean_nat_dec_le(v_hi_619_, v_fst_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_616_, v_snd_625_, v_lo_618_, v_fst_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_fst_624_, v___x_628_);
lean_dec(v_fst_624_);
v_as_617_ = v___x_627_;
v_lo_618_ = v___x_629_;
goto _start;
}
else
{
lean_dec(v_fst_624_);
lean_dec(v_lo_618_);
return v_snd_625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg___boxed(lean_object* v_n_651_, lean_object* v_as_652_, lean_object* v_lo_653_, lean_object* v_hi_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_651_, v_as_652_, v_lo_653_, v_hi_654_);
lean_dec(v_hi_654_);
lean_dec(v_n_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(lean_object* v_a_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v_a_659_, lean_object* v_b_660_){
_start:
{
lean_object* v_it_662_; lean_object* v_startInclusive_663_; lean_object* v_endExclusive_664_; 
if (lean_obj_tag(v_a_659_) == 0)
{
lean_object* v_currPos_668_; lean_object* v_searcher_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_692_; 
v_currPos_668_ = lean_ctor_get(v_a_659_, 0);
v_searcher_669_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_692_ == 0)
{
v___x_671_ = v_a_659_;
v_isShared_672_ = v_isSharedCheck_692_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_searcher_669_);
lean_inc(v_currPos_668_);
lean_dec(v_a_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_692_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
uint8_t v_decide_673_; 
v_decide_673_ = lean_nat_dec_eq(v_searcher_669_, v___x_658_);
if (v_decide_673_ == 0)
{
uint32_t v___x_674_; uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_674_ = 10;
v___x_675_ = lean_string_utf8_get_fast(v_a_656_, v_searcher_669_);
v___x_676_ = lean_uint32_dec_eq(v___x_675_, v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_string_utf8_next_fast(v_a_656_, v_searcher_669_);
lean_dec(v_searcher_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_677_);
v___x_679_ = v___x_671_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_currPos_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
v_a_659_ = v___x_679_;
goto _start;
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_slice_685_; lean_object* v_nextIt_687_; 
v___x_682_ = lean_string_utf8_next_fast(v_a_656_, v_searcher_669_);
v___x_683_ = lean_nat_sub(v___x_682_, v_searcher_669_);
v___x_684_ = lean_nat_add(v_searcher_669_, v___x_683_);
lean_dec(v___x_683_);
v_slice_685_ = l_String_Slice_subslice_x21(v___x_657_, v_currPos_668_, v_searcher_669_);
lean_inc(v___x_684_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_684_);
lean_ctor_set(v___x_671_, 0, v___x_684_);
v_nextIt_687_ = v___x_671_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_684_);
v_nextIt_687_ = v_reuseFailAlloc_690_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v_startInclusive_688_; lean_object* v_endExclusive_689_; 
v_startInclusive_688_ = lean_ctor_get(v_slice_685_, 0);
lean_inc(v_startInclusive_688_);
v_endExclusive_689_ = lean_ctor_get(v_slice_685_, 1);
lean_inc(v_endExclusive_689_);
lean_dec_ref(v_slice_685_);
v_it_662_ = v_nextIt_687_;
v_startInclusive_663_ = v_startInclusive_688_;
v_endExclusive_664_ = v_endExclusive_689_;
goto v___jp_661_;
}
}
}
else
{
lean_object* v___x_691_; 
lean_del_object(v___x_671_);
lean_dec(v_searcher_669_);
v___x_691_ = lean_box(1);
lean_inc(v___x_658_);
v_it_662_ = v___x_691_;
v_startInclusive_663_ = v_currPos_668_;
v_endExclusive_664_ = v___x_658_;
goto v___jp_661_;
}
}
}
else
{
lean_dec(v___x_658_);
lean_dec_ref(v_a_656_);
return v_b_660_;
}
v___jp_661_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_inc_ref(v_a_656_);
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v_a_656_);
lean_ctor_set(v___x_665_, 1, v_startInclusive_663_);
lean_ctor_set(v___x_665_, 2, v_endExclusive_664_);
v___x_666_ = lean_array_push(v_b_660_, v___x_665_);
v_a_659_ = v_it_662_;
v_b_660_ = v___x_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg___boxed(lean_object* v_a_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v_a_696_, lean_object* v_b_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_693_, v___x_694_, v___x_695_, v_a_696_, v_b_697_);
lean_dec_ref(v___x_694_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_702_ == 0)
{
return v_bs_701_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_v_703_ = lean_array_uget(v_bs_701_, v_i_700_);
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_704_);
v___x_706_ = l_String_Slice_toString(v_v_703_);
lean_dec(v_v_703_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_700_, v___x_707_);
v___x_709_ = lean_array_uset(v_bs_x27_705_, v_i_700_, v___x_706_);
v_i_700_ = v___x_708_;
v_bs_701_ = v___x_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9___boxed(lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_bs_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_boxed_714_, v_i_boxed_715_, v_bs_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
return v_x_717_;
}
else
{
lean_object* v_key_719_; lean_object* v_value_720_; lean_object* v_tail_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_744_; 
v_key_719_ = lean_ctor_get(v_x_718_, 0);
v_value_720_ = lean_ctor_get(v_x_718_, 1);
v_tail_721_ = lean_ctor_get(v_x_718_, 2);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_744_ == 0)
{
v___x_723_ = v_x_718_;
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_tail_721_);
lean_inc(v_value_720_);
lean_inc(v_key_719_);
lean_dec(v_x_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_744_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_fold_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_725_ = lean_array_get_size(v_x_717_);
v___x_726_ = lean_uint64_of_nat(v_key_719_);
v___x_727_ = 32ULL;
v___x_728_ = lean_uint64_shift_right(v___x_726_, v___x_727_);
v_fold_729_ = lean_uint64_xor(v___x_726_, v___x_728_);
v___x_730_ = 16ULL;
v___x_731_ = lean_uint64_shift_right(v_fold_729_, v___x_730_);
v___x_732_ = lean_uint64_xor(v_fold_729_, v___x_731_);
v___x_733_ = lean_uint64_to_usize(v___x_732_);
v___x_734_ = lean_usize_of_nat(v___x_725_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_sub(v___x_734_, v___x_735_);
v___x_737_ = lean_usize_land(v___x_733_, v___x_736_);
v___x_738_ = lean_array_uget_borrowed(v_x_717_, v___x_737_);
lean_inc(v___x_738_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 2, v___x_738_);
v___x_740_ = v___x_723_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_key_719_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_value_720_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v___x_738_);
v___x_740_ = v_reuseFailAlloc_743_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; 
v___x_741_ = lean_array_uset(v_x_717_, v___x_737_, v___x_740_);
v_x_717_ = v___x_741_;
v_x_718_ = v_tail_721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(lean_object* v_i_745_, lean_object* v_source_746_, lean_object* v_target_747_){
_start:
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_source_746_);
v___x_749_ = lean_nat_dec_lt(v_i_745_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec_ref(v_source_746_);
lean_dec(v_i_745_);
return v_target_747_;
}
else
{
lean_object* v_es_750_; lean_object* v___x_751_; lean_object* v_source_752_; lean_object* v_target_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_es_750_ = lean_array_fget(v_source_746_, v_i_745_);
v___x_751_ = lean_box(0);
v_source_752_ = lean_array_fset(v_source_746_, v_i_745_, v___x_751_);
v_target_753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_target_747_, v_es_750_);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_i_745_, v___x_754_);
lean_dec(v_i_745_);
v_i_745_ = v___x_755_;
v_source_746_ = v_source_752_;
v_target_747_ = v_target_753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(lean_object* v_data_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_nbuckets_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_758_ = lean_array_get_size(v_data_757_);
v___x_759_ = lean_unsigned_to_nat(2u);
v_nbuckets_760_ = lean_nat_mul(v___x_758_, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_box(0);
v___x_763_ = lean_mk_array(v_nbuckets_760_, v___x_762_);
v___x_764_ = lean_array_propagate_mark(v_data_757_, v___x_763_);
v___x_765_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v___x_761_, v_data_757_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
else
{
lean_object* v_key_769_; lean_object* v_tail_770_; uint8_t v___x_771_; 
v_key_769_ = lean_ctor_get(v_x_767_, 0);
v_tail_770_ = lean_ctor_get(v_x_767_, 2);
v___x_771_ = lean_nat_dec_eq(v_key_769_, v_a_766_);
if (v___x_771_ == 0)
{
v_x_767_ = v_tail_770_;
goto _start;
}
else
{
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg___boxed(lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_773_, v_x_774_);
lean_dec(v_x_774_);
lean_dec(v_a_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(lean_object* v_a_777_, lean_object* v_b_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_dec(v_b_778_);
lean_dec(v_a_777_);
return v_x_779_;
}
else
{
lean_object* v_key_780_; lean_object* v_value_781_; lean_object* v_tail_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_794_; 
v_key_780_ = lean_ctor_get(v_x_779_, 0);
v_value_781_ = lean_ctor_get(v_x_779_, 1);
v_tail_782_ = lean_ctor_get(v_x_779_, 2);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_779_);
if (v_isSharedCheck_794_ == 0)
{
v___x_784_ = v_x_779_;
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_tail_782_);
lean_inc(v_value_781_);
lean_inc(v_key_780_);
lean_dec(v_x_779_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_eq(v_key_780_, v_a_777_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_777_, v_b_778_, v_tail_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 2, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_key_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_value_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v___x_792_; 
lean_dec(v_value_781_);
lean_dec(v_key_780_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_b_778_);
lean_ctor_set(v___x_784_, 0, v_a_777_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_b_778_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_tail_782_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(lean_object* v_m_795_, lean_object* v_a_796_, lean_object* v_b_797_){
_start:
{
lean_object* v_size_798_; lean_object* v_buckets_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_842_; 
v_size_798_ = lean_ctor_get(v_m_795_, 0);
v_buckets_799_ = lean_ctor_get(v_m_795_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_m_795_);
if (v_isSharedCheck_842_ == 0)
{
v___x_801_ = v_m_795_;
v_isShared_802_ = v_isSharedCheck_842_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_buckets_799_);
lean_inc(v_size_798_);
lean_dec(v_m_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_842_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_fold_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v_bkt_816_; uint8_t v___x_817_; 
v___x_803_ = lean_array_get_size(v_buckets_799_);
v___x_804_ = lean_uint64_of_nat(v_a_796_);
v___x_805_ = 32ULL;
v___x_806_ = lean_uint64_shift_right(v___x_804_, v___x_805_);
v_fold_807_ = lean_uint64_xor(v___x_804_, v___x_806_);
v___x_808_ = 16ULL;
v___x_809_ = lean_uint64_shift_right(v_fold_807_, v___x_808_);
v___x_810_ = lean_uint64_xor(v_fold_807_, v___x_809_);
v___x_811_ = lean_uint64_to_usize(v___x_810_);
v___x_812_ = lean_usize_of_nat(v___x_803_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v___x_812_, v___x_813_);
v___x_815_ = lean_usize_land(v___x_811_, v___x_814_);
v_bkt_816_ = lean_array_uget_borrowed(v_buckets_799_, v___x_815_);
v___x_817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_796_, v_bkt_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v_size_x27_819_; lean_object* v___x_820_; lean_object* v_buckets_x27_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v_size_x27_819_ = lean_nat_add(v_size_798_, v___x_818_);
lean_dec(v_size_798_);
lean_inc(v_bkt_816_);
v___x_820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_820_, 0, v_a_796_);
lean_ctor_set(v___x_820_, 1, v_b_797_);
lean_ctor_set(v___x_820_, 2, v_bkt_816_);
v_buckets_x27_821_ = lean_array_uset(v_buckets_799_, v___x_815_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(4u);
v___x_823_ = lean_nat_mul(v_size_x27_819_, v___x_822_);
v___x_824_ = lean_unsigned_to_nat(3u);
v___x_825_ = lean_nat_div(v___x_823_, v___x_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_array_get_size(v_buckets_x27_821_);
v___x_827_ = lean_nat_dec_le(v___x_825_, v___x_826_);
lean_dec(v___x_825_);
if (v___x_827_ == 0)
{
lean_object* v_val_828_; lean_object* v___x_830_; 
v_val_828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_buckets_x27_821_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_val_828_);
lean_ctor_set(v___x_801_, 0, v_size_x27_819_);
v___x_830_ = v___x_801_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_size_x27_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_val_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v___x_833_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_buckets_x27_821_);
lean_ctor_set(v___x_801_, 0, v_size_x27_819_);
v___x_833_ = v___x_801_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_size_x27_819_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_buckets_x27_821_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v_buckets_x27_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc(v_bkt_816_);
v___x_835_ = lean_box(0);
v_buckets_x27_836_ = lean_array_uset(v_buckets_799_, v___x_815_, v___x_835_);
v___x_837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_796_, v_b_797_, v_bkt_816_);
v___x_838_ = lean_array_uset(v_buckets_x27_836_, v___x_815_, v___x_837_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_838_);
v___x_840_ = v___x_801_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_size_798_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(lean_object* v_a_843_, lean_object* v_as_844_, size_t v_i_845_, size_t v_stop_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_eq(v_i_845_, v_stop_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_array_uget_borrowed(v_as_844_, v_i_845_);
v___x_849_ = lean_name_eq(v_a_843_, v___x_848_);
if (v___x_849_ == 0)
{
size_t v___x_850_; size_t v___x_851_; 
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_845_, v___x_850_);
v_i_845_ = v___x_851_;
goto _start;
}
else
{
return v___x_849_;
}
}
else
{
uint8_t v___x_853_; 
v___x_853_ = 0;
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9___boxed(lean_object* v_a_854_, lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_){
_start:
{
size_t v_i_boxed_858_; size_t v_stop_boxed_859_; uint8_t v_res_860_; lean_object* v_r_861_; 
v_i_boxed_858_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_854_, v_as_855_, v_i_boxed_858_, v_stop_boxed_859_);
lean_dec_ref(v_as_855_);
lean_dec(v_a_854_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(lean_object* v_as_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_array_get_size(v_as_862_);
v___x_866_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
return v___x_866_;
}
else
{
size_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_of_nat(v___x_865_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4_spec__9(v_a_863_, v_as_862_, v___x_867_, v___x_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4___boxed(lean_object* v_as_870_, lean_object* v_a_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v_as_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_as_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(lean_object* v_a_874_, lean_object* v_fallback_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_inc(v_fallback_875_);
return v_fallback_875_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; uint8_t v___x_880_; 
v_key_877_ = lean_ctor_get(v_x_876_, 0);
v_value_878_ = lean_ctor_get(v_x_876_, 1);
v_tail_879_ = lean_ctor_get(v_x_876_, 2);
v___x_880_ = lean_nat_dec_eq(v_key_877_, v_a_874_);
if (v___x_880_ == 0)
{
v_x_876_ = v_tail_879_;
goto _start;
}
else
{
lean_inc(v_value_878_);
return v_value_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg___boxed(lean_object* v_a_882_, lean_object* v_fallback_883_, lean_object* v_x_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_882_, v_fallback_883_, v_x_884_);
lean_dec(v_x_884_);
lean_dec(v_fallback_883_);
lean_dec(v_a_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(lean_object* v_m_886_, lean_object* v_a_887_, lean_object* v_fallback_888_){
_start:
{
lean_object* v_buckets_889_; lean_object* v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v_fold_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_buckets_889_ = lean_ctor_get(v_m_886_, 1);
v___x_890_ = lean_array_get_size(v_buckets_889_);
v___x_891_ = lean_uint64_of_nat(v_a_887_);
v___x_892_ = 32ULL;
v___x_893_ = lean_uint64_shift_right(v___x_891_, v___x_892_);
v_fold_894_ = lean_uint64_xor(v___x_891_, v___x_893_);
v___x_895_ = 16ULL;
v___x_896_ = lean_uint64_shift_right(v_fold_894_, v___x_895_);
v___x_897_ = lean_uint64_xor(v_fold_894_, v___x_896_);
v___x_898_ = lean_uint64_to_usize(v___x_897_);
v___x_899_ = lean_usize_of_nat(v___x_890_);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_sub(v___x_899_, v___x_900_);
v___x_902_ = lean_usize_land(v___x_898_, v___x_901_);
v___x_903_ = lean_array_uget_borrowed(v_buckets_889_, v___x_902_);
v___x_904_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_887_, v_fallback_888_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg___boxed(lean_object* v_m_905_, lean_object* v_a_906_, lean_object* v_fallback_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_905_, v_a_906_, v_fallback_907_);
lean_dec(v_fallback_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_m_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(lean_object* v_as_911_, size_t v_sz_912_, size_t v_i_913_, lean_object* v_b_914_){
_start:
{
lean_object* v_a_917_; uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_913_, v_sz_912_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_914_);
return v___x_922_;
}
else
{
lean_object* v_a_923_; lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_a_923_ = lean_array_uget_borrowed(v_as_911_, v_i_913_);
v_fst_924_ = lean_ctor_get(v_a_923_, 0);
v_snd_925_ = lean_ctor_get(v_a_923_, 1);
v___x_926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_b_914_, v_fst_924_, v___x_926_);
v___x_928_ = l_Array_contains___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__4(v___x_927_, v_snd_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v_snd_925_);
v___x_929_ = lean_array_push(v___x_927_, v_snd_925_);
lean_inc(v_fst_924_);
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_b_914_, v_fst_924_, v___x_929_);
v_a_917_ = v___x_930_;
goto v___jp_916_;
}
else
{
lean_dec(v___x_927_);
v_a_917_ = v_b_914_;
goto v___jp_916_;
}
}
v___jp_916_:
{
size_t v___x_918_; size_t v___x_919_; 
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_913_, v___x_918_);
v_i_913_ = v___x_919_;
v_b_914_ = v_a_917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___boxed(lean_object* v_as_931_, lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_){
_start:
{
size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_sz_boxed_936_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_937_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_as_931_, v_sz_boxed_936_, v_i_boxed_937_, v_b_934_);
lean_dec_ref(v_as_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(lean_object* v_s_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_putStr_942_; lean_object* v___x_943_; 
v___x_941_ = lean_get_stdout();
v_putStr_942_ = lean_ctor_get(v___x_941_, 4);
lean_inc_ref(v_putStr_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = lean_apply_2(v_putStr_942_, v_s_939_, lean_box(0));
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23___boxed(lean_object* v_s_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v_s_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(lean_object* v_s_947_){
_start:
{
uint32_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = 10;
v___x_950_ = lean_string_push(v_s_947_, v___x_949_);
v___x_951_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13___boxed(lean_object* v_s_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v_s_952_);
return v_res_954_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(uint8_t v___x_955_, lean_object* v_a_956_, lean_object* v_b_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_956_, v___x_955_);
v___x_959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_b_957_, v___x_955_);
v___x_960_ = lean_string_dec_lt(v___x_958_, v___x_959_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v___x_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0___boxed(lean_object* v___x_961_, lean_object* v_a_962_, lean_object* v_b_963_){
_start:
{
uint8_t v___x_11634__boxed_964_; uint8_t v_res_965_; lean_object* v_r_966_; 
v___x_11634__boxed_964_ = lean_unbox(v___x_961_);
v_res_965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_11634__boxed_964_, v_a_962_, v_b_963_);
v_r_966_ = lean_box(v_res_965_);
return v_r_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v_hi_969_, lean_object* v_pivot_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_lt(v_k_973_, v_hi_969_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_k_973_);
lean_dec(v_pivot_970_);
v___x_975_ = lean_array_fswap(v_as_971_, v_i_972_, v_hi_969_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_i_972_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
return v___x_976_;
}
else
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_977_ = lean_nat_dec_lt(v___x_967_, v___x_968_);
v___x_978_ = lean_array_fget_borrowed(v_as_971_, v_k_973_);
lean_inc(v___x_978_);
v___x_979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_978_, v___x_977_);
lean_inc(v_pivot_970_);
v___x_980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pivot_970_, v___x_977_);
v___x_981_ = lean_string_dec_lt(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
lean_dec_ref(v___x_979_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_k_973_, v___x_982_);
lean_dec(v_k_973_);
v_k_973_ = v___x_983_;
goto _start;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = lean_array_fswap(v_as_971_, v_i_972_, v_k_973_);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v_i_972_, v___x_986_);
lean_dec(v_i_972_);
v___x_988_ = lean_nat_add(v_k_973_, v___x_986_);
lean_dec(v_k_973_);
v_as_971_ = v___x_985_;
v_i_972_ = v___x_987_;
v_k_973_ = v___x_988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg___boxed(lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v_hi_992_, lean_object* v_pivot_993_, lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_k_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_990_, v___x_991_, v_hi_992_, v_pivot_993_, v_as_994_, v_i_995_, v_k_996_);
lean_dec(v_hi_992_);
lean_dec(v___x_991_);
lean_dec(v___x_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v_n_1000_, lean_object* v_as_1001_, lean_object* v_lo_1002_, lean_object* v_hi_1003_){
_start:
{
lean_object* v___y_1005_; uint8_t v___x_1015_; 
v___x_1015_ = lean_nat_dec_lt(v_lo_1002_, v_hi_1003_);
if (v___x_1015_ == 0)
{
lean_dec(v_lo_1002_);
return v_as_1001_;
}
else
{
uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_mid_1019_; lean_object* v___y_1021_; lean_object* v___y_1027_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1016_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
v___x_1017_ = lean_nat_add(v_lo_1002_, v_hi_1003_);
v___x_1018_ = lean_unsigned_to_nat(1u);
v_mid_1019_ = lean_nat_shiftr(v___x_1017_, v___x_1018_);
lean_dec(v___x_1017_);
v___x_1032_ = lean_array_fget_borrowed(v_as_1001_, v_mid_1019_);
v___x_1033_ = lean_array_fget_borrowed(v_as_1001_, v_lo_1002_);
lean_inc(v___x_1033_);
lean_inc(v___x_1032_);
v___x_1034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1016_, v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
v___y_1027_ = v_as_1001_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_array_fswap(v_as_1001_, v_lo_1002_, v_mid_1019_);
v___y_1027_ = v___x_1035_;
goto v___jp_1026_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1022_ = lean_array_fget_borrowed(v___y_1021_, v_mid_1019_);
v___x_1023_ = lean_array_fget_borrowed(v___y_1021_, v_hi_1003_);
lean_inc(v___x_1023_);
lean_inc(v___x_1022_);
v___x_1024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1016_, v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v_mid_1019_);
v___y_1005_ = v___y_1021_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_array_fswap(v___y_1021_, v_mid_1019_, v_hi_1003_);
lean_dec(v_mid_1019_);
v___y_1005_ = v___x_1025_;
goto v___jp_1004_;
}
}
v___jp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = lean_array_fget_borrowed(v___y_1027_, v_hi_1003_);
v___x_1029_ = lean_array_fget_borrowed(v___y_1027_, v_lo_1002_);
lean_inc(v___x_1029_);
lean_inc(v___x_1028_);
v___x_1030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___lam__0(v___x_1016_, v___x_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
v___y_1021_ = v___y_1027_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_array_fswap(v___y_1027_, v_lo_1002_, v_hi_1003_);
v___y_1021_ = v___x_1031_;
goto v___jp_1020_;
}
}
}
v___jp_1004_:
{
lean_object* v_pivot_1006_; lean_object* v___x_1007_; lean_object* v_fst_1008_; lean_object* v_snd_1009_; uint8_t v___x_1010_; 
v_pivot_1006_ = lean_array_fget(v___y_1005_, v_hi_1003_);
lean_inc_n(v_lo_1002_, 2);
v___x_1007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_998_, v___x_999_, v_hi_1003_, v_pivot_1006_, v___y_1005_, v_lo_1002_, v_lo_1002_);
v_fst_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_fst_1008_);
v_snd_1009_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_snd_1009_);
lean_dec_ref(v___x_1007_);
v___x_1010_ = lean_nat_dec_le(v_hi_1003_, v_fst_1008_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_998_, v___x_999_, v_n_1000_, v_snd_1009_, v_lo_1002_, v_fst_1008_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_add(v_fst_1008_, v___x_1012_);
lean_dec(v_fst_1008_);
v_as_1001_ = v___x_1011_;
v_lo_1002_ = v___x_1013_;
goto _start;
}
else
{
lean_dec(v_fst_1008_);
lean_dec(v_lo_1002_);
return v_snd_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg___boxed(lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_n_1038_, lean_object* v_as_1039_, lean_object* v_lo_1040_, lean_object* v_hi_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1036_, v___x_1037_, v_n_1038_, v_as_1039_, v_lo_1040_, v_hi_1041_);
lean_dec(v_hi_1041_);
lean_dec(v_n_1038_);
lean_dec(v___x_1037_);
lean_dec(v___x_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(lean_object* v___x_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_bs_1050_){
_start:
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v___x_1045_);
return v_bs_1050_;
}
else
{
uint8_t v___x_1052_; lean_object* v_v_1053_; lean_object* v___x_1054_; lean_object* v_bs_x27_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1052_ = lean_nat_dec_lt(v___x_1046_, v___x_1047_);
v_v_1053_ = lean_array_uget(v_bs_1050_, v_i_1049_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v_bs_x27_1055_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1054_);
v___x_1056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__0));
lean_inc_ref(v___x_1045_);
v___x_1057_ = lean_string_append(v___x_1045_, v___x_1056_);
v___x_1058_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1053_, v___x_1052_);
v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___closed__1));
v___x_1061_ = lean_string_append(v___x_1059_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordedMarker___closed__0));
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
v___x_1064_ = ((size_t)1ULL);
v___x_1065_ = lean_usize_add(v_i_1049_, v___x_1064_);
v___x_1066_ = lean_array_uset(v_bs_x27_1055_, v_i_1049_, v___x_1063_);
v_i_1049_ = v___x_1065_;
v_bs_1050_ = v___x_1066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10___boxed(lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v___x_1070_, lean_object* v_sz_1071_, lean_object* v_i_1072_, lean_object* v_bs_1073_){
_start:
{
size_t v_sz_boxed_1074_; size_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v_sz_boxed_1074_ = lean_unbox_usize(v_sz_1071_);
lean_dec(v_sz_1071_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1072_);
lean_dec(v_i_1072_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1068_, v___x_1069_, v___x_1070_, v_sz_boxed_1074_, v_i_boxed_1075_, v_bs_1073_);
lean_dec(v___x_1070_);
lean_dec(v___x_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(lean_object* v_as_1077_, size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_b_1080_){
_start:
{
lean_object* v_a_1083_; uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_b_1080_);
return v___x_1088_;
}
else
{
lean_object* v_a_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1132_; 
v_a_1089_ = lean_array_uget_borrowed(v_as_1077_, v_i_1079_);
v_fst_1090_ = lean_ctor_get(v_a_1089_, 0);
v_snd_1091_ = lean_ctor_get(v_a_1089_, 1);
v_fst_1092_ = lean_ctor_get(v_b_1080_, 0);
v_snd_1093_ = lean_ctor_get(v_b_1080_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_b_1080_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1095_ = v_b_1080_;
v_isShared_1096_ = v_isSharedCheck_1132_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snd_1093_);
lean_inc(v_fst_1092_);
lean_dec(v_b_1080_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1132_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_sub(v_fst_1090_, v___x_1097_);
v___x_1099_ = lean_array_get_size(v_fst_1092_);
v___x_1100_ = lean_nat_dec_lt(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v___x_1098_);
if (v_isShared_1096_ == 0)
{
v___x_1102_ = v___x_1095_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fst_1092_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_snd_1093_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
v_a_1083_ = v___x_1102_;
goto v___jp_1082_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; lean_object* v___x_1121_; lean_object* v___y_1123_; lean_object* v___y_1124_; uint8_t v___x_1126_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_array_fget_borrowed(v_fst_1092_, v___x_1098_);
v___x_1106_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_leadingWhitespace(v___x_1105_);
v___x_1121_ = lean_array_get_size(v_snd_1091_);
v___x_1126_ = lean_nat_dec_eq(v___x_1121_, v___x_1104_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___y_1129_; uint8_t v___x_1131_; 
v___x_1127_ = lean_nat_sub(v___x_1121_, v___x_1097_);
v___x_1131_ = lean_nat_dec_le(v___x_1104_, v___x_1127_);
if (v___x_1131_ == 0)
{
lean_inc(v___x_1127_);
v___y_1129_ = v___x_1127_;
goto v___jp_1128_;
}
else
{
v___y_1129_ = v___x_1104_;
goto v___jp_1128_;
}
v___jp_1128_:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_nat_dec_le(v___y_1129_, v___x_1127_);
if (v___x_1130_ == 0)
{
lean_dec(v___x_1127_);
lean_inc(v___y_1129_);
v___y_1123_ = v___y_1129_;
v___y_1124_ = v___y_1129_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___y_1129_;
v___y_1124_ = v___x_1127_;
goto v___jp_1122_;
}
}
}
else
{
lean_inc(v_snd_1091_);
v___y_1108_ = v_snd_1091_;
goto v___jp_1107_;
}
v___jp_1107_:
{
size_t v_sz_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v_sz_1109_ = lean_array_size(v___y_1108_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__10(v___x_1106_, v___x_1098_, v___x_1099_, v_sz_1109_, v___x_1110_, v___y_1108_);
lean_inc(v___x_1098_);
v___x_1112_ = l_Array_extract___redArg(v_fst_1092_, v___x_1104_, v___x_1098_);
v___x_1113_ = l_Array_append___redArg(v___x_1112_, v___x_1111_);
v___x_1114_ = l_Array_extract___redArg(v_fst_1092_, v___x_1098_, v___x_1099_);
lean_dec(v_fst_1092_);
v___x_1115_ = l_Array_append___redArg(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_array_get_size(v___x_1111_);
lean_dec_ref(v___x_1111_);
v___x_1117_ = lean_nat_add(v_snd_1093_, v___x_1116_);
lean_dec(v_snd_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___x_1117_);
lean_ctor_set(v___x_1095_, 0, v___x_1115_);
v___x_1119_ = v___x_1095_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
v_a_1083_ = v___x_1119_;
goto v___jp_1082_;
}
}
v___jp_1122_:
{
lean_object* v___x_1125_; 
lean_inc(v_snd_1091_);
v___x_1125_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1098_, v___x_1099_, v___x_1121_, v_snd_1091_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
v___y_1108_ = v___x_1125_;
goto v___jp_1107_;
}
}
}
}
v___jp_1082_:
{
size_t v___x_1084_; size_t v___x_1085_; 
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1079_, v___x_1084_);
v_i_1079_ = v___x_1085_;
v_b_1080_ = v_a_1083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12___boxed(lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v_as_1133_, v_sz_boxed_1138_, v_i_boxed_1139_, v_b_1136_);
lean_dec_ref(v_as_1133_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_unsigned_to_nat(16u);
v___x_1145_ = lean_mk_array(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__2);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___x_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(lean_object* v_as_1157_, size_t v_sz_1158_, size_t v_i_1159_, lean_object* v_b_1160_){
_start:
{
lean_object* v_a_1163_; uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1159_, v_sz_1158_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_b_1160_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v_snd_1170_; lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1279_; 
v_a_1169_ = lean_array_uget_borrowed(v_as_1157_, v_i_1159_);
v_snd_1170_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1170_);
v_fst_1171_ = lean_ctor_get(v_snd_1170_, 0);
v_snd_1172_ = lean_ctor_get(v_snd_1170_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_snd_1170_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1174_ = v_snd_1170_;
v_isShared_1175_ = v_isSharedCheck_1279_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1171_);
lean_dec(v_snd_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1279_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___x_1190_; lean_object* v___x_1191_; size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1176_ = lean_box(0);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__3);
v_sz_1192_ = lean_array_size(v_snd_1172_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6(v_snd_1172_, v_sz_1192_, v___x_1193_, v___x_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l_IO_FS_readFile(v_fst_1171_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_size_1200_; lean_object* v_buckets_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; size_t v_sz_1205_; lean_object* v___x_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1250_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
lean_dec(v_snd_1172_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_n(v_a_1197_, 2);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_string_utf8_byte_size(v_a_1197_);
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_a_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1190_);
lean_ctor_set(v___x_1199_, 2, v___x_1198_);
v_size_1200_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_size_1200_);
v_buckets_1201_ = lean_ctor_get(v_a_1195_, 1);
lean_inc_ref(v_buckets_1201_);
lean_dec(v_a_1195_);
v___x_1202_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__7___closed__0);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__4));
v___x_1204_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1197_, v___x_1199_, v___x_1198_, v___x_1202_, v___x_1203_);
lean_dec_ref_known(v___x_1199_, 3);
v_sz_1205_ = lean_array_size(v___x_1204_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__9(v_sz_1205_, v___x_1193_, v___x_1204_);
v___x_1256_ = lean_mk_empty_array_with_capacity(v_size_1200_);
lean_dec(v_size_1200_);
v___x_1257_ = lean_array_get_size(v_buckets_1201_);
v___x_1258_ = lean_nat_dec_lt(v___x_1190_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_dec_ref(v_buckets_1201_);
v___y_1250_ = v___x_1256_;
goto v___jp_1249_;
}
else
{
size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_usize_of_nat(v___x_1257_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__16(v_buckets_1201_, v___x_1193_, v___x_1259_, v___x_1256_);
lean_dec_ref(v_buckets_1201_);
v___y_1250_ = v___x_1260_;
goto v___jp_1249_;
}
v___jp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1190_);
lean_ctor_set(v___x_1174_, 0, v___x_1206_);
v___x_1211_ = v___x_1174_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1190_);
v___x_1211_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
size_t v_sz_1212_; lean_object* v___x_1213_; 
v_sz_1212_ = lean_array_size(v___y_1209_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__12(v___y_1209_, v_sz_1212_, v___x_1193_, v___x_1211_);
lean_dec_ref(v___y_1209_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; uint8_t v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_fst_1215_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_fst_1215_);
v_snd_1216_ = lean_ctor_get(v_a_1214_, 1);
lean_inc(v_snd_1216_);
lean_dec(v_a_1214_);
v___x_1217_ = lean_nat_dec_lt(v___x_1190_, v_snd_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_snd_1216_);
lean_dec(v_fst_1215_);
lean_dec(v_fst_1171_);
v_a_1163_ = v___x_1176_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__5));
lean_inc(v_snd_1216_);
v___x_1219_ = l_Nat_reprFast(v_snd_1216_);
v___x_1220_ = lean_string_append(v___x_1218_, v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__6));
v___x_1222_ = lean_string_append(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_nat_dec_eq(v_snd_1216_, v___y_1208_);
lean_dec(v_snd_1216_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__7));
v___y_1178_ = v_fst_1215_;
v___y_1179_ = v___x_1222_;
v___y_1180_ = v___x_1224_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_1178_ = v_fst_1215_;
v___y_1179_ = v___x_1222_;
v___y_1180_ = v___x_1225_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_fst_1171_);
v_a_1226_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1213_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1213_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
v___jp_1235_:
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v___y_1237_, v___y_1236_, v___y_1238_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec(v___y_1237_);
v___y_1208_ = v___y_1239_;
v___y_1209_ = v___x_1241_;
goto v___jp_1207_;
}
v___jp_1242_:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_nat_dec_le(v___y_1247_, v___y_1244_);
if (v___x_1248_ == 0)
{
lean_dec(v___y_1244_);
lean_inc(v___y_1247_);
v___y_1236_ = v___y_1243_;
v___y_1237_ = v___y_1245_;
v___y_1238_ = v___y_1247_;
v___y_1239_ = v___y_1246_;
v___y_1240_ = v___y_1247_;
goto v___jp_1235_;
}
else
{
v___y_1236_ = v___y_1243_;
v___y_1237_ = v___y_1245_;
v___y_1238_ = v___y_1247_;
v___y_1239_ = v___y_1246_;
v___y_1240_ = v___y_1244_;
goto v___jp_1235_;
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_array_get_size(v___y_1250_);
v___x_1253_ = lean_nat_dec_eq(v___x_1252_, v___x_1190_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_nat_sub(v___x_1252_, v___x_1251_);
v___x_1255_ = lean_nat_dec_le(v___x_1190_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_inc(v___x_1254_);
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___x_1254_;
v___y_1245_ = v___x_1252_;
v___y_1246_ = v___x_1251_;
v___y_1247_ = v___x_1254_;
goto v___jp_1242_;
}
else
{
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___x_1254_;
v___y_1245_ = v___x_1252_;
v___y_1246_ = v___x_1251_;
v___y_1247_ = v___x_1190_;
goto v___jp_1242_;
}
}
else
{
v___y_1208_ = v___x_1251_;
v___y_1209_ = v___y_1250_;
goto v___jp_1207_;
}
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref_known(v___x_1196_, 1);
lean_dec(v_a_1195_);
lean_del_object(v___x_1174_);
v___x_1261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__8));
v___x_1262_ = lean_string_append(v___x_1261_, v_fst_1171_);
lean_dec(v_fst_1171_);
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__9));
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_array_get_size(v_snd_1172_);
lean_dec(v_snd_1172_);
v___x_1266_ = l_Nat_reprFast(v___x_1265_);
v___x_1267_ = lean_string_append(v___x_1264_, v___x_1266_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__10));
v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
v___x_1270_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_dec_ref_known(v___x_1270_, 1);
v_a_1163_ = v___x_1176_;
goto v___jp_1162_;
}
else
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_del_object(v___x_1174_);
lean_dec(v_snd_1172_);
lean_dec(v_fst_1171_);
v_a_1271_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1194_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1194_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
v___jp_1177_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1181_ = lean_string_append(v___y_1179_, v___y_1180_);
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__0));
v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_string_append(v___x_1183_, v_fst_1171_);
v___x_1185_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref_known(v___x_1185_, 1);
v___x_1186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___closed__1));
v___x_1187_ = lean_array_to_list(v___y_1178_);
v___x_1188_ = l_String_intercalate(v___x_1186_, v___x_1187_);
v___x_1189_ = l_IO_FS_writeFile(v_fst_1171_, v___x_1188_);
lean_dec_ref(v___x_1188_);
lean_dec(v_fst_1171_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_dec_ref_known(v___x_1189_, 1);
v_a_1163_ = v___x_1176_;
goto v___jp_1162_;
}
else
{
return v___x_1189_;
}
}
else
{
lean_dec(v___y_1178_);
lean_dec(v_fst_1171_);
return v___x_1185_;
}
}
}
}
v___jp_1162_:
{
size_t v___x_1164_; size_t v___x_1165_; 
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1159_, v___x_1164_);
v_i_1159_ = v___x_1165_;
v_b_1160_ = v_a_1163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18___boxed(lean_object* v_as_1280_, lean_object* v_sz_1281_, lean_object* v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_){
_start:
{
size_t v_sz_boxed_1285_; size_t v_i_boxed_1286_; lean_object* v_res_1287_; 
v_sz_boxed_1285_ = lean_unbox_usize(v_sz_1281_);
lean_dec(v_sz_1281_);
v_i_boxed_1286_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v_as_1280_, v_sz_boxed_1285_, v_i_boxed_1286_, v_b_1283_);
lean_dec_ref(v_as_1280_);
return v_res_1287_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(lean_object* v_a_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
else
{
lean_object* v_key_1291_; lean_object* v_tail_1292_; uint8_t v___x_1293_; 
v_key_1291_ = lean_ctor_get(v_x_1289_, 0);
v_tail_1292_ = lean_ctor_get(v_x_1289_, 2);
v___x_1293_ = lean_string_dec_eq(v_key_1291_, v_a_1288_);
if (v___x_1293_ == 0)
{
v_x_1289_ = v_tail_1292_;
goto _start;
}
else
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg___boxed(lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec_ref(v_a_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(lean_object* v_a_1299_, lean_object* v_b_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
lean_dec(v_b_1300_);
lean_dec_ref(v_a_1299_);
return v_x_1301_;
}
else
{
lean_object* v_key_1302_; lean_object* v_value_1303_; lean_object* v_tail_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1316_; 
v_key_1302_ = lean_ctor_get(v_x_1301_, 0);
v_value_1303_ = lean_ctor_get(v_x_1301_, 1);
v_tail_1304_ = lean_ctor_get(v_x_1301_, 2);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1306_ = v_x_1301_;
v_isShared_1307_ = v_isSharedCheck_1316_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_tail_1304_);
lean_inc(v_value_1303_);
lean_inc(v_key_1302_);
lean_dec(v_x_1301_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1316_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_string_dec_eq(v_key_1302_, v_a_1299_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1299_, v_b_1300_, v_tail_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 2, v___x_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_key_1302_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_value_1303_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v___x_1314_; 
lean_dec(v_value_1303_);
lean_dec(v_key_1302_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v_b_1300_);
lean_ctor_set(v___x_1306_, 0, v_a_1299_);
v___x_1314_ = v___x_1306_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1299_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_b_1300_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_tail_1304_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
return v_x_1317_;
}
else
{
lean_object* v_key_1319_; lean_object* v_value_1320_; lean_object* v_tail_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1344_; 
v_key_1319_ = lean_ctor_get(v_x_1318_, 0);
v_value_1320_ = lean_ctor_get(v_x_1318_, 1);
v_tail_1321_ = lean_ctor_get(v_x_1318_, 2);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1323_ = v_x_1318_;
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_tail_1321_);
lean_inc(v_value_1320_);
lean_inc(v_key_1319_);
lean_dec(v_x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1344_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v_fold_1329_; uint64_t v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1325_ = lean_array_get_size(v_x_1317_);
v___x_1326_ = lean_string_hash(v_key_1319_);
v___x_1327_ = 32ULL;
v___x_1328_ = lean_uint64_shift_right(v___x_1326_, v___x_1327_);
v_fold_1329_ = lean_uint64_xor(v___x_1326_, v___x_1328_);
v___x_1330_ = 16ULL;
v___x_1331_ = lean_uint64_shift_right(v_fold_1329_, v___x_1330_);
v___x_1332_ = lean_uint64_xor(v_fold_1329_, v___x_1331_);
v___x_1333_ = lean_uint64_to_usize(v___x_1332_);
v___x_1334_ = lean_usize_of_nat(v___x_1325_);
v___x_1335_ = ((size_t)1ULL);
v___x_1336_ = lean_usize_sub(v___x_1334_, v___x_1335_);
v___x_1337_ = lean_usize_land(v___x_1333_, v___x_1336_);
v___x_1338_ = lean_array_uget_borrowed(v_x_1317_, v___x_1337_);
lean_inc(v___x_1338_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 2, v___x_1338_);
v___x_1340_ = v___x_1323_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_key_1319_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_value_1320_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_array_uset(v_x_1317_, v___x_1337_, v___x_1340_);
v_x_1317_ = v___x_1341_;
v_x_1318_ = v_tail_1321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(lean_object* v_i_1345_, lean_object* v_source_1346_, lean_object* v_target_1347_){
_start:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_array_get_size(v_source_1346_);
v___x_1349_ = lean_nat_dec_lt(v_i_1345_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v_source_1346_);
lean_dec(v_i_1345_);
return v_target_1347_;
}
else
{
lean_object* v_es_1350_; lean_object* v___x_1351_; lean_object* v_source_1352_; lean_object* v_target_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_es_1350_ = lean_array_fget(v_source_1346_, v_i_1345_);
v___x_1351_ = lean_box(0);
v_source_1352_ = lean_array_fset(v_source_1346_, v_i_1345_, v___x_1351_);
v_target_1353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_target_1347_, v_es_1350_);
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_i_1345_, v___x_1354_);
lean_dec(v_i_1345_);
v_i_1345_ = v___x_1355_;
v_source_1346_ = v_source_1352_;
v_target_1347_ = v_target_1353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(lean_object* v_data_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_nbuckets_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1358_ = lean_array_get_size(v_data_1357_);
v___x_1359_ = lean_unsigned_to_nat(2u);
v_nbuckets_1360_ = lean_nat_mul(v___x_1358_, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_mk_array(v_nbuckets_1360_, v___x_1362_);
v___x_1364_ = lean_array_propagate_mark(v_data_1357_, v___x_1363_);
v___x_1365_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v___x_1361_, v_data_1357_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(lean_object* v_m_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_){
_start:
{
lean_object* v_size_1369_; lean_object* v_buckets_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1413_; 
v_size_1369_ = lean_ctor_get(v_m_1366_, 0);
v_buckets_1370_ = lean_ctor_get(v_m_1366_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_m_1366_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1372_ = v_m_1366_;
v_isShared_1373_ = v_isSharedCheck_1413_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_buckets_1370_);
lean_inc(v_size_1369_);
lean_dec(v_m_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1413_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v_fold_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v_bkt_1387_; uint8_t v___x_1388_; 
v___x_1374_ = lean_array_get_size(v_buckets_1370_);
v___x_1375_ = lean_string_hash(v_a_1367_);
v___x_1376_ = 32ULL;
v___x_1377_ = lean_uint64_shift_right(v___x_1375_, v___x_1376_);
v_fold_1378_ = lean_uint64_xor(v___x_1375_, v___x_1377_);
v___x_1379_ = 16ULL;
v___x_1380_ = lean_uint64_shift_right(v_fold_1378_, v___x_1379_);
v___x_1381_ = lean_uint64_xor(v_fold_1378_, v___x_1380_);
v___x_1382_ = lean_uint64_to_usize(v___x_1381_);
v___x_1383_ = lean_usize_of_nat(v___x_1374_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_sub(v___x_1383_, v___x_1384_);
v___x_1386_ = lean_usize_land(v___x_1382_, v___x_1385_);
v_bkt_1387_ = lean_array_uget_borrowed(v_buckets_1370_, v___x_1386_);
v___x_1388_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1367_, v_bkt_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v_size_x27_1390_; lean_object* v___x_1391_; lean_object* v_buckets_x27_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v_size_x27_1390_ = lean_nat_add(v_size_1369_, v___x_1389_);
lean_dec(v_size_1369_);
lean_inc(v_bkt_1387_);
v___x_1391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1367_);
lean_ctor_set(v___x_1391_, 1, v_b_1368_);
lean_ctor_set(v___x_1391_, 2, v_bkt_1387_);
v_buckets_x27_1392_ = lean_array_uset(v_buckets_1370_, v___x_1386_, v___x_1391_);
v___x_1393_ = lean_unsigned_to_nat(4u);
v___x_1394_ = lean_nat_mul(v_size_x27_1390_, v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(3u);
v___x_1396_ = lean_nat_div(v___x_1394_, v___x_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_array_get_size(v_buckets_x27_1392_);
v___x_1398_ = lean_nat_dec_le(v___x_1396_, v___x_1397_);
lean_dec(v___x_1396_);
if (v___x_1398_ == 0)
{
lean_object* v_val_1399_; lean_object* v___x_1401_; 
v_val_1399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_buckets_x27_1392_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_val_1399_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1390_);
v___x_1401_ = v___x_1372_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_size_x27_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_val_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v___x_1404_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_buckets_x27_1392_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1390_);
v___x_1404_ = v___x_1372_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_size_x27_1390_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_buckets_x27_1392_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v_buckets_x27_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_inc(v_bkt_1387_);
v___x_1406_ = lean_box(0);
v_buckets_x27_1407_ = lean_array_uset(v_buckets_1370_, v___x_1386_, v___x_1406_);
v___x_1408_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1367_, v_b_1368_, v_bkt_1387_);
v___x_1409_ = lean_array_uset(v_buckets_x27_1407_, v___x_1386_, v___x_1408_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1409_);
v___x_1411_ = v___x_1372_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_size_1369_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(lean_object* v_a_1414_, lean_object* v_fallback_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1416_) == 0)
{
lean_inc(v_fallback_1415_);
return v_fallback_1415_;
}
else
{
lean_object* v_key_1417_; lean_object* v_value_1418_; lean_object* v_tail_1419_; uint8_t v___x_1420_; 
v_key_1417_ = lean_ctor_get(v_x_1416_, 0);
v_value_1418_ = lean_ctor_get(v_x_1416_, 1);
v_tail_1419_ = lean_ctor_get(v_x_1416_, 2);
v___x_1420_ = lean_string_dec_eq(v_key_1417_, v_a_1414_);
if (v___x_1420_ == 0)
{
v_x_1416_ = v_tail_1419_;
goto _start;
}
else
{
lean_inc(v_value_1418_);
return v_value_1418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg___boxed(lean_object* v_a_1422_, lean_object* v_fallback_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1422_, v_fallback_1423_, v_x_1424_);
lean_dec(v_x_1424_);
lean_dec(v_fallback_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(lean_object* v_m_1426_, lean_object* v_a_1427_, lean_object* v_fallback_1428_){
_start:
{
lean_object* v_buckets_1429_; lean_object* v___x_1430_; uint64_t v___x_1431_; uint64_t v___x_1432_; uint64_t v___x_1433_; uint64_t v_fold_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_buckets_1429_ = lean_ctor_get(v_m_1426_, 1);
v___x_1430_ = lean_array_get_size(v_buckets_1429_);
v___x_1431_ = lean_string_hash(v_a_1427_);
v___x_1432_ = 32ULL;
v___x_1433_ = lean_uint64_shift_right(v___x_1431_, v___x_1432_);
v_fold_1434_ = lean_uint64_xor(v___x_1431_, v___x_1433_);
v___x_1435_ = 16ULL;
v___x_1436_ = lean_uint64_shift_right(v_fold_1434_, v___x_1435_);
v___x_1437_ = lean_uint64_xor(v_fold_1434_, v___x_1436_);
v___x_1438_ = lean_uint64_to_usize(v___x_1437_);
v___x_1439_ = lean_usize_of_nat(v___x_1430_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_sub(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_usize_land(v___x_1438_, v___x_1441_);
v___x_1443_ = lean_array_uget_borrowed(v_buckets_1429_, v___x_1442_);
v___x_1444_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1427_, v_fallback_1428_, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg___boxed(lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_fallback_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1445_, v_a_1446_, v_fallback_1447_);
lean_dec(v_fallback_1447_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_m_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(lean_object* v_as_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_b_1454_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1454_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v_file_1459_; lean_object* v_pos_1460_; lean_object* v_option_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1487_; 
v_a_1458_ = lean_array_uget_borrowed(v_as_1451_, v_i_1453_);
v_file_1459_ = lean_ctor_get(v_a_1458_, 0);
v_pos_1460_ = lean_ctor_get(v_a_1458_, 1);
lean_inc_ref(v_pos_1460_);
v_option_1461_ = lean_ctor_get(v_a_1458_, 2);
v___x_1462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___closed__0));
lean_inc_ref(v_file_1459_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_file_1459_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_b_1454_, v_file_1459_, v___x_1463_);
lean_dec_ref_known(v___x_1463_, 2);
v_fst_1465_ = lean_ctor_get(v___x_1464_, 0);
v_snd_1466_ = lean_ctor_get(v___x_1464_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1487_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snd_1466_);
lean_inc(v_fst_1465_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1487_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_line_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1485_; 
v_line_1470_ = lean_ctor_get(v_pos_1460_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_pos_1460_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v_pos_1460_, 1);
lean_dec(v_unused_1486_);
v___x_1472_ = v_pos_1460_;
v_isShared_1473_ = v_isSharedCheck_1485_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_line_1470_);
lean_dec(v_pos_1460_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1485_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
lean_inc(v_option_1461_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v_option_1461_);
lean_ctor_set(v___x_1468_, 0, v_line_1470_);
v___x_1475_ = v___x_1468_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_line_1470_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_option_1461_);
v___x_1475_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_array_push(v_snd_1466_, v___x_1475_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1476_);
lean_ctor_set(v___x_1472_, 0, v_fst_1465_);
v___x_1478_ = v___x_1472_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_fst_1465_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; 
lean_inc_ref(v_file_1459_);
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_b_1454_, v_file_1459_, v___x_1478_);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_add(v_i_1453_, v___x_1480_);
v_i_1453_ = v___x_1481_;
v_b_1454_ = v___x_1479_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2___boxed(lean_object* v_as_1488_, lean_object* v_sz_1489_, lean_object* v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_){
_start:
{
size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_as_1488_, v_sz_boxed_1493_, v_i_boxed_1494_, v_b_1491_);
lean_dec_ref(v_as_1488_);
return v_res_1495_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_unsigned_to_nat(16u);
v___x_1498_ = lean_mk_array(v___x_1497_, v___x_1496_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_byFile_1501_; 
v___x_1499_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__0);
v___x_1500_ = lean_unsigned_to_nat(0u);
v_byFile_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byFile_1501_, 0, v___x_1500_);
lean_ctor_set(v_byFile_1501_, 1, v___x_1499_);
return v_byFile_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(lean_object* v_records_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v_byFile_1505_; size_t v_sz_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v_byFile_1505_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___closed__1);
v_sz_1506_ = lean_array_size(v_records_1502_);
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__2(v_records_1502_, v_sz_1506_, v___x_1507_, v_byFile_1505_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___y_1511_; lean_object* v_size_1523_; lean_object* v_buckets_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v_size_1523_ = lean_ctor_get(v_a_1509_, 0);
lean_inc(v_size_1523_);
v_buckets_1524_ = lean_ctor_get(v_a_1509_, 1);
lean_inc_ref(v_buckets_1524_);
lean_dec(v_a_1509_);
v___x_1525_ = lean_mk_empty_array_with_capacity(v_size_1523_);
lean_dec(v_size_1523_);
v___x_1526_ = lean_array_get_size(v_buckets_1524_);
v___x_1527_ = lean_nat_dec_lt(v___x_1504_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec_ref(v_buckets_1524_);
v___y_1511_ = v___x_1525_;
goto v___jp_1510_;
}
else
{
size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_usize_of_nat(v___x_1526_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__20(v_buckets_1524_, v___x_1507_, v___x_1528_, v___x_1525_);
lean_dec_ref(v_buckets_1524_);
v___y_1511_ = v___x_1529_;
goto v___jp_1510_;
}
v___jp_1510_:
{
lean_object* v___x_1512_; size_t v_sz_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
v_sz_1513_ = lean_array_size(v___y_1511_);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__18(v___y_1511_, v_sz_1513_, v___x_1507_, v___x_1512_);
lean_dec_ref(v___y_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1514_, 0);
lean_dec(v_unused_1522_);
v___x_1516_ = v___x_1514_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v___x_1514_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1512_);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1512_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1508_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1508_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles___boxed(lean_object* v_records_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_records_1538_);
lean_dec_ref(v_records_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, lean_object* v_a_1543_, lean_object* v_fallback_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___redArg(v_m_1542_, v_a_1543_, v_fallback_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0___boxed(lean_object* v_00_u03b2_1546_, lean_object* v_m_1547_, lean_object* v_a_1548_, lean_object* v_fallback_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0(v_00_u03b2_1546_, v_m_1547_, v_a_1548_, v_fallback_1549_);
lean_dec(v_fallback_1549_);
lean_dec_ref(v_a_1548_);
lean_dec_ref(v_m_1547_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1(lean_object* v_00_u03b2_1551_, lean_object* v_m_1552_, lean_object* v_a_1553_, lean_object* v_b_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1___redArg(v_m_1552_, v_a_1553_, v_b_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_a_1558_, lean_object* v_fallback_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___redArg(v_m_1557_, v_a_1558_, v_fallback_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3___boxed(lean_object* v_00_u03b2_1561_, lean_object* v_m_1562_, lean_object* v_a_1563_, lean_object* v_fallback_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3(v_00_u03b2_1561_, v_m_1562_, v_a_1563_, v_fallback_1564_);
lean_dec(v_fallback_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_m_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5(lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_, lean_object* v_a_1568_, lean_object* v_b_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5___redArg(v_m_1567_, v_a_1568_, v_b_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(lean_object* v_a_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_inst_1574_, lean_object* v_R_1575_, lean_object* v_a_1576_, lean_object* v_b_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___redArg(v_a_1571_, v___x_1572_, v___x_1573_, v_a_1576_, v_b_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8___boxed(lean_object* v_a_1579_, lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v_inst_1582_, lean_object* v_R_1583_, lean_object* v_a_1584_, lean_object* v_b_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__8(v_a_1579_, v___x_1580_, v___x_1581_, v_inst_1582_, v_R_1583_, v_a_1584_, v_b_1585_);
lean_dec_ref(v___x_1580_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(lean_object* v___x_1587_, lean_object* v___x_1588_, lean_object* v_n_1589_, lean_object* v_as_1590_, lean_object* v_lo_1591_, lean_object* v_hi_1592_, lean_object* v_w_1593_, lean_object* v_hlo_1594_, lean_object* v_hhi_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___redArg(v___x_1587_, v___x_1588_, v_n_1589_, v_as_1590_, v_lo_1591_, v_hi_1592_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11___boxed(lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v_n_1599_, lean_object* v_as_1600_, lean_object* v_lo_1601_, lean_object* v_hi_1602_, lean_object* v_w_1603_, lean_object* v_hlo_1604_, lean_object* v_hhi_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11(v___x_1597_, v___x_1598_, v_n_1599_, v_as_1600_, v_lo_1601_, v_hi_1602_, v_w_1603_, v_hlo_1604_, v_hhi_1605_);
lean_dec(v_hi_1602_);
lean_dec(v_n_1599_);
lean_dec(v___x_1598_);
lean_dec(v___x_1597_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(lean_object* v_n_1607_, lean_object* v_as_1608_, lean_object* v_lo_1609_, lean_object* v_hi_1610_, lean_object* v_w_1611_, lean_object* v_hlo_1612_, lean_object* v_hhi_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___redArg(v_n_1607_, v_as_1608_, v_lo_1609_, v_hi_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14___boxed(lean_object* v_n_1615_, lean_object* v_as_1616_, lean_object* v_lo_1617_, lean_object* v_hi_1618_, lean_object* v_w_1619_, lean_object* v_hlo_1620_, lean_object* v_hhi_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14(v_n_1615_, v_as_1616_, v_lo_1617_, v_hi_1618_, v_w_1619_, v_hlo_1620_, v_hhi_1621_);
lean_dec(v_hi_1618_);
lean_dec(v_n_1615_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(lean_object* v_00_u03b2_1623_, lean_object* v_a_1624_, lean_object* v_fallback_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___redArg(v_a_1624_, v_fallback_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1628_, lean_object* v_a_1629_, lean_object* v_fallback_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__0_spec__0(v_00_u03b2_1628_, v_a_1629_, v_fallback_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec(v_fallback_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___redArg(v_a_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__2(v_00_u03b2_1637_, v_a_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_a_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3(lean_object* v_00_u03b2_1642_, lean_object* v_data_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3___redArg(v_data_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__4___redArg(v_a_1646_, v_b_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(lean_object* v_00_u03b2_1650_, lean_object* v_a_1651_, lean_object* v_fallback_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___redArg(v_a_1651_, v_fallback_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_a_1656_, lean_object* v_fallback_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__3_spec__7(v_00_u03b2_1655_, v_a_1656_, v_fallback_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec(v_fallback_1657_);
lean_dec(v_a_1656_);
return v_res_1659_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(lean_object* v_00_u03b2_1660_, lean_object* v_a_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___redArg(v_a_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_a_1665_, lean_object* v_x_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__11(v_00_u03b2_1664_, v_a_1665_, v_x_1666_);
lean_dec(v_x_1666_);
lean_dec(v_a_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12(lean_object* v_00_u03b2_1669_, lean_object* v_data_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12___redArg(v_data_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13(lean_object* v_00_u03b2_1672_, lean_object* v_a_1673_, lean_object* v_b_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__13___redArg(v_a_1673_, v_b_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(lean_object* v___x_1677_, lean_object* v___x_1678_, lean_object* v_n_1679_, lean_object* v_lo_1680_, lean_object* v_hi_1681_, lean_object* v_hhi_1682_, lean_object* v_pivot_1683_, lean_object* v_as_1684_, lean_object* v_i_1685_, lean_object* v_k_1686_, lean_object* v_ilo_1687_, lean_object* v_ik_1688_, lean_object* v_w_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___redArg(v___x_1677_, v___x_1678_, v_hi_1681_, v_pivot_1683_, v_as_1684_, v_i_1685_, v_k_1686_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20___boxed(lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v_n_1693_, lean_object* v_lo_1694_, lean_object* v_hi_1695_, lean_object* v_hhi_1696_, lean_object* v_pivot_1697_, lean_object* v_as_1698_, lean_object* v_i_1699_, lean_object* v_k_1700_, lean_object* v_ilo_1701_, lean_object* v_ik_1702_, lean_object* v_w_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__11_spec__20(v___x_1691_, v___x_1692_, v_n_1693_, v_lo_1694_, v_hi_1695_, v_hhi_1696_, v_pivot_1697_, v_as_1698_, v_i_1699_, v_k_1700_, v_ilo_1701_, v_ik_1702_, v_w_1703_);
lean_dec(v_hi_1695_);
lean_dec(v_lo_1694_);
lean_dec(v_n_1693_);
lean_dec(v___x_1692_);
lean_dec(v___x_1691_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(lean_object* v_n_1705_, lean_object* v_lo_1706_, lean_object* v_hi_1707_, lean_object* v_hhi_1708_, lean_object* v_pivot_1709_, lean_object* v_as_1710_, lean_object* v_i_1711_, lean_object* v_k_1712_, lean_object* v_ilo_1713_, lean_object* v_ik_1714_, lean_object* v_w_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___redArg(v_hi_1707_, v_pivot_1709_, v_as_1710_, v_i_1711_, v_k_1712_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25___boxed(lean_object* v_n_1717_, lean_object* v_lo_1718_, lean_object* v_hi_1719_, lean_object* v_hhi_1720_, lean_object* v_pivot_1721_, lean_object* v_as_1722_, lean_object* v_i_1723_, lean_object* v_k_1724_, lean_object* v_ilo_1725_, lean_object* v_ik_1726_, lean_object* v_w_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__14_spec__25(v_n_1717_, v_lo_1718_, v_hi_1719_, v_hhi_1720_, v_pivot_1721_, v_as_1722_, v_i_1723_, v_k_1724_, v_ilo_1725_, v_ik_1726_, v_w_1727_);
lean_dec_ref(v_pivot_1721_);
lean_dec(v_hi_1719_);
lean_dec(v_lo_1718_);
lean_dec(v_n_1717_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1729_, lean_object* v_i_1730_, lean_object* v_source_1731_, lean_object* v_target_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5___redArg(v_i_1730_, v_source_1731_, v_target_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1734_, lean_object* v_i_1735_, lean_object* v_source_1736_, lean_object* v_target_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15___redArg(v_i_1735_, v_source_1736_, v_target_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26(lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__1_spec__3_spec__5_spec__26___redArg(v_x_1740_, v_x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33(lean_object* v_00_u03b2_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__5_spec__12_spec__15_spec__33___redArg(v_x_1744_, v_x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(lean_object* v_declName_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v_env_1751_; lean_object* v___x_1752_; lean_object* v_env_1753_; lean_object* v___x_1754_; lean_object* v_toEnvExtension_1755_; lean_object* v_asyncMode_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1750_ = lean_st_ref_get(v___y_1748_);
v_env_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_env_1751_);
lean_dec(v___x_1750_);
v___x_1752_ = lean_st_ref_get(v___y_1748_);
v_env_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_env_1753_);
lean_dec(v___x_1752_);
v___x_1754_ = l_Lean_declRangeExt;
v_toEnvExtension_1755_ = lean_ctor_get(v___x_1754_, 0);
v_asyncMode_1756_ = lean_ctor_get(v_toEnvExtension_1755_, 2);
v___x_1757_ = 0;
lean_inc(v_declName_1747_);
v___x_1758_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1754_, v_env_1751_, v_declName_1747_, v_asyncMode_1756_, v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = 1;
v___x_1760_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1754_, v_env_1753_, v_declName_1747_, v_asyncMode_1756_, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; 
lean_dec_ref(v_env_1753_);
lean_dec(v_declName_1747_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1758_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1763_, v___y_1764_);
lean_dec(v___y_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v_env_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1770_ = lean_st_ref_get(v___y_1768_);
v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc_ref(v_env_1771_);
lean_dec(v___x_1770_);
v___x_1772_ = l_Lean_isRecCore(v_env_1771_, v_declName_1767_);
v___x_1773_ = lean_box(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1775_, v___y_1776_);
lean_dec(v___y_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_ranges_1784_; lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v___x_1792_; lean_object* v_a_1793_; uint8_t v___x_1798_; 
v___x_1790_ = lean_st_ref_get(v___y_1781_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref_n(v_env_1791_, 2);
lean_dec(v___x_1790_);
lean_inc_n(v_declName_1779_, 2);
v___x_1792_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1779_, v___y_1781_);
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
v___x_1798_ = l_Lean_isAuxRecursor(v_env_1791_, v_declName_1779_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; 
lean_inc(v_declName_1779_);
v___x_1799_ = l_Lean_isNoConfusion(v_env_1791_, v_declName_1779_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_unbox(v_a_1793_);
lean_dec(v_a_1793_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v_a_1802_; 
lean_inc(v_declName_1779_);
v___x_1801_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1779_, v___y_1781_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v_ranges_1784_ = v_a_1802_;
goto v___jp_1783_;
}
else
{
goto v___jp_1794_;
}
}
else
{
lean_dec(v_a_1793_);
goto v___jp_1794_;
}
}
else
{
lean_dec(v_a_1793_);
lean_dec_ref(v_env_1791_);
goto v___jp_1794_;
}
v___jp_1783_:
{
if (lean_obj_tag(v_ranges_1784_) == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = l_Lean_builtinDeclRanges;
v___x_1786_ = lean_st_ref_get(v___x_1785_);
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1786_, v_declName_1779_);
lean_dec(v_declName_1779_);
lean_dec(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_declName_1779_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_ranges_1784_);
return v___x_1789_;
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; 
v___x_1795_ = l_Lean_Name_getPrefix(v_declName_1779_);
v___x_1796_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1795_, v___y_1781_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v_ranges_1784_ = v_a_1797_;
goto v___jp_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1808_, lean_object* v_site_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
if (lean_obj_tag(v_site_1809_) == 0)
{
lean_object* v_name_1813_; lean_object* v___x_1814_; 
v_name_1813_ = lean_ctor_get(v_site_1809_, 0);
lean_inc(v_name_1813_);
lean_dec_ref_known(v_site_1809_, 1);
v___x_1814_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1813_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1836_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1836_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1836_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_box(0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
lean_object* v_val_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1835_; 
v_val_1823_ = lean_ctor_get(v_a_1815_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1825_ = v_a_1815_;
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_val_1823_);
lean_dec(v_a_1815_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_range_1827_; lean_object* v_pos_1828_; lean_object* v___x_1830_; 
v_range_1827_ = lean_ctor_get(v_val_1823_, 0);
lean_inc_ref(v_range_1827_);
lean_dec(v_val_1823_);
v_pos_1828_ = lean_ctor_get(v_range_1827_, 0);
lean_inc_ref(v_pos_1828_);
lean_dec_ref(v_range_1827_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_pos_1828_);
v___x_1830_ = v___x_1825_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_pos_1828_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1830_);
v___x_1832_ = v___x_1817_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_a_1837_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1814_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1814_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_n_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1876_; 
v_n_1845_ = lean_ctor_get(v_site_1809_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_site_1809_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1847_ = v_site_1809_;
v_isShared_1848_ = v_isSharedCheck_1876_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_n_1845_);
lean_dec(v_site_1809_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1876_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v_env_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_st_ref_get(v_a_1811_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = l_Lean_getVersoModuleDoc_x3f(v_env_1850_, v_failMod_1808_);
lean_dec_ref(v_env_1850_);
if (lean_obj_tag(v___x_1851_) == 1)
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1871_; 
v_val_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1871_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1871_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = lean_array_get_size(v_val_1852_);
v___x_1857_ = lean_nat_dec_lt(v_n_1845_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
lean_dec(v_n_1845_);
v___x_1858_ = lean_box(0);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1858_);
v___x_1860_ = v___x_1847_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v_declarationRange_1863_; lean_object* v_pos_1864_; lean_object* v___x_1866_; 
v___x_1862_ = lean_array_fget(v_val_1852_, v_n_1845_);
lean_dec(v_n_1845_);
lean_dec(v_val_1852_);
v_declarationRange_1863_ = lean_ctor_get(v___x_1862_, 2);
lean_inc_ref(v_declarationRange_1863_);
lean_dec(v___x_1862_);
v_pos_1864_ = lean_ctor_get(v_declarationRange_1863_, 0);
lean_inc_ref(v_pos_1864_);
lean_dec_ref(v_declarationRange_1863_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_pos_1864_);
v___x_1866_ = v___x_1854_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_pos_1864_);
v___x_1866_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1866_);
v___x_1868_ = v___x_1847_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v___x_1851_);
lean_dec(v_n_1845_);
v___x_1872_ = lean_box(0);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1872_);
v___x_1874_ = v___x_1847_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1877_, lean_object* v_site_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1877_, v_site_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_failMod_1877_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1883_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1893_, v___y_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_name_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_name_1907_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_name_1907_);
lean_dec_ref_known(v_x_1906_, 1);
v___x_1908_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1909_ = 1;
v___x_1910_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1907_, v___x_1909_);
v___x_1911_ = lean_string_append(v___x_1908_, v___x_1910_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1913_ = lean_string_append(v___x_1911_, v___x_1912_);
return v___x_1913_;
}
else
{
lean_object* v_n_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_n_1914_ = lean_ctor_get(v_x_1906_, 0);
lean_inc(v_n_1914_);
lean_dec_ref_known(v_x_1906_, 1);
v___x_1915_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_n_1914_, v___x_1916_);
lean_dec(v_n_1914_);
v___x_1918_ = l_Nat_reprFast(v___x_1917_);
v___x_1919_ = lean_string_append(v___x_1915_, v___x_1918_);
lean_dec_ref(v___x_1918_);
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_env_1925_; lean_object* v___x_1926_; lean_object* v_toEnvExtension_1927_; lean_object* v_asyncMode_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v_merged_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v___x_1923_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1924_ = lean_st_ref_get(v___y_1921_);
v_env_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_env_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1927_ = lean_ctor_get(v___x_1926_, 0);
v_asyncMode_1928_ = lean_ctor_get(v_toEnvExtension_1927_, 2);
v___x_1929_ = lean_box(0);
v___x_1930_ = 0;
v___x_1931_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1923_, v___x_1926_, v_env_1925_, v_asyncMode_1928_, v___x_1929_, v___x_1930_);
v_merged_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1931_, 1);
lean_dec(v_unused_1941_);
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_merged_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v_merged_1932_);
lean_ctor_set(v___x_1934_, 0, v_o_1920_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_o_1920_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_merged_1932_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1942_, v___y_1943_);
lean_dec(v___y_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1946_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1956_, lean_object* v_opt_1957_){
_start:
{
lean_object* v_name_1958_; lean_object* v_defValue_1959_; lean_object* v_map_1960_; lean_object* v___x_1961_; 
v_name_1958_ = lean_ctor_get(v_opt_1957_, 0);
v_defValue_1959_ = lean_ctor_get(v_opt_1957_, 1);
v_map_1960_ = lean_ctor_get(v_opts_1956_, 0);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1960_, v_name_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_inc(v_defValue_1959_);
return v_defValue_1959_;
}
else
{
lean_object* v_val_1962_; 
v_val_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1962_);
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v_val_1962_) == 3)
{
lean_object* v_v_1963_; 
v_v_1963_ = lean_ctor_get(v_val_1962_, 0);
lean_inc(v_v_1963_);
lean_dec_ref_known(v_val_1962_, 1);
return v_v_1963_;
}
else
{
lean_dec(v_val_1962_);
lean_inc(v_defValue_1959_);
return v_defValue_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1964_, lean_object* v_opt_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1964_, v_opt_1965_);
lean_dec_ref(v_opt_1965_);
lean_dec_ref(v_opts_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_options_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1983_; 
v_options_1971_ = lean_ctor_get(v_c_1967_, 6);
lean_inc_ref(v_options_1971_);
lean_dec_ref(v_c_1967_);
v___x_1972_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1971_, v___y_1969_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1977_ = l_Lean_linter_doc_deferred;
v___x_1978_ = l_Lean_Linter_getLinterValue(v___x_1977_, v_a_1973_);
lean_dec(v_a_1973_);
v___x_1979_ = lean_box(v___x_1978_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1989_, lean_object* v_docCheckedModules_1990_, uint8_t v___y_1991_, lean_object* v_m_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1989_, v_m_1992_);
if (v___x_1993_ == 0)
{
return v___x_1993_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_NameSet_contains(v_docCheckedModules_1990_, v_m_1992_);
if (v___x_1994_ == 0)
{
return v___y_1991_;
}
else
{
uint8_t v___x_1995_; 
v___x_1995_ = 0;
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1996_, lean_object* v_docCheckedModules_1997_, lean_object* v___y_1998_, lean_object* v_m_1999_){
_start:
{
uint8_t v___y_7547__boxed_2000_; uint8_t v_res_2001_; lean_object* v_r_2002_; 
v___y_7547__boxed_2000_ = lean_unbox(v___y_1998_);
v_res_2001_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1996_, v_docCheckedModules_1997_, v___y_7547__boxed_2000_, v_m_1999_);
lean_dec(v_m_1999_);
lean_dec(v_docCheckedModules_1997_);
lean_dec(v_pkgRoot_1996_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t v___x_2010_, lean_object* v_sp_2011_, lean_object* v_as_2012_, size_t v_sz_2013_, size_t v_i_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_a_2020_; uint8_t v_unlocated_2024_; 
v_unlocated_2024_ = lean_usize_dec_lt(v_i_2014_, v_sz_2013_);
if (v_unlocated_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec(v_sp_2011_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_b_2015_);
return v___x_2025_;
}
else
{
lean_object* v_a_2026_; lean_object* v_snd_2027_; lean_object* v_fst_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2150_; 
v_a_2026_ = lean_array_uget_borrowed(v_as_2012_, v_i_2014_);
v_snd_2027_ = lean_ctor_get(v_a_2026_, 1);
lean_inc(v_snd_2027_);
v_fst_2028_ = lean_ctor_get(v_snd_2027_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_snd_2027_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_snd_2027_, 1);
lean_dec(v_unused_2151_);
v___x_2030_ = v_snd_2027_;
v_isShared_2031_ = v_isSharedCheck_2150_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_fst_2028_);
lean_dec(v_snd_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2150_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_fst_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2149_; 
v_fst_2032_ = lean_ctor_get(v_a_2026_, 0);
v_fst_2033_ = lean_ctor_get(v_b_2015_, 0);
v_snd_2034_ = lean_ctor_get(v_b_2015_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_b_2015_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2036_ = v_b_2015_;
v_isShared_2037_ = v_isSharedCheck_2149_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v_b_2015_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2149_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_site_2038_; lean_object* v___x_2039_; 
v_site_2038_ = lean_ctor_get(v_fst_2028_, 0);
lean_inc_ref_n(v_site_2038_, 2);
lean_dec(v_fst_2028_);
v___x_2039_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2032_, v_site_2038_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_a_2040_) == 0)
{
lean_object* v___x_2041_; lean_object* v_name_2042_; lean_object* v_ref_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec(v_snd_2034_);
v___x_2041_ = l_Lean_linter_doc_deferred;
v_name_2042_ = lean_ctor_get(v___x_2041_, 0);
v_ref_2043_ = lean_ctor_get(v___y_2016_, 2);
lean_inc(v_fst_2032_);
v___x_2044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2032_, v___x_2010_);
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0));
v___x_2046_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2038_);
v___x_2047_ = lean_string_append(v___x_2045_, v___x_2046_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1));
v___x_2049_ = lean_string_append(v___x_2047_, v___x_2048_);
v___x_2050_ = lean_string_append(v___x_2049_, v___x_2044_);
lean_dec_ref(v___x_2044_);
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
lean_inc(v_name_2042_);
v___x_2053_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2042_, v___x_2010_);
v___x_2054_ = lean_string_append(v___x_2052_, v___x_2053_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
v___x_2057_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2057_, 1);
lean_del_object(v___x_2030_);
v___x_2058_ = lean_box(v_unlocated_2024_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2058_);
v___x_2060_ = v___x_2036_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_fst_2033_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v_a_2020_ = v___x_2060_;
goto v___jp_2019_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2075_; 
lean_del_object(v___x_2036_);
lean_dec(v_fst_2033_);
lean_dec(v_sp_2011_);
v_a_2062_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2064_ = v___x_2057_;
v_isShared_2065_ = v_isSharedCheck_2075_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2057_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2075_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2066_ = lean_io_error_to_string(v_a_2062_);
v___x_2067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = l_Lean_MessageData_ofFormat(v___x_2067_);
lean_inc(v_ref_2043_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2068_);
lean_ctor_set(v___x_2030_, 0, v_ref_2043_);
v___x_2070_ = v___x_2030_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_ref_2043_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2070_);
v___x_2072_ = v___x_2064_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_site_2038_);
v_val_2076_ = lean_ctor_get(v_a_2040_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2078_ = v_a_2040_;
v_isShared_2079_ = v_isSharedCheck_2140_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_val_2076_);
lean_dec(v_a_2040_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2140_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_ref_2080_ = lean_ctor_get(v___y_2016_, 2);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2032_);
lean_inc(v_sp_2011_);
v___x_2082_ = l_Lean_SearchPath_findWithExt(v_sp_2011_, v___x_2081_, v_fst_2032_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
if (lean_obj_tag(v_a_2083_) == 0)
{
lean_object* v___x_2084_; lean_object* v_name_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_val_2076_);
lean_dec(v_snd_2034_);
v___x_2084_ = l_Lean_linter_doc_deferred;
v_name_2085_ = lean_ctor_get(v___x_2084_, 0);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
lean_inc(v_fst_2032_);
v___x_2087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2032_, v___x_2010_);
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
lean_inc(v_name_2085_);
v___x_2091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2085_, v___x_2010_);
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
v___x_2095_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
lean_dec_ref_known(v___x_2095_, 1);
lean_del_object(v___x_2078_);
lean_del_object(v___x_2030_);
v___x_2096_ = lean_box(v_unlocated_2024_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2096_);
v___x_2098_ = v___x_2036_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_fst_2033_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
v_a_2020_ = v___x_2098_;
goto v___jp_2019_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2115_; 
lean_del_object(v___x_2036_);
lean_dec(v_fst_2033_);
lean_dec(v_sp_2011_);
v_a_2100_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2102_ = v___x_2095_;
v_isShared_2103_ = v_isSharedCheck_2115_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2095_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2115_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_io_error_to_string(v_a_2100_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 3);
lean_ctor_set(v___x_2078_, 0, v___x_2104_);
v___x_2106_ = v___x_2078_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_MessageData_ofFormat(v___x_2106_);
lean_inc(v_ref_2080_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2107_);
lean_ctor_set(v___x_2030_, 0, v_ref_2080_);
v___x_2109_ = v___x_2030_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_ref_2080_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2109_);
v___x_2111_ = v___x_2102_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
else
{
lean_object* v_val_2116_; lean_object* v___x_2117_; lean_object* v_name_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_del_object(v___x_2078_);
lean_del_object(v___x_2030_);
v_val_2116_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_a_2083_, 1);
v___x_2117_ = l_Lean_linter_doc_deferred;
v_name_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_name_2118_);
v___x_2119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2119_, 0, v_val_2116_);
lean_ctor_set(v___x_2119_, 1, v_val_2076_);
lean_ctor_set(v___x_2119_, 2, v_name_2118_);
v___x_2120_ = lean_array_push(v_fst_2033_, v___x_2119_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2120_);
v___x_2122_ = v___x_2036_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2034_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
v_a_2020_ = v___x_2122_;
goto v___jp_2019_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_val_2076_);
lean_del_object(v___x_2036_);
lean_dec(v_snd_2034_);
lean_dec(v_fst_2033_);
lean_dec(v_sp_2011_);
v_a_2124_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2126_ = v___x_2082_;
v_isShared_2127_ = v_isSharedCheck_2139_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2082_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2139_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_io_error_to_string(v_a_2124_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 3);
lean_ctor_set(v___x_2078_, 0, v___x_2128_);
v___x_2130_ = v___x_2078_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_MessageData_ofFormat(v___x_2130_);
lean_inc(v_ref_2080_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2131_);
lean_ctor_set(v___x_2030_, 0, v_ref_2080_);
v___x_2133_ = v___x_2030_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_ref_2080_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2133_);
v___x_2135_ = v___x_2126_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
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
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_site_2038_);
lean_del_object(v___x_2036_);
lean_dec(v_snd_2034_);
lean_dec(v_fst_2033_);
lean_del_object(v___x_2030_);
lean_dec(v_sp_2011_);
v_a_2141_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2039_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2039_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
v___jp_2019_:
{
size_t v___x_2021_; size_t v___x_2022_; 
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2014_, v___x_2021_);
v_i_2014_ = v___x_2022_;
v_b_2015_ = v_a_2020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v___x_2152_, lean_object* v_sp_2153_, lean_object* v_as_2154_, lean_object* v_sz_2155_, lean_object* v_i_2156_, lean_object* v_b_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v___x_7571__boxed_2161_; size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v___x_7571__boxed_2161_ = lean_unbox(v___x_2152_);
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2155_);
lean_dec(v_sz_2155_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2156_);
lean_dec(v_i_2156_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_7571__boxed_2161_, v_sp_2153_, v_as_2154_, v_sz_boxed_2162_, v_i_boxed_2163_, v_b_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec_ref(v_as_2154_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object* v_sp_2171_, uint8_t v___y_2172_, lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_a_2180_; uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v_sp_2171_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_b_2176_);
return v___x_2185_;
}
else
{
lean_object* v_a_2186_; lean_object* v_snd_2187_; lean_object* v_fst_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2283_; 
v_a_2186_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
v_snd_2187_ = lean_ctor_get(v_a_2186_, 1);
lean_inc(v_snd_2187_);
v_fst_2188_ = lean_ctor_get(v_snd_2187_, 0);
lean_inc(v_fst_2188_);
v_fst_2189_ = lean_ctor_get(v_a_2186_, 0);
v_snd_2190_ = lean_ctor_get(v_snd_2187_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_snd_2187_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_snd_2187_, 0);
lean_dec(v_unused_2284_);
v___x_2192_ = v_snd_2187_;
v_isShared_2193_ = v_isSharedCheck_2283_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_dec(v_snd_2187_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2283_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v_site_2194_; lean_object* v_sourceString_2195_; lean_object* v___x_2196_; lean_object* v___y_2198_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_site_2194_ = lean_ctor_get(v_fst_2188_, 0);
lean_inc_ref(v_site_2194_);
v_sourceString_2195_ = lean_ctor_get(v_fst_2188_, 2);
lean_inc_ref(v_sourceString_2195_);
lean_dec(v_fst_2188_);
v___x_2196_ = lean_box(0);
v___x_2275_ = lean_string_utf8_byte_size(v_sourceString_2195_);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_nat_dec_eq(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4));
v___x_2279_ = lean_string_append(v___x_2278_, v_sourceString_2195_);
lean_dec_ref(v_sourceString_2195_);
v___x_2280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5));
v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
v___y_2198_ = v___x_2281_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2282_; 
lean_dec_ref(v_sourceString_2195_);
v___x_2282_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2198_ = v___x_2282_;
goto v___jp_2197_;
}
v___jp_2197_:
{
lean_object* v_ref_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_ref_2199_ = lean_ctor_get(v___y_2177_, 2);
v___x_2200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2189_);
lean_inc(v_sp_2171_);
v___x_2201_ = l_Lean_SearchPath_findWithExt(v_sp_2171_, v___x_2200_, v_fst_2189_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
if (lean_obj_tag(v_a_2202_) == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2203_ = l_Lean_MessageData_toString(v_snd_2190_);
v___x_2204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0));
lean_inc(v_fst_2189_);
v___x_2205_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2189_, v___y_2172_);
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1));
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
v___x_2209_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2194_);
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = lean_string_append(v___x_2210_, v___y_2198_);
lean_dec_ref(v___y_2198_);
v___x_2212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
v___x_2214_ = lean_string_append(v___x_2213_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2215_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_dec_ref_known(v___x_2215_, 1);
lean_del_object(v___x_2192_);
v_a_2180_ = v___x_2196_;
goto v___jp_2179_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_sp_2171_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2220_ = lean_io_error_to_string(v_a_2216_);
v___x_2221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
v___x_2222_ = l_Lean_MessageData_ofFormat(v___x_2221_);
lean_inc(v_ref_2199_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2222_);
lean_ctor_set(v___x_2192_, 0, v_ref_2199_);
v___x_2224_ = v___x_2192_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_ref_2199_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2224_);
v___x_2226_ = v___x_2218_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_val_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2260_; 
v_val_2230_ = lean_ctor_get(v_a_2202_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2232_ = v_a_2202_;
v_isShared_2233_ = v_isSharedCheck_2260_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_val_2230_);
lean_dec(v_a_2202_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2260_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2234_ = l_Lean_MessageData_toString(v_snd_2190_);
v___x_2235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3));
v___x_2236_ = lean_string_append(v_val_2230_, v___x_2235_);
v___x_2237_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2194_);
v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_string_append(v___x_2238_, v___y_2198_);
lean_dec_ref(v___y_2198_);
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2241_ = lean_string_append(v___x_2239_, v___x_2240_);
v___x_2242_ = lean_string_append(v___x_2241_, v___x_2234_);
lean_dec_ref(v___x_2234_);
v___x_2243_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_dec_ref_known(v___x_2243_, 1);
lean_del_object(v___x_2232_);
lean_del_object(v___x_2192_);
v_a_2180_ = v___x_2196_;
goto v___jp_2179_;
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_sp_2171_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2259_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2259_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_io_error_to_string(v_a_2244_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 3);
lean_ctor_set(v___x_2232_, 0, v___x_2248_);
v___x_2250_ = v___x_2232_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = l_Lean_MessageData_ofFormat(v___x_2250_);
lean_inc(v_ref_2199_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2251_);
lean_ctor_set(v___x_2192_, 0, v_ref_2199_);
v___x_2253_ = v___x_2192_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_ref_2199_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2253_);
v___x_2255_ = v___x_2246_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
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
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_site_2194_);
lean_dec(v_snd_2190_);
lean_dec(v_sp_2171_);
v_a_2261_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2263_ = v___x_2201_;
v_isShared_2264_ = v_isSharedCheck_2274_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2201_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2274_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2265_ = lean_io_error_to_string(v_a_2261_);
v___x_2266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = l_Lean_MessageData_ofFormat(v___x_2266_);
lean_inc(v_ref_2199_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2267_);
lean_ctor_set(v___x_2192_, 0, v_ref_2199_);
v___x_2269_ = v___x_2192_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_ref_2199_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2269_);
v___x_2271_ = v___x_2263_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
v___jp_2179_:
{
size_t v___x_2181_; size_t v___x_2182_; 
v___x_2181_ = ((size_t)1ULL);
v___x_2182_ = lean_usize_add(v_i_2175_, v___x_2181_);
v_i_2175_ = v___x_2182_;
v_b_2176_ = v_a_2180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object* v_sp_2285_, lean_object* v___y_2286_, lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v___y_7853__boxed_2293_; size_t v_sz_boxed_2294_; size_t v_i_boxed_2295_; lean_object* v_res_2296_; 
v___y_7853__boxed_2293_ = lean_unbox(v___y_2286_);
v_sz_boxed_2294_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2295_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2285_, v___y_7853__boxed_2293_, v_as_2287_, v_sz_boxed_2294_, v_i_boxed_2295_, v_b_2290_, v___y_2291_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_as_2287_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2297_, lean_object* v_as_2298_, size_t v_sz_2299_, size_t v_i_2300_, lean_object* v_b_2301_){
_start:
{
lean_object* v_a_2304_; uint8_t v___x_2308_; 
v___x_2308_ = lean_usize_dec_lt(v_i_2300_, v_sz_2299_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_b_2301_);
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; uint8_t v___x_2311_; 
v_a_2310_ = lean_array_uget_borrowed(v_as_2298_, v_i_2300_);
v___x_2311_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2297_, v_a_2310_);
if (v___x_2311_ == 0)
{
v_a_2304_ = v_b_2301_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2312_; 
lean_inc(v_a_2310_);
v___x_2312_ = l_Lean_NameSet_insert(v_b_2301_, v_a_2310_);
v_a_2304_ = v___x_2312_;
goto v___jp_2303_;
}
}
v___jp_2303_:
{
size_t v___x_2305_; size_t v___x_2306_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2300_, v___x_2305_);
v_i_2300_ = v___x_2306_;
v_b_2301_ = v_a_2304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2313_, lean_object* v_as_2314_, lean_object* v_sz_2315_, lean_object* v_i_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_){
_start:
{
size_t v_sz_boxed_2319_; size_t v_i_boxed_2320_; lean_object* v_res_2321_; 
v_sz_boxed_2319_ = lean_unbox_usize(v_sz_2315_);
lean_dec(v_sz_2315_);
v_i_boxed_2320_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_res_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2313_, v_as_2314_, v_sz_boxed_2319_, v_i_boxed_2320_, v_b_2317_);
lean_dec_ref(v_as_2314_);
lean_dec(v_pkgRoot_2313_);
return v_res_2321_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = l_Lean_Options_empty;
v___x_2329_ = l_Lean_Core_getMaxHeartbeats(v___x_2328_);
return v___x_2329_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2330_; uint16_t v___x_2331_; 
v___x_2330_ = l_Lean_Options_empty;
v___x_2331_ = l_Lean_OptionFlags_ofOptions(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = l_Lean_firstFrontendMacroScope;
v___x_2334_ = lean_nat_add(v___x_2333_, v___x_2332_);
return v___x_2334_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_unsigned_to_nat(32u);
v___x_2346_ = lean_mk_empty_array_with_capacity(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
size_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2348_ = ((size_t)5ULL);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_unsigned_to_nat(32u);
v___x_2351_ = lean_mk_empty_array_with_capacity(v___x_2350_);
v___x_2352_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2353_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___x_2351_);
lean_ctor_set(v___x_2353_, 2, v___x_2349_);
lean_ctor_set(v___x_2353_, 3, v___x_2349_);
lean_ctor_set_usize(v___x_2353_, 4, v___x_2348_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2354_; uint64_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2355_ = 0ULL;
v___x_2356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint64(v___x_2356_, sizeof(void*)*1, v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = l_Lean_Options_empty;
v___x_2364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2365_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
lean_ctor_set(v___x_2365_, 1, v___x_2363_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
lean_ctor_set(v___x_2365_, 3, v___x_2362_);
lean_ctor_set(v___x_2365_, 4, v___x_2362_);
lean_ctor_set(v___x_2365_, 5, v___x_2362_);
lean_ctor_set(v___x_2365_, 6, v___x_2364_);
lean_ctor_set(v___x_2365_, 7, v___x_2364_);
return v___x_2365_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = l_Lean_NameSet_empty;
v___x_2367_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v_unlocated_2371_; lean_object* v___x_2372_; 
v___x_2369_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2370_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v_unlocated_2371_ = 1;
v___x_2372_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2370_);
lean_ctor_set(v___x_2372_, 2, v___x_2369_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*3, v_unlocated_2371_);
return v___x_2372_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21(void){
_start:
{
uint16_t v___x_2373_; uint16_t v___x_2374_; uint16_t v___x_2375_; 
v___x_2373_ = 512;
v___x_2374_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2375_ = lean_uint16_land(v___x_2374_, v___x_2373_);
return v___x_2375_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22(void){
_start:
{
uint16_t v___x_2376_; uint16_t v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = 0;
v___x_2377_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21);
v___x_2378_ = lean_uint16_dec_eq(v___x_2377_, v___x_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2379_, lean_object* v_linterOpts_2380_, lean_object* v_sp_2381_, lean_object* v_env_2382_, lean_object* v_pkgRoot_2383_, lean_object* v_docCheckedModules_2384_){
_start:
{
lean_object* v___y_2387_; lean_object* v_a_2391_; uint8_t v___y_2395_; lean_object* v_a_2396_; lean_object* v___y_2413_; lean_object* v_a_2414_; lean_object* v___y_2439_; uint8_t v___y_2440_; uint8_t v_lintOnly_2442_; uint8_t v_mode_2443_; lean_object* v___f_2444_; lean_object* v___y_2446_; lean_object* v___y_2447_; uint8_t v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; uint16_t v___y_2452_; lean_object* v_fileName_2453_; lean_object* v_fileMap_2454_; lean_object* v_currNamespace_2455_; lean_object* v_openDecls_2456_; lean_object* v_initHeartbeats_2457_; lean_object* v_maxHeartbeats_2458_; lean_object* v_quotContext_2459_; lean_object* v_currMacroScope_2460_; lean_object* v_cancelTk_x3f_2461_; lean_object* v_inheritedTraceOptions_2462_; lean_object* v_currRecDepth_2463_; lean_object* v_ref_2464_; uint8_t v_suppressElabErrors_2465_; uint8_t v_checkDeprecated_2466_; uint8_t v_isRecordingDeps_2467_; lean_object* v___y_2468_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; uint16_t v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2545_; 
v_lintOnly_2442_ = lean_ctor_get_uint8(v_args_2379_, sizeof(void*)*4);
v_mode_2443_ = lean_ctor_get_uint8(v_args_2379_, sizeof(void*)*4 + 1);
v___f_2444_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2442_ == 0)
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = l_Lean_linter_doc_deferred;
v___x_2588_ = l_Lean_Linter_getLinterValue(v___x_2587_, v_linterOpts_2380_);
v___y_2545_ = v___x_2588_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2589_; lean_object* v_name_2590_; uint8_t v___x_2591_; 
v___x_2589_ = l_Lean_linter_doc_deferred;
v_name_2590_ = lean_ctor_get(v___x_2589_, 0);
v___x_2591_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2590_, v_linterOpts_2380_);
v___y_2545_ = v___x_2591_;
goto v___jp_2544_;
}
v___jp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2387_);
lean_ctor_set(v___x_2388_, 1, v_docCheckedModules_2384_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
v___jp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_mk_io_user_error(v_a_2391_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
v___jp_2394_:
{
if (lean_obj_tag(v_a_2396_) == 0)
{
lean_object* v_msg_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_msg_2397_ = lean_ctor_get(v_a_2396_, 1);
lean_inc_ref(v_msg_2397_);
lean_dec_ref_known(v_a_2396_, 2);
v___x_2398_ = l_Lean_MessageData_toString(v_msg_2397_);
v___x_2399_ = lean_mk_io_user_error(v___x_2398_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
else
{
lean_object* v_id_2401_; lean_object* v___x_2402_; 
v_id_2401_ = lean_ctor_get(v_a_2396_, 0);
lean_inc(v_id_2401_);
lean_dec_ref_known(v_a_2396_, 2);
v___x_2402_ = l_Lean_InternalExceptionId_getName(v_id_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec(v_id_2401_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2405_ = l_Lean_Name_toString(v_a_2403_, v___y_2395_);
v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
lean_dec_ref(v___x_2405_);
v_a_2391_ = v___x_2406_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec_ref_known(v___x_2402_, 1);
v___x_2407_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2408_ = l_Nat_reprFast(v_id_2401_);
v___x_2409_ = lean_string_append(v___x_2407_, v___x_2408_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2411_ = lean_string_append(v___x_2409_, v___x_2410_);
v_a_2391_ = v___x_2411_;
goto v___jp_2390_;
}
}
}
v___jp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_moduleNames_2417_; size_t v_sz_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2415_ = lean_st_ref_get(v___y_2413_);
lean_dec(v___y_2413_);
lean_dec(v___x_2415_);
v___x_2416_ = l_Lean_Environment_header(v_env_2382_);
lean_dec_ref(v_env_2382_);
v_moduleNames_2417_ = lean_ctor_get(v___x_2416_, 4);
lean_inc_ref(v_moduleNames_2417_);
lean_dec_ref(v___x_2416_);
v_sz_2418_ = lean_array_size(v_moduleNames_2417_);
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2383_, v_moduleNames_2417_, v_sz_2418_, v___x_2419_, v_docCheckedModules_2384_);
lean_dec_ref(v_moduleNames_2417_);
lean_dec(v_pkgRoot_2383_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_a_2414_);
lean_ctor_set(v___x_2425_, 1, v_a_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v_a_2414_);
v_a_2430_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2420_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2420_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2441_, 0, v___y_2440_);
v___y_2413_ = v___y_2439_;
v_a_2414_ = v___x_2441_;
goto v___jp_2412_;
}
v___jp_2445_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2469_ = l_Lean_maxRecDepth;
v___x_2470_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_2446_, v___x_2469_);
lean_inc_ref(v___y_2446_);
v___x_2471_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2471_, 0, v_fileName_2453_);
lean_ctor_set(v___x_2471_, 1, v_fileMap_2454_);
lean_ctor_set(v___x_2471_, 2, v___y_2446_);
lean_ctor_set(v___x_2471_, 3, v___x_2470_);
lean_ctor_set(v___x_2471_, 4, v_currNamespace_2455_);
lean_ctor_set(v___x_2471_, 5, v_openDecls_2456_);
lean_ctor_set(v___x_2471_, 6, v_initHeartbeats_2457_);
lean_ctor_set(v___x_2471_, 7, v_maxHeartbeats_2458_);
lean_ctor_set(v___x_2471_, 8, v_quotContext_2459_);
lean_ctor_set(v___x_2471_, 9, v_currMacroScope_2460_);
lean_ctor_set(v___x_2471_, 10, v_cancelTk_x3f_2461_);
lean_ctor_set(v___x_2471_, 11, v_inheritedTraceOptions_2462_);
v___x_2472_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v_currRecDepth_2463_);
lean_ctor_set(v___x_2472_, 2, v_ref_2464_);
lean_ctor_set_uint16(v___x_2472_, sizeof(void*)*3, v___y_2452_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*3 + 2, v_suppressElabErrors_2465_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*3 + 3, v_checkDeprecated_2466_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*3 + 4, v_isRecordingDeps_2467_);
v___x_2473_ = l_Lean_Doc_DeferredCheck_run(v___y_2447_, v___f_2444_, v___x_2472_, v___y_2468_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; uint8_t v___x_2475_; uint8_t v___x_2476_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = 1;
v___x_2476_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2443_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; size_t v_sz_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v___y_2468_);
v___x_2477_ = lean_box(0);
v_sz_2478_ = lean_array_size(v_a_2474_);
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2381_, v___y_2448_, v_a_2474_, v_sz_2478_, v___x_2479_, v___x_2477_, v___x_2472_);
lean_dec_ref_known(v___x_2472_, 3);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
lean_dec_ref_known(v___x_2480_, 1);
v___x_2481_ = lean_array_get_size(v_a_2474_);
lean_dec(v_a_2474_);
v___x_2482_ = lean_nat_dec_eq(v___x_2481_, v___y_2451_);
lean_dec(v___y_2451_);
if (v___x_2482_ == 0)
{
v___y_2439_ = v___y_2450_;
v___y_2440_ = v___y_2448_;
goto v___jp_2438_;
}
else
{
v___y_2439_ = v___y_2450_;
v___y_2440_ = v___x_2476_;
goto v___jp_2438_;
}
}
else
{
lean_object* v_a_2483_; 
lean_dec(v_a_2474_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v_docCheckedModules_2384_);
lean_dec(v_pkgRoot_2383_);
lean_dec_ref(v_env_2382_);
v_a_2483_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2480_, 1);
v___y_2395_ = v___y_2448_;
v_a_2396_ = v_a_2483_;
goto v___jp_2394_;
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; size_t v_sz_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2484_ = lean_mk_empty_array_with_capacity(v___y_2451_);
lean_dec(v___y_2451_);
v___x_2485_ = lean_box(v___y_2449_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v_sz_2487_ = lean_array_size(v_a_2474_);
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2476_, v_sp_2381_, v_a_2474_, v_sz_2487_, v___x_2488_, v___x_2486_, v___x_2472_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref_known(v___x_2472_, 3);
lean_dec(v_a_2474_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v_fst_2491_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_fst_2491_);
v_snd_2492_ = lean_ctor_get(v_a_2490_, 1);
lean_inc(v_snd_2492_);
lean_dec(v_a_2490_);
v___x_2493_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2493_, 0, v_fst_2491_);
v___x_2494_ = lean_unbox(v_snd_2492_);
lean_dec(v_snd_2492_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2494_);
v___y_2413_ = v___y_2450_;
v_a_2414_ = v___x_2493_;
goto v___jp_2412_;
}
else
{
lean_object* v_a_2495_; 
lean_dec(v___y_2450_);
lean_dec(v_docCheckedModules_2384_);
lean_dec(v_pkgRoot_2383_);
lean_dec_ref(v_env_2382_);
v_a_2495_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2489_, 1);
v___y_2395_ = v___y_2448_;
v_a_2396_ = v_a_2495_;
goto v___jp_2394_;
}
}
}
else
{
lean_object* v_a_2496_; 
lean_dec_ref_known(v___x_2472_, 3);
lean_dec(v___y_2468_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v_docCheckedModules_2384_);
lean_dec(v_pkgRoot_2383_);
lean_dec_ref(v_env_2382_);
lean_dec(v_sp_2381_);
v_a_2496_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2473_, 1);
v___y_2395_ = v___y_2448_;
v_a_2396_ = v_a_2496_;
goto v___jp_2394_;
}
}
v___jp_2497_:
{
lean_object* v___x_2508_; lean_object* v_env_2509_; lean_object* v_nextMacroScope_2510_; lean_object* v_ngen_2511_; lean_object* v_auxDeclNGen_2512_; lean_object* v_traceState_2513_; lean_object* v_recordedDeps_2514_; lean_object* v_messages_2515_; lean_object* v_infoState_2516_; lean_object* v_snapshotTasks_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2542_; 
v___x_2508_ = lean_st_ref_take(v___y_2503_);
v_env_2509_ = lean_ctor_get(v___x_2508_, 0);
v_nextMacroScope_2510_ = lean_ctor_get(v___x_2508_, 1);
v_ngen_2511_ = lean_ctor_get(v___x_2508_, 2);
v_auxDeclNGen_2512_ = lean_ctor_get(v___x_2508_, 3);
v_traceState_2513_ = lean_ctor_get(v___x_2508_, 4);
v_recordedDeps_2514_ = lean_ctor_get(v___x_2508_, 6);
v_messages_2515_ = lean_ctor_get(v___x_2508_, 7);
v_infoState_2516_ = lean_ctor_get(v___x_2508_, 8);
v_snapshotTasks_2517_ = lean_ctor_get(v___x_2508_, 9);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2508_, 5);
lean_dec(v_unused_2543_);
v___x_2519_ = v___x_2508_;
v_isShared_2520_ = v_isSharedCheck_2542_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_snapshotTasks_2517_);
lean_inc(v_infoState_2516_);
lean_inc(v_messages_2515_);
lean_inc(v_recordedDeps_2514_);
lean_inc(v_traceState_2513_);
lean_inc(v_auxDeclNGen_2512_);
lean_inc(v_ngen_2511_);
lean_inc(v_nextMacroScope_2510_);
lean_inc(v_env_2509_);
lean_dec(v___x_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2542_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = l_Lean_Kernel_enableDiag(v_env_2509_, v___y_2506_);
lean_inc_ref(v___y_2507_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 5, v___y_2507_);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_nextMacroScope_2510_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_ngen_2511_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_auxDeclNGen_2512_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_traceState_2513_);
lean_ctor_set(v_reuseFailAlloc_2541_, 5, v___y_2507_);
lean_ctor_set(v_reuseFailAlloc_2541_, 6, v_recordedDeps_2514_);
lean_ctor_set(v_reuseFailAlloc_2541_, 7, v_messages_2515_);
lean_ctor_set(v_reuseFailAlloc_2541_, 8, v_infoState_2516_);
lean_ctor_set(v_reuseFailAlloc_2541_, 9, v_snapshotTasks_2517_);
v___x_2523_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v_toCold_2525_; lean_object* v_currRecDepth_2526_; lean_object* v_ref_2527_; uint8_t v_suppressElabErrors_2528_; uint8_t v_checkDeprecated_2529_; uint8_t v_isRecordingDeps_2530_; lean_object* v_fileName_2531_; lean_object* v_fileMap_2532_; lean_object* v_currNamespace_2533_; lean_object* v_openDecls_2534_; lean_object* v_initHeartbeats_2535_; lean_object* v_maxHeartbeats_2536_; lean_object* v_quotContext_2537_; lean_object* v_currMacroScope_2538_; lean_object* v_cancelTk_x3f_2539_; lean_object* v_inheritedTraceOptions_2540_; 
v___x_2524_ = lean_st_ref_put(v___y_2503_, v___x_2523_);
v_toCold_2525_ = lean_ctor_get(v___y_2499_, 0);
lean_inc_ref(v_toCold_2525_);
v_currRecDepth_2526_ = lean_ctor_get(v___y_2499_, 1);
lean_inc(v_currRecDepth_2526_);
v_ref_2527_ = lean_ctor_get(v___y_2499_, 2);
lean_inc(v_ref_2527_);
v_suppressElabErrors_2528_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 2);
v_checkDeprecated_2529_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2530_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_2499_);
v_fileName_2531_ = lean_ctor_get(v_toCold_2525_, 0);
lean_inc_ref(v_fileName_2531_);
v_fileMap_2532_ = lean_ctor_get(v_toCold_2525_, 1);
lean_inc_ref(v_fileMap_2532_);
v_currNamespace_2533_ = lean_ctor_get(v_toCold_2525_, 4);
lean_inc(v_currNamespace_2533_);
v_openDecls_2534_ = lean_ctor_get(v_toCold_2525_, 5);
lean_inc(v_openDecls_2534_);
v_initHeartbeats_2535_ = lean_ctor_get(v_toCold_2525_, 6);
lean_inc(v_initHeartbeats_2535_);
v_maxHeartbeats_2536_ = lean_ctor_get(v_toCold_2525_, 7);
lean_inc(v_maxHeartbeats_2536_);
v_quotContext_2537_ = lean_ctor_get(v_toCold_2525_, 8);
lean_inc(v_quotContext_2537_);
v_currMacroScope_2538_ = lean_ctor_get(v_toCold_2525_, 9);
lean_inc(v_currMacroScope_2538_);
v_cancelTk_x3f_2539_ = lean_ctor_get(v_toCold_2525_, 10);
lean_inc(v_cancelTk_x3f_2539_);
v_inheritedTraceOptions_2540_ = lean_ctor_get(v_toCold_2525_, 11);
lean_inc_ref(v_inheritedTraceOptions_2540_);
lean_dec_ref(v_toCold_2525_);
lean_inc(v___y_2503_);
v___y_2446_ = v___y_2498_;
v___y_2447_ = v___y_2500_;
v___y_2448_ = v___y_2501_;
v___y_2449_ = v___y_2502_;
v___y_2450_ = v___y_2503_;
v___y_2451_ = v___y_2504_;
v___y_2452_ = v___y_2505_;
v_fileName_2453_ = v_fileName_2531_;
v_fileMap_2454_ = v_fileMap_2532_;
v_currNamespace_2455_ = v_currNamespace_2533_;
v_openDecls_2456_ = v_openDecls_2534_;
v_initHeartbeats_2457_ = v_initHeartbeats_2535_;
v_maxHeartbeats_2458_ = v_maxHeartbeats_2536_;
v_quotContext_2459_ = v_quotContext_2537_;
v_currMacroScope_2460_ = v_currMacroScope_2538_;
v_cancelTk_x3f_2461_ = v_cancelTk_x3f_2539_;
v_inheritedTraceOptions_2462_ = v_inheritedTraceOptions_2540_;
v_currRecDepth_2463_ = v_currRecDepth_2526_;
v_ref_2464_ = v_ref_2527_;
v_suppressElabErrors_2465_ = v_suppressElabErrors_2528_;
v_checkDeprecated_2466_ = v_checkDeprecated_2529_;
v_isRecordingDeps_2467_ = v_isRecordingDeps_2530_;
v___y_2468_ = v___y_2503_;
goto v___jp_2445_;
}
}
}
v___jp_2544_:
{
if (v___y_2545_ == 0)
{
uint8_t v___x_2546_; uint8_t v___x_2547_; 
lean_dec(v_pkgRoot_2383_);
lean_dec_ref(v_env_2382_);
lean_dec(v_sp_2381_);
v___x_2546_ = 1;
v___x_2547_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2443_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2548_, 0, v___x_2547_);
v___y_2387_ = v___x_2548_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2550_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*1, v___y_2545_);
v___y_2387_ = v___x_2550_;
goto v___jp_2386_;
}
}
else
{
lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint16_t v___x_2564_; uint8_t v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_env_2584_; uint8_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2551_ = lean_box(v___y_2545_);
lean_inc(v_docCheckedModules_2384_);
lean_inc(v_pkgRoot_2383_);
v___f_2552_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2552_, 0, v_pkgRoot_2383_);
lean_closure_set(v___f_2552_, 1, v_docCheckedModules_2384_);
lean_closure_set(v___f_2552_, 2, v___x_2551_);
v___x_2553_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2554_ = l_Lean_instInhabitedFileMap_default;
v___x_2555_ = l_Lean_Options_empty;
v___x_2556_ = lean_unsigned_to_nat(1000u);
v___x_2557_ = lean_box(0);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2561_ = l_Lean_firstFrontendMacroScope;
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2565_ = 0;
v___x_2566_ = 0;
v___x_2567_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2568_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2569_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_2570_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2571_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2573_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2574_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2575_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
lean_inc_ref(v_env_2382_);
v___x_2576_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2576_, 0, v_env_2382_);
lean_ctor_set(v___x_2576_, 1, v___x_2567_);
lean_ctor_set(v___x_2576_, 2, v___x_2568_);
lean_ctor_set(v___x_2576_, 3, v___x_2569_);
lean_ctor_set(v___x_2576_, 4, v___x_2570_);
lean_ctor_set(v___x_2576_, 5, v___x_2571_);
lean_ctor_set(v___x_2576_, 6, v___x_2573_);
lean_ctor_set(v___x_2576_, 7, v___x_2574_);
lean_ctor_set(v___x_2576_, 8, v___x_2575_);
lean_ctor_set(v___x_2576_, 9, v___x_2572_);
v___x_2577_ = lean_io_get_num_heartbeats();
v___x_2578_ = lean_st_mk_ref(v___x_2576_);
v___x_2579_ = l_Lean_inheritedTraceOptions;
v___x_2580_ = lean_st_ref_get(v___x_2579_);
lean_inc(v___x_2580_);
lean_inc(v___x_2577_);
v___x_2581_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2553_);
lean_ctor_set(v___x_2581_, 1, v___x_2554_);
lean_ctor_set(v___x_2581_, 2, v___x_2555_);
lean_ctor_set(v___x_2581_, 3, v___x_2556_);
lean_ctor_set(v___x_2581_, 4, v___x_2557_);
lean_ctor_set(v___x_2581_, 5, v___x_2558_);
lean_ctor_set(v___x_2581_, 6, v___x_2577_);
lean_ctor_set(v___x_2581_, 7, v___x_2560_);
lean_ctor_set(v___x_2581_, 8, v___x_2557_);
lean_ctor_set(v___x_2581_, 9, v___x_2561_);
lean_ctor_set(v___x_2581_, 10, v___x_2562_);
lean_ctor_set(v___x_2581_, 11, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___x_2559_);
lean_ctor_set(v___x_2582_, 2, v___x_2563_);
lean_ctor_set_uint16(v___x_2582_, sizeof(void*)*3, v___x_2564_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3 + 2, v___x_2565_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3 + 3, v___x_2566_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3 + 4, v___x_2565_);
v___x_2583_ = lean_st_ref_get(v___x_2578_);
v_env_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc_ref(v_env_2584_);
lean_dec(v___x_2583_);
v___x_2585_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2584_);
lean_dec_ref(v_env_2584_);
v___x_2586_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_2586_ == 0)
{
if (v___x_2585_ == 0)
{
lean_dec(v___x_2580_);
lean_dec(v___x_2577_);
v___y_2498_ = v___x_2555_;
v___y_2499_ = v___x_2582_;
v___y_2500_ = v___f_2552_;
v___y_2501_ = v___y_2545_;
v___y_2502_ = v___x_2565_;
v___y_2503_ = v___x_2578_;
v___y_2504_ = v___x_2559_;
v___y_2505_ = v___x_2564_;
v___y_2506_ = v___y_2545_;
v___y_2507_ = v___x_2571_;
goto v___jp_2497_;
}
else
{
lean_dec_ref_known(v___x_2582_, 3);
lean_inc(v___x_2578_);
v___y_2446_ = v___x_2555_;
v___y_2447_ = v___f_2552_;
v___y_2448_ = v___y_2545_;
v___y_2449_ = v___x_2565_;
v___y_2450_ = v___x_2578_;
v___y_2451_ = v___x_2559_;
v___y_2452_ = v___x_2564_;
v_fileName_2453_ = v___x_2553_;
v_fileMap_2454_ = v___x_2554_;
v_currNamespace_2455_ = v___x_2557_;
v_openDecls_2456_ = v___x_2558_;
v_initHeartbeats_2457_ = v___x_2577_;
v_maxHeartbeats_2458_ = v___x_2560_;
v_quotContext_2459_ = v___x_2557_;
v_currMacroScope_2460_ = v___x_2561_;
v_cancelTk_x3f_2461_ = v___x_2562_;
v_inheritedTraceOptions_2462_ = v___x_2580_;
v_currRecDepth_2463_ = v___x_2559_;
v_ref_2464_ = v___x_2563_;
v_suppressElabErrors_2465_ = v___x_2565_;
v_checkDeprecated_2466_ = v___x_2566_;
v_isRecordingDeps_2467_ = v___x_2565_;
v___y_2468_ = v___x_2578_;
goto v___jp_2445_;
}
}
else
{
if (v___x_2585_ == 0)
{
lean_dec_ref_known(v___x_2582_, 3);
lean_inc(v___x_2578_);
v___y_2446_ = v___x_2555_;
v___y_2447_ = v___f_2552_;
v___y_2448_ = v___y_2545_;
v___y_2449_ = v___x_2565_;
v___y_2450_ = v___x_2578_;
v___y_2451_ = v___x_2559_;
v___y_2452_ = v___x_2564_;
v_fileName_2453_ = v___x_2553_;
v_fileMap_2454_ = v___x_2554_;
v_currNamespace_2455_ = v___x_2557_;
v_openDecls_2456_ = v___x_2558_;
v_initHeartbeats_2457_ = v___x_2577_;
v_maxHeartbeats_2458_ = v___x_2560_;
v_quotContext_2459_ = v___x_2557_;
v_currMacroScope_2460_ = v___x_2561_;
v_cancelTk_x3f_2461_ = v___x_2562_;
v_inheritedTraceOptions_2462_ = v___x_2580_;
v_currRecDepth_2463_ = v___x_2559_;
v_ref_2464_ = v___x_2563_;
v_suppressElabErrors_2465_ = v___x_2565_;
v_checkDeprecated_2466_ = v___x_2566_;
v_isRecordingDeps_2467_ = v___x_2565_;
v___y_2468_ = v___x_2578_;
goto v___jp_2445_;
}
else
{
lean_dec(v___x_2580_);
lean_dec(v___x_2577_);
v___y_2498_ = v___x_2555_;
v___y_2499_ = v___x_2582_;
v___y_2500_ = v___f_2552_;
v___y_2501_ = v___y_2545_;
v___y_2502_ = v___x_2565_;
v___y_2503_ = v___x_2578_;
v___y_2504_ = v___x_2559_;
v___y_2505_ = v___x_2564_;
v___y_2506_ = v___x_2565_;
v___y_2507_ = v___x_2571_;
goto v___jp_2497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2592_, lean_object* v_linterOpts_2593_, lean_object* v_sp_2594_, lean_object* v_env_2595_, lean_object* v_pkgRoot_2596_, lean_object* v_docCheckedModules_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2592_, v_linterOpts_2593_, v_sp_2594_, v_env_2595_, v_pkgRoot_2596_, v_docCheckedModules_2597_);
lean_dec_ref(v_linterOpts_2593_);
lean_dec_ref(v_args_2592_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_sp_2600_, uint8_t v___y_2601_, lean_object* v_as_2602_, size_t v_sz_2603_, size_t v_i_2604_, lean_object* v_b_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2600_, v___y_2601_, v_as_2602_, v_sz_2603_, v_i_2604_, v_b_2605_, v___y_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_sp_2610_, lean_object* v___y_2611_, lean_object* v_as_2612_, lean_object* v_sz_2613_, lean_object* v_i_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
uint8_t v___y_8603__boxed_2619_; size_t v_sz_boxed_2620_; size_t v_i_boxed_2621_; lean_object* v_res_2622_; 
v___y_8603__boxed_2619_ = lean_unbox(v___y_2611_);
v_sz_boxed_2620_ = lean_unbox_usize(v_sz_2613_);
lean_dec(v_sz_2613_);
v_i_boxed_2621_ = lean_unbox_usize(v_i_2614_);
lean_dec(v_i_2614_);
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2610_, v___y_8603__boxed_2619_, v_as_2612_, v_sz_boxed_2620_, v_i_boxed_2621_, v_b_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec_ref(v_as_2612_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2623_, lean_object* v_as_2624_, size_t v_i_2625_, size_t v_stop_2626_, lean_object* v_b_2627_){
_start:
{
lean_object* v___y_2629_; uint8_t v___x_2633_; 
v___x_2633_ = lean_usize_dec_eq(v_i_2625_, v_stop_2626_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v_linter_2635_; uint8_t v___x_2636_; 
v___x_2634_ = lean_array_uget_borrowed(v_as_2624_, v_i_2625_);
v_linter_2635_ = lean_ctor_get(v___x_2634_, 0);
v___x_2636_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2635_, v_linterOpts_2623_);
if (v___x_2636_ == 0)
{
v___y_2629_ = v_b_2627_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2637_; 
lean_inc(v___x_2634_);
v___x_2637_ = lean_array_push(v_b_2627_, v___x_2634_);
v___y_2629_ = v___x_2637_;
goto v___jp_2628_;
}
}
else
{
return v_b_2627_;
}
v___jp_2628_:
{
size_t v___x_2630_; size_t v___x_2631_; 
v___x_2630_ = ((size_t)1ULL);
v___x_2631_ = lean_usize_add(v_i_2625_, v___x_2630_);
v_i_2625_ = v___x_2631_;
v_b_2627_ = v___y_2629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2638_, lean_object* v_as_2639_, lean_object* v_i_2640_, lean_object* v_stop_2641_, lean_object* v_b_2642_){
_start:
{
size_t v_i_boxed_2643_; size_t v_stop_boxed_2644_; lean_object* v_res_2645_; 
v_i_boxed_2643_ = lean_unbox_usize(v_i_2640_);
lean_dec(v_i_2640_);
v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2641_);
lean_dec(v_stop_2641_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2638_, v_as_2639_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2642_);
lean_dec_ref(v_as_2639_);
lean_dec_ref(v_linterOpts_2638_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2648_, lean_object* v_as_2649_, size_t v_i_2650_, size_t v_stop_2651_, lean_object* v_b_2652_){
_start:
{
lean_object* v___y_2654_; uint8_t v___x_2658_; 
v___x_2658_ = lean_usize_dec_eq(v_i_2650_, v_stop_2651_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2681_; 
v___x_2659_ = lean_array_uget(v_as_2649_, v_i_2650_);
v_fst_2660_ = lean_ctor_get(v___x_2659_, 0);
v_snd_2661_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2663_ = v___x_2659_;
v_isShared_2664_ = v_isSharedCheck_2681_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_snd_2661_);
lean_inc(v_fst_2660_);
lean_dec(v___x_2659_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2681_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___y_2666_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2674_ = lean_unsigned_to_nat(0u);
v___x_2675_ = lean_array_get_size(v_snd_2661_);
v___x_2676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2677_ = lean_nat_dec_lt(v___x_2674_, v___x_2675_);
if (v___x_2677_ == 0)
{
lean_dec(v_snd_2661_);
v___y_2666_ = v___x_2676_;
goto v___jp_2665_;
}
else
{
size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = lean_usize_of_nat(v___x_2675_);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2648_, v_snd_2661_, v___x_2678_, v___x_2679_, v___x_2676_);
lean_dec(v_snd_2661_);
v___y_2666_ = v___x_2680_;
goto v___jp_2665_;
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = lean_array_get_size(v___y_2666_);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_nat_dec_eq(v___x_2667_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2671_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___y_2666_);
v___x_2671_ = v___x_2663_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_fst_2660_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___y_2666_);
v___x_2671_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_array_push(v_b_2652_, v___x_2671_);
v___y_2654_ = v___x_2672_;
goto v___jp_2653_;
}
}
else
{
lean_dec_ref(v___y_2666_);
lean_del_object(v___x_2663_);
lean_dec(v_fst_2660_);
v___y_2654_ = v_b_2652_;
goto v___jp_2653_;
}
}
}
}
else
{
return v_b_2652_;
}
v___jp_2653_:
{
size_t v___x_2655_; size_t v___x_2656_; 
v___x_2655_ = ((size_t)1ULL);
v___x_2656_ = lean_usize_add(v_i_2650_, v___x_2655_);
v_i_2650_ = v___x_2656_;
v_b_2652_ = v___y_2654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2682_, lean_object* v_as_2683_, lean_object* v_i_2684_, lean_object* v_stop_2685_, lean_object* v_b_2686_){
_start:
{
size_t v_i_boxed_2687_; size_t v_stop_boxed_2688_; lean_object* v_res_2689_; 
v_i_boxed_2687_ = lean_unbox_usize(v_i_2684_);
lean_dec(v_i_2684_);
v_stop_boxed_2688_ = lean_unbox_usize(v_stop_2685_);
lean_dec(v_stop_2685_);
v_res_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2682_, v_as_2683_, v_i_boxed_2687_, v_stop_boxed_2688_, v_b_2686_);
lean_dec_ref(v_as_2683_);
lean_dec_ref(v_linterOpts_2682_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2690_, lean_object* v_as_2691_, lean_object* v_start_2692_, lean_object* v_stop_2693_){
_start:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2695_ = lean_nat_dec_lt(v_start_2692_, v_stop_2693_);
if (v___x_2695_ == 0)
{
return v___x_2694_;
}
else
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = lean_array_get_size(v_as_2691_);
v___x_2697_ = lean_nat_dec_le(v_stop_2693_, v___x_2696_);
if (v___x_2697_ == 0)
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_nat_dec_lt(v_start_2692_, v___x_2696_);
if (v___x_2698_ == 0)
{
return v___x_2694_;
}
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_usize_of_nat(v_start_2692_);
v___x_2700_ = lean_usize_of_nat(v___x_2696_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2690_, v_as_2691_, v___x_2699_, v___x_2700_, v___x_2694_);
return v___x_2701_;
}
}
else
{
size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_usize_of_nat(v_start_2692_);
v___x_2703_ = lean_usize_of_nat(v_stop_2693_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2690_, v_as_2691_, v___x_2702_, v___x_2703_, v___x_2694_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2705_, lean_object* v_as_2706_, lean_object* v_start_2707_, lean_object* v_stop_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2705_, v_as_2706_, v_start_2707_, v_stop_2708_);
lean_dec(v_stop_2708_);
lean_dec(v_start_2707_);
lean_dec_ref(v_as_2706_);
lean_dec_ref(v_linterOpts_2705_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2710_, lean_object* v_init_2711_, lean_object* v_x_2712_){
_start:
{
if (lean_obj_tag(v_x_2712_) == 0)
{
lean_object* v_k_2714_; lean_object* v_v_2715_; lean_object* v_l_2716_; lean_object* v_r_2717_; uint8_t v_anyUnlocated_2718_; lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2734_; 
v_k_2714_ = lean_ctor_get(v_x_2712_, 1);
lean_inc(v_k_2714_);
v_v_2715_ = lean_ctor_get(v_x_2712_, 2);
lean_inc(v_v_2715_);
v_l_2716_ = lean_ctor_get(v_x_2712_, 3);
lean_inc(v_l_2716_);
v_r_2717_ = lean_ctor_get(v_x_2712_, 4);
lean_inc(v_r_2717_);
lean_dec_ref_known(v_x_2712_, 5);
v_anyUnlocated_2718_ = 1;
lean_inc(v_fst_2710_);
v___x_2719_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2710_, v_init_2711_, v_l_2716_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref(v___x_2719_);
v_a_2721_ = lean_ctor_get(v_a_2720_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_a_2720_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2723_ = v_a_2720_;
v_isShared_2724_ = v_isSharedCheck_2734_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v_a_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2734_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = l_Lean_Name_toString(v_k_2714_, v_anyUnlocated_2718_);
lean_inc(v_fst_2710_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 0);
lean_ctor_set(v___x_2723_, 0, v_fst_2710_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_fst_2710_);
v___x_2727_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
double v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2728_ = lean_float_of_nat(v_v_2715_);
v___x_2729_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2729_, 0, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2725_);
lean_ctor_set(v___x_2730_, 1, v___x_2727_);
lean_ctor_set(v___x_2730_, 2, v___x_2729_);
v___x_2731_ = lean_array_push(v_a_2721_, v___x_2730_);
v_init_2711_ = v___x_2731_;
v_x_2712_ = v_r_2717_;
goto _start;
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v_fst_2710_);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_init_2711_);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2737_, lean_object* v_init_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2737_, v_init_2738_, v_x_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2742_, lean_object* v_k_2743_, lean_object* v_fallback_2744_){
_start:
{
if (lean_obj_tag(v_t_2742_) == 0)
{
lean_object* v_k_2745_; lean_object* v_v_2746_; lean_object* v_l_2747_; lean_object* v_r_2748_; uint8_t v___x_2749_; 
v_k_2745_ = lean_ctor_get(v_t_2742_, 1);
v_v_2746_ = lean_ctor_get(v_t_2742_, 2);
v_l_2747_ = lean_ctor_get(v_t_2742_, 3);
v_r_2748_ = lean_ctor_get(v_t_2742_, 4);
v___x_2749_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2743_, v_k_2745_);
switch(v___x_2749_)
{
case 0:
{
v_t_2742_ = v_l_2747_;
goto _start;
}
case 1:
{
lean_inc(v_v_2746_);
return v_v_2746_;
}
default: 
{
v_t_2742_ = v_r_2748_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2744_);
return v_fallback_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2752_, lean_object* v_k_2753_, lean_object* v_fallback_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2752_, v_k_2753_, v_fallback_2754_);
lean_dec(v_fallback_2754_);
lean_dec(v_k_2753_);
lean_dec(v_t_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2756_, size_t v_i_2757_, size_t v_stop_2758_, lean_object* v_b_2759_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_eq(v_i_2757_, v_stop_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v_linter_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; 
v___x_2761_ = lean_array_uget_borrowed(v_as_2756_, v_i_2757_);
v_linter_2762_ = lean_ctor_get(v___x_2761_, 0);
v___x_2763_ = lean_unsigned_to_nat(0u);
v___x_2764_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2759_, v_linter_2762_, v___x_2763_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_add(v___x_2764_, v___x_2765_);
lean_dec(v___x_2764_);
lean_inc(v_linter_2762_);
v___x_2767_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2762_, v___x_2766_, v_b_2759_);
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2757_, v___x_2768_);
v_i_2757_ = v___x_2769_;
v_b_2759_ = v___x_2767_;
goto _start;
}
else
{
return v_b_2759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2771_, lean_object* v_i_2772_, lean_object* v_stop_2773_, lean_object* v_b_2774_){
_start:
{
size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; lean_object* v_res_2777_; 
v_i_boxed_2775_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2773_);
lean_dec(v_stop_2773_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2771_, v_i_boxed_2775_, v_stop_boxed_2776_, v_b_2774_);
lean_dec_ref(v_as_2771_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2778_, size_t v_sz_2779_, size_t v_i_2780_, lean_object* v_b_2781_){
_start:
{
lean_object* v_a_2784_; uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_b_2781_);
return v___x_2789_;
}
else
{
lean_object* v_a_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; lean_object* v___y_2794_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_a_2790_ = lean_array_uget_borrowed(v_as_2778_, v_i_2780_);
v_fst_2791_ = lean_ctor_get(v_a_2790_, 0);
v_snd_2792_ = lean_ctor_get(v_a_2790_, 1);
v___x_2806_ = lean_box(1);
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_array_get_size(v_snd_2792_);
v___x_2809_ = lean_nat_dec_lt(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
v___y_2794_ = v___x_2806_;
goto v___jp_2793_;
}
else
{
size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = ((size_t)0ULL);
v___x_2811_ = lean_usize_of_nat(v___x_2808_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2792_, v___x_2810_, v___x_2811_, v___x_2806_);
v___y_2794_ = v___x_2812_;
goto v___jp_2793_;
}
v___jp_2793_:
{
lean_object* v___x_2795_; 
lean_inc(v_fst_2791_);
v___x_2795_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2791_, v_b_2781_, v___y_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v_a_2797_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v_a_2797_ = lean_ctor_get(v_a_2796_, 0);
lean_inc(v_a_2797_);
lean_dec(v_a_2796_);
v_a_2784_ = v_a_2797_;
goto v___jp_2783_;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
v_a_2798_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2795_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2795_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
v___jp_2783_:
{
size_t v___x_2785_; size_t v___x_2786_; 
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_add(v_i_2780_, v___x_2785_);
v_i_2780_ = v___x_2786_;
v_b_2781_ = v_a_2784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2813_, lean_object* v_sz_2814_, lean_object* v_i_2815_, lean_object* v_b_2816_, lean_object* v___y_2817_){
_start:
{
size_t v_sz_boxed_2818_; size_t v_i_boxed_2819_; lean_object* v_res_2820_; 
v_sz_boxed_2818_ = lean_unbox_usize(v_sz_2814_);
lean_dec(v_sz_2814_);
v_i_boxed_2819_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_res_2820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2813_, v_sz_boxed_2818_, v_i_boxed_2819_, v_b_2816_);
lean_dec_ref(v_as_2813_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2824_, lean_object* v_as_2825_, size_t v_sz_2826_, size_t v_i_2827_, lean_object* v_b_2828_){
_start:
{
lean_object* v_a_2831_; uint8_t v_anyUnlocated_2835_; 
v_anyUnlocated_2835_ = lean_usize_dec_lt(v_i_2827_, v_sz_2826_);
if (v_anyUnlocated_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v_fst_2824_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_b_2828_);
return v___x_2836_;
}
else
{
lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2875_; 
v_fst_2837_ = lean_ctor_get(v_b_2828_, 0);
v_snd_2838_ = lean_ctor_get(v_b_2828_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_b_2828_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2840_ = v_b_2828_;
v_isShared_2841_ = v_isSharedCheck_2875_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_snd_2838_);
lean_inc(v_fst_2837_);
lean_dec(v_b_2828_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2875_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_a_2842_; lean_object* v_position_x3f_2843_; 
v_a_2842_ = lean_array_uget_borrowed(v_as_2825_, v_i_2827_);
v_position_x3f_2843_ = lean_ctor_get(v_a_2842_, 2);
if (lean_obj_tag(v_position_x3f_2843_) == 0)
{
lean_object* v_linter_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec(v_snd_2838_);
v_linter_2844_ = lean_ctor_get(v_a_2842_, 0);
v___x_2845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2844_);
v___x_2846_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2844_, v_anyUnlocated_2835_);
v___x_2847_ = lean_string_append(v___x_2845_, v___x_2846_);
lean_dec_ref(v___x_2846_);
v___x_2848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2849_ = lean_string_append(v___x_2847_, v___x_2848_);
lean_inc(v_fst_2824_);
v___x_2850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2824_, v_anyUnlocated_2835_);
v___x_2851_ = lean_string_append(v___x_2849_, v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
v___x_2854_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
lean_dec_ref_known(v___x_2854_, 1);
v___x_2855_ = lean_box(v_anyUnlocated_2835_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v___x_2855_);
v___x_2857_ = v___x_2840_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_fst_2837_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
v_a_2831_ = v___x_2857_;
goto v___jp_2830_;
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_del_object(v___x_2840_);
lean_dec(v_fst_2837_);
lean_dec(v_fst_2824_);
v_a_2859_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2854_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2854_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_linter_2867_; lean_object* v_file_2868_; lean_object* v_val_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v_linter_2867_ = lean_ctor_get(v_a_2842_, 0);
v_file_2868_ = lean_ctor_get(v_a_2842_, 3);
v_val_2869_ = lean_ctor_get(v_position_x3f_2843_, 0);
lean_inc(v_linter_2867_);
lean_inc(v_val_2869_);
lean_inc_ref(v_file_2868_);
v___x_2870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2870_, 0, v_file_2868_);
lean_ctor_set(v___x_2870_, 1, v_val_2869_);
lean_ctor_set(v___x_2870_, 2, v_linter_2867_);
v___x_2871_ = lean_array_push(v_fst_2837_, v___x_2870_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2871_);
v___x_2873_ = v___x_2840_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_snd_2838_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
v_a_2831_ = v___x_2873_;
goto v___jp_2830_;
}
}
}
}
v___jp_2830_:
{
size_t v___x_2832_; size_t v___x_2833_; 
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2827_, v___x_2832_);
v_i_2827_ = v___x_2833_;
v_b_2828_ = v_a_2831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2876_, lean_object* v_as_2877_, lean_object* v_sz_2878_, lean_object* v_i_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2878_);
lean_dec(v_sz_2878_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2879_);
lean_dec(v_i_2879_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2876_, v_as_2877_, v_sz_boxed_2882_, v_i_boxed_2883_, v_b_2880_);
lean_dec_ref(v_as_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2885_, size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_b_2888_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_b_2888_);
return v___x_2891_;
}
else
{
lean_object* v_a_2892_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v_fst_2895_; lean_object* v_snd_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2919_; 
v_a_2892_ = lean_array_uget_borrowed(v_as_2885_, v_i_2887_);
v_fst_2893_ = lean_ctor_get(v_a_2892_, 0);
v_snd_2894_ = lean_ctor_get(v_a_2892_, 1);
v_fst_2895_ = lean_ctor_get(v_b_2888_, 0);
v_snd_2896_ = lean_ctor_get(v_b_2888_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_b_2888_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2898_ = v_b_2888_;
v_isShared_2899_ = v_isSharedCheck_2919_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snd_2896_);
lean_inc(v_fst_2895_);
lean_dec(v_b_2888_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2919_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_fst_2895_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_snd_2896_);
v___x_2901_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
size_t v_sz_2902_; size_t v___x_2903_; lean_object* v___x_2904_; 
v_sz_2902_ = lean_array_size(v_snd_2894_);
v___x_2903_ = ((size_t)0ULL);
lean_inc(v_fst_2893_);
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2893_, v_snd_2894_, v_sz_2902_, v___x_2903_, v___x_2901_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v_fst_2906_; lean_object* v_snd_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2917_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v_fst_2906_ = lean_ctor_get(v_a_2905_, 0);
v_snd_2907_ = lean_ctor_get(v_a_2905_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2905_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2909_ = v_a_2905_;
v_isShared_2910_ = v_isSharedCheck_2917_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_snd_2907_);
lean_inc(v_fst_2906_);
lean_dec(v_a_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2917_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_fst_2906_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_snd_2907_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
size_t v___x_2913_; size_t v___x_2914_; 
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_add(v_i_2887_, v___x_2913_);
v_i_2887_ = v___x_2914_;
v_b_2888_ = v___x_2912_;
goto _start;
}
}
}
else
{
return v___x_2904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2920_, lean_object* v_sz_2921_, lean_object* v_i_2922_, lean_object* v_b_2923_, lean_object* v___y_2924_){
_start:
{
size_t v_sz_boxed_2925_; size_t v_i_boxed_2926_; lean_object* v_res_2927_; 
v_sz_boxed_2925_ = lean_unbox_usize(v_sz_2921_);
lean_dec(v_sz_2921_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2920_, v_sz_boxed_2925_, v_i_boxed_2926_, v_b_2923_);
lean_dec_ref(v_as_2920_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2928_, size_t v_sz_2929_, size_t v_i_2930_, lean_object* v_b_2931_){
_start:
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_usize_dec_lt(v_i_2930_, v_sz_2929_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_b_2931_);
return v___x_2934_;
}
else
{
lean_object* v_a_2935_; lean_object* v_message_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_a_2935_ = lean_array_uget_borrowed(v_as_2928_, v_i_2930_);
v_message_2936_ = lean_ctor_get(v_a_2935_, 1);
v___x_2937_ = lean_box(0);
v___x_2938_ = 0;
lean_inc_ref(v_message_2936_);
v___x_2939_ = l_Lean_SerialMessage_toString(v_message_2936_, v___x_2938_);
v___x_2940_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
size_t v___x_2941_; size_t v___x_2942_; 
lean_dec_ref_known(v___x_2940_, 1);
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2930_, v___x_2941_);
v_i_2930_ = v___x_2942_;
v_b_2931_ = v___x_2937_;
goto _start;
}
else
{
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2944_, lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_b_2947_, lean_object* v___y_2948_){
_start:
{
size_t v_sz_boxed_2949_; size_t v_i_boxed_2950_; lean_object* v_res_2951_; 
v_sz_boxed_2949_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2950_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2944_, v_sz_boxed_2949_, v_i_boxed_2950_, v_b_2947_);
lean_dec_ref(v_as_2944_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2954_, size_t v_sz_2955_, size_t v_i_2956_, lean_object* v_b_2957_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_usize_dec_lt(v_i_2956_, v_sz_2955_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_b_2957_);
return v___x_2960_;
}
else
{
lean_object* v_a_2961_; lean_object* v_fst_2962_; lean_object* v_snd_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_a_2961_ = lean_array_uget_borrowed(v_as_2954_, v_i_2956_);
v_fst_2962_ = lean_ctor_get(v_a_2961_, 0);
v_snd_2963_ = lean_ctor_get(v_a_2961_, 1);
v___x_2964_ = lean_box(0);
v___x_2965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_2962_);
v___x_2966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2962_, v___x_2959_);
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
lean_dec_ref(v___x_2966_);
v___x_2968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_2969_ = lean_string_append(v___x_2967_, v___x_2968_);
v___x_2970_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
size_t v_sz_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2970_, 1);
v_sz_2971_ = lean_array_size(v_snd_2963_);
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_2963_, v_sz_2971_, v___x_2972_, v___x_2964_);
if (lean_obj_tag(v___x_2973_) == 0)
{
size_t v___x_2974_; size_t v___x_2975_; 
lean_dec_ref_known(v___x_2973_, 1);
v___x_2974_ = ((size_t)1ULL);
v___x_2975_ = lean_usize_add(v_i_2956_, v___x_2974_);
v_i_2956_ = v___x_2975_;
v_b_2957_ = v___x_2964_;
goto _start;
}
else
{
return v___x_2973_;
}
}
else
{
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_2977_, lean_object* v_sz_2978_, lean_object* v_i_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_){
_start:
{
size_t v_sz_boxed_2982_; size_t v_i_boxed_2983_; lean_object* v_res_2984_; 
v_sz_boxed_2982_ = lean_unbox_usize(v_sz_2978_);
lean_dec(v_sz_2978_);
v_i_boxed_2983_ = lean_unbox_usize(v_i_2979_);
lean_dec(v_i_2979_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_2977_, v_sz_boxed_2982_, v_i_boxed_2983_, v_b_2980_);
lean_dec_ref(v_as_2977_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_2989_, lean_object* v_linterOpts_2990_, lean_object* v_env_2991_, lean_object* v_mod_2992_){
_start:
{
uint8_t v_lintOnly_2994_; uint8_t v_mode_2995_; lean_object* v___y_2997_; uint8_t v___y_2998_; lean_object* v___y_3066_; lean_object* v___x_3072_; lean_object* v_textGroups_3073_; 
v_lintOnly_2994_ = lean_ctor_get_uint8(v_args_2989_, sizeof(void*)*4);
v_mode_2995_ = lean_ctor_get_uint8(v_args_2989_, sizeof(void*)*4 + 1);
v___x_3072_ = l_Lean_Name_getRoot(v_mod_2992_);
v_textGroups_3073_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_2991_, v___x_3072_);
lean_dec(v___x_3072_);
if (v_lintOnly_2994_ == 0)
{
v___y_3066_ = v_textGroups_3073_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_array_get_size(v_textGroups_3073_);
v___x_3076_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2990_, v_textGroups_3073_, v___x_3074_, v___x_3075_);
lean_dec_ref(v_textGroups_3073_);
v___y_3066_ = v___x_3076_;
goto v___jp_3065_;
}
v___jp_2996_:
{
switch(v_mode_2995_)
{
case 0:
{
lean_object* v___x_2999_; size_t v_sz_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = lean_box(0);
v_sz_3000_ = lean_array_size(v___y_2997_);
v___x_3001_ = ((size_t)0ULL);
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_2997_, v_sz_3000_, v___x_3001_, v___x_2999_);
lean_dec_ref(v___y_2997_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3010_; 
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v___x_3002_, 0);
lean_dec(v_unused_3011_);
v___x_3004_ = v___x_3002_;
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
else
{
lean_dec(v___x_3002_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3006_, 0, v___y_2998_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3006_);
v___x_3008_ = v___x_3004_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3002_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3002_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
case 1:
{
lean_object* v___x_3020_; size_t v_sz_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3020_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3021_ = lean_array_size(v___y_2997_);
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_2997_, v_sz_3021_, v___x_3022_, v___x_3020_);
lean_dec_ref(v___y_2997_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3035_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3035_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3035_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_fst_3028_; lean_object* v_snd_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; lean_object* v___x_3033_; 
v_fst_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_fst_3028_);
v_snd_3029_ = lean_ctor_get(v_a_3024_, 1);
lean_inc(v_snd_3029_);
lean_dec(v_a_3024_);
v___x_3030_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3030_, 0, v_fst_3028_);
v___x_3031_ = lean_unbox(v_snd_3029_);
lean_dec(v_snd_3029_);
lean_ctor_set_uint8(v___x_3030_, sizeof(void*)*1, v___x_3031_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3030_);
v___x_3033_ = v___x_3026_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3030_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_a_3036_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3023_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3023_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
default: 
{
lean_object* v_codeQualityEntries_3044_; size_t v_sz_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v_codeQualityEntries_3044_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3045_ = lean_array_size(v___y_2997_);
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_2997_, v_sz_3045_, v___x_3046_, v_codeQualityEntries_3044_);
lean_dec_ref(v___y_2997_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3056_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_a_3048_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3047_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3047_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
v___jp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3067_ = lean_array_get_size(v___y_3066_);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_nat_dec_eq(v___x_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
v___x_3070_ = 1;
v___y_2997_ = v___y_3066_;
v___y_2998_ = v___x_3070_;
goto v___jp_2996_;
}
else
{
uint8_t v___x_3071_; 
v___x_3071_ = 0;
v___y_2997_ = v___y_3066_;
v___y_2998_ = v___x_3071_;
goto v___jp_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3077_, lean_object* v_linterOpts_3078_, lean_object* v_env_3079_, lean_object* v_mod_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3077_, v_linterOpts_3078_, v_env_3079_, v_mod_3080_);
lean_dec(v_mod_3080_);
lean_dec_ref(v_env_3079_);
lean_dec_ref(v_linterOpts_3078_);
lean_dec_ref(v_args_3077_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3083_, lean_object* v_t_3084_, lean_object* v_k_3085_, lean_object* v_fallback_3086_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3084_, v_k_3085_, v_fallback_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3088_, lean_object* v_t_3089_, lean_object* v_k_3090_, lean_object* v_fallback_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3088_, v_t_3089_, v_k_3090_, v_fallback_3091_);
lean_dec(v_fallback_3091_);
lean_dec(v_k_3090_);
lean_dec(v_t_3089_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3093_, lean_object* v_____r_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3098_, 0, v___y_3093_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3100_, lean_object* v_____r_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
uint8_t v___y_16490__boxed_3105_; lean_object* v_res_3106_; 
v___y_16490__boxed_3105_ = lean_unbox(v___y_3100_);
v_res_3106_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16490__boxed_3105_, v_____r_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3106_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
lean_ctor_set(v___x_3111_, 2, v___x_3110_);
lean_ctor_set(v___x_3111_, 3, v___x_3110_);
lean_ctor_set(v___x_3111_, 4, v___x_3109_);
lean_ctor_set(v___x_3111_, 5, v___x_3109_);
lean_ctor_set(v___x_3111_, 6, v___x_3109_);
lean_ctor_set(v___x_3111_, 7, v___x_3109_);
lean_ctor_set(v___x_3111_, 8, v___x_3109_);
lean_ctor_set(v___x_3111_, 9, v___x_3109_);
lean_ctor_set(v___x_3111_, 10, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_unsigned_to_nat(32u);
v___x_3113_ = lean_mk_empty_array_with_capacity(v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
size_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3115_ = ((size_t)5ULL);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_unsigned_to_nat(32u);
v___x_3118_ = lean_mk_empty_array_with_capacity(v___x_3117_);
v___x_3119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3120_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v___x_3118_);
lean_ctor_set(v___x_3120_, 2, v___x_3116_);
lean_ctor_set(v___x_3120_, 3, v___x_3116_);
lean_ctor_set_usize(v___x_3120_, 4, v___x_3115_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3121_ = lean_box(1);
v___x_3122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v___x_3122_);
lean_ctor_set(v___x_3124_, 2, v___x_3121_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; lean_object* v_toCold_3130_; lean_object* v_env_3131_; lean_object* v_options_3132_; uint8_t v___x_3133_; lean_object* v_env_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3129_ = lean_st_ref_get(v___y_3127_);
v_toCold_3130_ = lean_ctor_get(v___y_3126_, 0);
v_env_3131_ = lean_ctor_get(v___x_3129_, 0);
lean_inc_ref(v_env_3131_);
lean_dec(v___x_3129_);
v_options_3132_ = lean_ctor_get(v_toCold_3130_, 2);
v___x_3133_ = 0;
v_env_3134_ = l_Lean_Environment_setRecordingDeps(v_env_3131_, v___x_3133_);
v___x_3135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3132_);
v___x_3137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3137_, 0, v_env_3134_);
lean_ctor_set(v___x_3137_, 1, v___x_3135_);
lean_ctor_set(v___x_3137_, 2, v___x_3136_);
lean_ctor_set(v___x_3137_, 3, v_options_3132_);
v___x_3138_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
lean_ctor_set(v___x_3138_, 1, v_msgData_3125_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_ref_3149_; lean_object* v___x_3150_; lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3159_; 
v_ref_3149_ = lean_ctor_get(v___y_3146_, 2);
v___x_3150_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3145_, v___y_3146_, v___y_3147_);
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
lean_inc(v_ref_3149_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_ref_3149_);
lean_ctor_set(v___x_3155_, 1, v_a_3151_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 1);
lean_ctor_set(v___x_3153_, 0, v___x_3155_);
v___x_3157_ = v___x_3153_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3165_, lean_object* v_msg_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_toCold_3170_; lean_object* v_currRecDepth_3171_; lean_object* v_ref_3172_; uint16_t v_optionFlags_3173_; uint8_t v_suppressElabErrors_3174_; uint8_t v_checkDeprecated_3175_; uint8_t v_isRecordingDeps_3176_; lean_object* v_ref_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_toCold_3170_ = lean_ctor_get(v___y_3167_, 0);
v_currRecDepth_3171_ = lean_ctor_get(v___y_3167_, 1);
v_ref_3172_ = lean_ctor_get(v___y_3167_, 2);
v_optionFlags_3173_ = lean_ctor_get_uint16(v___y_3167_, sizeof(void*)*3);
v_suppressElabErrors_3174_ = lean_ctor_get_uint8(v___y_3167_, sizeof(void*)*3 + 2);
v_checkDeprecated_3175_ = lean_ctor_get_uint8(v___y_3167_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3176_ = lean_ctor_get_uint8(v___y_3167_, sizeof(void*)*3 + 4);
v_ref_3177_ = l_Lean_replaceRef(v_ref_3165_, v_ref_3172_);
lean_inc(v_currRecDepth_3171_);
lean_inc_ref(v_toCold_3170_);
v___x_3178_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3178_, 0, v_toCold_3170_);
lean_ctor_set(v___x_3178_, 1, v_currRecDepth_3171_);
lean_ctor_set(v___x_3178_, 2, v_ref_3177_);
lean_ctor_set_uint16(v___x_3178_, sizeof(void*)*3, v_optionFlags_3173_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*3 + 2, v_suppressElabErrors_3174_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*3 + 3, v_checkDeprecated_3175_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*3 + 4, v_isRecordingDeps_3176_);
v___x_3179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3166_, v___x_3178_, v___y_3168_);
lean_dec_ref_known(v___x_3178_, 3);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3180_, lean_object* v_msg_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3180_, v_msg_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v_ref_3180_);
return v_res_3185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__14));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__16));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__18));
v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__20));
v___x_3218_ = l_Lean_stringToMessageData(v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3219_, lean_object* v_declHint_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_env_3225_; uint8_t v___x_3226_; 
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_st_ref_get(v___y_3221_);
v_env_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3224_);
v___x_3226_ = l_Lean_Name_isAnonymous(v_declHint_3220_);
if (v___x_3226_ == 0)
{
uint8_t v_isExporting_3227_; 
v_isExporting_3227_ = lean_ctor_get_uint8(v_env_3225_, sizeof(void*)*13);
if (v_isExporting_3227_ == 0)
{
lean_object* v___x_3228_; 
lean_dec_ref(v_env_3225_);
lean_dec(v_declHint_3220_);
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_msg_3219_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
lean_inc_ref(v_env_3225_);
v___x_3229_ = l_Lean_Environment_setExporting(v_env_3225_, v___x_3226_);
lean_inc(v_declHint_3220_);
lean_inc_ref(v___x_3229_);
v___x_3230_ = l_Lean_Environment_contains(v___x_3229_, v_declHint_3220_, v_isExporting_3227_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref(v___x_3229_);
lean_dec_ref(v_env_3225_);
lean_dec(v_declHint_3220_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_msg_3219_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_c_3237_; lean_object* v___x_3238_; 
v___x_3232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3234_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3229_);
v___x_3235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3229_);
lean_ctor_set(v___x_3235_, 1, v___x_3232_);
lean_ctor_set(v___x_3235_, 2, v___x_3233_);
lean_ctor_set(v___x_3235_, 3, v___x_3234_);
lean_inc(v_declHint_3220_);
v___x_3236_ = l_Lean_MessageData_ofConstName(v_declHint_3220_, v___x_3226_);
v_c_3237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3237_, 0, v___x_3235_);
lean_ctor_set(v_c_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3229_, v_declHint_3220_);
lean_dec_ref(v___x_3229_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_dec_ref(v_env_3225_);
lean_dec(v_declHint_3220_);
v___x_3239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v_c_3237_);
v___x_3241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l_Lean_MessageData_note(v___x_3242_);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_msg_3219_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
return v___x_3245_;
}
else
{
lean_object* v_val_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3299_; 
v_val_3246_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3248_ = v___x_3238_;
v_isShared_3249_ = v_isSharedCheck_3299_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_val_3246_);
lean_dec(v___x_3238_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3299_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v_modules_3251_; lean_object* v_moduleNames_3252_; lean_object* v_mod_3253_; uint8_t v___x_3268_; 
v___x_3250_ = l_Lean_Environment_header(v_env_3225_);
lean_dec_ref(v_env_3225_);
v_modules_3251_ = lean_ctor_get(v___x_3250_, 3);
lean_inc_ref(v_modules_3251_);
v_moduleNames_3252_ = lean_ctor_get(v___x_3250_, 4);
lean_inc_ref(v_moduleNames_3252_);
lean_dec_ref(v___x_3250_);
v_mod_3253_ = lean_array_get(v___x_3223_, v_moduleNames_3252_, v_val_3246_);
lean_dec_ref(v_moduleNames_3252_);
v___x_3268_ = l_Lean_isPrivateName(v_declHint_3220_);
lean_dec(v_declHint_3220_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_array_get_size(v_modules_3251_);
v___x_3270_ = lean_nat_dec_lt(v_val_3246_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_dec_ref(v_modules_3251_);
lean_dec(v_val_3246_);
goto v___jp_3254_;
}
else
{
lean_object* v___x_3271_; lean_object* v_toImport_3272_; uint8_t v_isExported_3273_; 
v___x_3271_ = lean_array_fget(v_modules_3251_, v_val_3246_);
lean_dec(v_val_3246_);
lean_dec_ref(v_modules_3251_);
v_toImport_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc_ref(v_toImport_3272_);
lean_dec(v___x_3271_);
v_isExported_3273_ = lean_ctor_get_uint8(v_toImport_3272_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3272_);
if (v_isExported_3273_ == 0)
{
goto v___jp_3254_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_del_object(v___x_3248_);
v___x_3274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v_c_3237_);
v___x_3276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = l_Lean_MessageData_ofName(v_mod_3253_);
lean_inc_ref(v___x_3278_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__15);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3278_);
v___x_3283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__17);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_MessageData_note(v___x_3284_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_msg_3219_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
}
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_modules_3251_);
lean_del_object(v___x_3248_);
lean_dec(v_val_3246_);
v___x_3288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_c_3237_);
v___x_3290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__19);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Lean_MessageData_ofName(v_mod_3253_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__21);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_MessageData_note(v___x_3295_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_msg_3219_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
v___jp_3254_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v_c_3237_);
v___x_3257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_Lean_MessageData_ofName(v_mod_3253_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Lean_MessageData_note(v___x_3262_);
v___x_3264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3264_, 0, v_msg_3219_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set_tag(v___x_3248_, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3264_);
v___x_3266_ = v___x_3248_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec_ref(v_env_3225_);
lean_dec(v_declHint_3220_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_msg_3219_);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3301_, lean_object* v_declHint_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3301_, v_declHint_3302_, v___y_3303_);
lean_dec(v___y_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3306_, lean_object* v_declHint_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3321_; 
v___x_3311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3306_, v_declHint_3307_, v___y_3309_);
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3321_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3316_ = l_Lean_unknownIdentifierMessageTag;
v___x_3317_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v_a_3312_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3322_, lean_object* v_declHint_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3322_, v_declHint_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3328_, lean_object* v_msg_3329_, lean_object* v_declHint_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3336_; 
v___x_3334_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3329_, v_declHint_3330_, v___y_3331_, v___y_3332_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3328_, v_a_3335_, v___y_3331_, v___y_3332_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3337_, lean_object* v_msg_3338_, lean_object* v_declHint_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3337_, v_msg_3338_, v_declHint_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v_ref_3337_);
return v_res_3343_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3346_ = l_Lean_stringToMessageData(v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3348_ = l_Lean_stringToMessageData(v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3349_, lean_object* v_constName_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3354_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3355_ = 0;
lean_inc(v_constName_3350_);
v___x_3356_ = l_Lean_MessageData_ofConstName(v_constName_3350_, v___x_3355_);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3354_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3349_, v___x_3359_, v_constName_3350_, v___y_3351_, v___y_3352_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3361_, lean_object* v_constName_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3361_, v_constName_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v_ref_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_ref_3371_; lean_object* v___x_3372_; 
v_ref_3371_ = lean_ctor_get(v___y_3368_, 2);
v___x_3372_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3371_, v_constName_3367_, v___y_3368_, v___y_3369_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; lean_object* v_env_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3382_ = lean_st_ref_get(v___y_3380_);
v_env_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_env_3383_);
lean_dec(v___x_3382_);
v___x_3384_ = 0;
lean_inc(v_constName_3378_);
v___x_3385_ = l_Lean_Environment_find_x3f(v_env_3383_, v_constName_3378_, v___x_3384_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3378_, v___y_3379_, v___y_3380_);
return v___x_3386_;
}
else
{
lean_object* v_val_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_constName_3378_);
v_val_3387_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3385_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_val_3387_);
lean_dec(v___x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 0);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_val_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_box(0);
lean_inc(v_declName_3400_);
v___x_3405_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3431_; 
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v___x_3405_, 0);
lean_dec(v_unused_3432_);
v___x_3407_ = v___x_3405_;
v_isShared_3408_ = v_isSharedCheck_3431_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v___x_3405_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3431_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v_env_3410_; lean_object* v___x_3411_; 
v___x_3409_ = lean_st_ref_get(v___y_3402_);
v_env_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc_ref(v_env_3410_);
lean_dec(v___x_3409_);
v___x_3411_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3410_, v_declName_3400_);
lean_dec(v_declName_3400_);
lean_dec_ref(v_env_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3412_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3412_);
v___x_3414_ = v___x_3407_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
else
{
lean_object* v_val_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3430_; 
v_val_3416_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3418_ = v___x_3411_;
v_isShared_3419_ = v_isSharedCheck_3430_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_val_3416_);
lean_dec(v___x_3411_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3430_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v_env_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3420_ = lean_st_ref_get(v___y_3402_);
v_env_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc_ref(v_env_3421_);
lean_dec(v___x_3420_);
v___x_3422_ = l_Lean_Environment_allImportedModuleNames(v_env_3421_);
lean_dec_ref(v_env_3421_);
v___x_3423_ = lean_array_get(v___x_3404_, v___x_3422_, v_val_3416_);
lean_dec(v_val_3416_);
lean_dec_ref(v___x_3422_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3423_);
v___x_3425_ = v___x_3418_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3425_);
v___x_3427_ = v___x_3407_;
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
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v_declName_3400_);
v_a_3433_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3405_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3405_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3447_, lean_object* v_sp_3448_, lean_object* v___x_3449_, lean_object* v_as_3450_, size_t v_sz_3451_, size_t v_i_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_a_3458_; uint8_t v___x_3462_; 
v___x_3462_ = lean_usize_dec_lt(v_i_3452_, v_sz_3451_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_b_3453_);
return v___x_3463_;
}
else
{
lean_object* v_a_3464_; lean_object* v_fst_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3593_; 
v_a_3464_ = lean_array_uget(v_as_3450_, v_i_3452_);
v_fst_3465_ = lean_ctor_get(v_a_3464_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_a_3464_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v_a_3464_, 1);
lean_dec(v_unused_3594_);
v___x_3467_ = v_a_3464_;
v_isShared_3468_ = v_isSharedCheck_3593_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_fst_3465_);
lean_dec(v_a_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3593_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_fst_3469_; lean_object* v_snd_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3592_; 
v_fst_3469_ = lean_ctor_get(v_b_3453_, 0);
v_snd_3470_ = lean_ctor_get(v_b_3453_, 1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_b_3453_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3472_ = v_b_3453_;
v_isShared_3473_ = v_isSharedCheck_3592_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_snd_3470_);
lean_inc(v_fst_3469_);
lean_dec(v_b_3453_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3592_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; 
lean_inc(v_fst_3465_);
v___x_3474_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3465_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
if (lean_obj_tag(v_a_3475_) == 0)
{
lean_object* v_optName_3476_; lean_object* v_ref_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_snd_3470_);
v_optName_3476_ = lean_ctor_get(v_fst_3447_, 1);
v_ref_3477_ = lean_ctor_get(v___y_3454_, 2);
v___x_3478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3465_, v___x_3462_);
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3480_ = lean_string_append(v___x_3479_, v___x_3478_);
lean_dec_ref(v___x_3478_);
v___x_3481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_3482_ = lean_string_append(v___x_3480_, v___x_3481_);
lean_inc(v_optName_3476_);
v___x_3483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3476_, v___x_3462_);
v___x_3484_ = lean_string_append(v___x_3482_, v___x_3483_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
v___x_3487_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec_ref_known(v___x_3487_, 1);
lean_del_object(v___x_3467_);
v___x_3488_ = lean_box(v___x_3462_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v___x_3488_);
v___x_3490_ = v___x_3472_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_fst_3469_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
v_a_3458_ = v___x_3490_;
goto v___jp_3457_;
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3505_; 
lean_del_object(v___x_3472_);
lean_dec(v_fst_3469_);
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v_a_3492_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3494_ = v___x_3487_;
v_isShared_3495_ = v_isSharedCheck_3505_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3487_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3505_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3496_ = lean_io_error_to_string(v_a_3492_);
v___x_3497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
v___x_3498_ = l_Lean_MessageData_ofFormat(v___x_3497_);
lean_inc(v_ref_3477_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3498_);
lean_ctor_set(v___x_3467_, 0, v_ref_3477_);
v___x_3500_ = v___x_3467_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_ref_3477_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3500_);
v___x_3502_ = v___x_3494_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
else
{
lean_object* v_val_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3583_; 
v_val_3506_ = lean_ctor_get(v_a_3475_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_a_3475_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3508_ = v_a_3475_;
v_isShared_3509_ = v_isSharedCheck_3583_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_val_3506_);
lean_dec(v_a_3475_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3583_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3465_, v___y_3454_, v___y_3455_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___y_3513_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
if (lean_obj_tag(v_a_3511_) == 0)
{
lean_inc(v___x_3449_);
v___y_3513_ = v___x_3449_;
goto v___jp_3512_;
}
else
{
lean_object* v_val_3574_; 
v_val_3574_ = lean_ctor_get(v_a_3511_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v_a_3511_, 1);
v___y_3513_ = v_val_3574_;
goto v___jp_3512_;
}
v___jp_3512_:
{
lean_object* v_ref_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_ref_3514_ = lean_ctor_get(v___y_3454_, 2);
v___x_3515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v___y_3513_);
lean_inc(v_sp_3448_);
v___x_3516_ = l_Lean_SearchPath_findWithExt(v_sp_3448_, v___x_3515_, v___y_3513_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
if (lean_obj_tag(v_a_3517_) == 0)
{
lean_object* v_optName_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec(v_val_3506_);
lean_dec(v_snd_3470_);
v_optName_3518_ = lean_ctor_get(v_fst_3447_, 1);
v___x_3519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
v___x_3520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3513_, v___x_3462_);
v___x_3521_ = lean_string_append(v___x_3519_, v___x_3520_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_3523_ = lean_string_append(v___x_3521_, v___x_3522_);
lean_inc(v_optName_3518_);
v___x_3524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3518_, v___x_3462_);
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
v___x_3528_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_dec_ref_known(v___x_3528_, 1);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3467_);
v___x_3529_ = lean_box(v___x_3462_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v___x_3529_);
v___x_3531_ = v___x_3472_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_fst_3469_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3458_ = v___x_3531_;
goto v___jp_3457_;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3548_; 
lean_del_object(v___x_3472_);
lean_dec(v_fst_3469_);
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v_a_3533_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3535_ = v___x_3528_;
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3528_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3548_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3537_ = lean_io_error_to_string(v_a_3533_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 3);
lean_ctor_set(v___x_3508_, 0, v___x_3537_);
v___x_3539_ = v___x_3508_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = l_Lean_MessageData_ofFormat(v___x_3539_);
lean_inc(v_ref_3514_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3540_);
lean_ctor_set(v___x_3467_, 0, v_ref_3514_);
v___x_3542_ = v___x_3467_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_ref_3514_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3544_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3542_);
v___x_3544_ = v___x_3535_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
}
else
{
lean_object* v_range_3549_; lean_object* v_val_3550_; lean_object* v_pos_3551_; lean_object* v_optName_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec(v___y_3513_);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3467_);
v_range_3549_ = lean_ctor_get(v_val_3506_, 0);
lean_inc_ref(v_range_3549_);
lean_dec(v_val_3506_);
v_val_3550_ = lean_ctor_get(v_a_3517_, 0);
lean_inc(v_val_3550_);
lean_dec_ref_known(v_a_3517_, 1);
v_pos_3551_ = lean_ctor_get(v_range_3549_, 0);
lean_inc_ref(v_pos_3551_);
lean_dec_ref(v_range_3549_);
v_optName_3552_ = lean_ctor_get(v_fst_3447_, 1);
lean_inc(v_optName_3552_);
v___x_3553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3553_, 0, v_val_3550_);
lean_ctor_set(v___x_3553_, 1, v_pos_3551_);
lean_ctor_set(v___x_3553_, 2, v_optName_3552_);
v___x_3554_ = lean_array_push(v_fst_3469_, v___x_3553_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3554_);
v___x_3556_ = v___x_3472_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_snd_3470_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
v_a_3458_ = v___x_3556_;
goto v___jp_3457_;
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v___y_3513_);
lean_dec(v_val_3506_);
lean_del_object(v___x_3472_);
lean_dec(v_snd_3470_);
lean_dec(v_fst_3469_);
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v_a_3558_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3560_ = v___x_3516_;
v_isShared_3561_ = v_isSharedCheck_3573_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3516_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3573_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3562_ = lean_io_error_to_string(v_a_3558_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 3);
lean_ctor_set(v___x_3508_, 0, v___x_3562_);
v___x_3564_ = v___x_3508_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3565_ = l_Lean_MessageData_ofFormat(v___x_3564_);
lean_inc(v_ref_3514_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3565_);
lean_ctor_set(v___x_3467_, 0, v_ref_3514_);
v___x_3567_ = v___x_3467_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_ref_3514_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3569_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3567_);
v___x_3569_ = v___x_3560_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_del_object(v___x_3508_);
lean_dec(v_val_3506_);
lean_del_object(v___x_3472_);
lean_dec(v_snd_3470_);
lean_dec(v_fst_3469_);
lean_del_object(v___x_3467_);
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v_a_3575_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3510_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3510_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3472_);
lean_dec(v_snd_3470_);
lean_dec(v_fst_3469_);
lean_del_object(v___x_3467_);
lean_dec(v_fst_3465_);
lean_dec(v___x_3449_);
lean_dec(v_sp_3448_);
lean_dec_ref(v_fst_3447_);
v_a_3584_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3474_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3474_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
}
v___jp_3457_:
{
size_t v___x_3459_; size_t v___x_3460_; 
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3452_, v___x_3459_);
v_i_3452_ = v___x_3460_;
v_b_3453_ = v_a_3458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3595_, lean_object* v_sp_3596_, lean_object* v___x_3597_, lean_object* v_as_3598_, lean_object* v_sz_3599_, lean_object* v_i_3600_, lean_object* v_b_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
size_t v_sz_boxed_3605_; size_t v_i_boxed_3606_; lean_object* v_res_3607_; 
v_sz_boxed_3605_ = lean_unbox_usize(v_sz_3599_);
lean_dec(v_sz_3599_);
v_i_boxed_3606_ = lean_unbox_usize(v_i_3600_);
lean_dec(v_i_3600_);
v_res_3607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3595_, v_sp_3596_, v___x_3597_, v_as_3598_, v_sz_boxed_3605_, v_i_boxed_3606_, v_b_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_as_3598_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3609_) == 0)
{
return v_x_3608_;
}
else
{
lean_object* v_key_3610_; lean_object* v_value_3611_; lean_object* v_tail_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_key_3610_ = lean_ctor_get(v_x_3609_, 0);
v_value_3611_ = lean_ctor_get(v_x_3609_, 1);
v_tail_3612_ = lean_ctor_get(v_x_3609_, 2);
lean_inc(v_value_3611_);
lean_inc(v_key_3610_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v_key_3610_);
lean_ctor_set(v___x_3613_, 1, v_value_3611_);
v___x_3614_ = lean_array_push(v_x_3608_, v___x_3613_);
v_x_3608_ = v___x_3614_;
v_x_3609_ = v_tail_3612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3616_, v_x_3617_);
lean_dec(v_x_3617_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3619_, size_t v_i_3620_, size_t v_stop_3621_, lean_object* v_b_3622_){
_start:
{
uint8_t v___x_3623_; 
v___x_3623_ = lean_usize_dec_eq(v_i_3620_, v_stop_3621_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; 
v___x_3624_ = lean_array_uget_borrowed(v_as_3619_, v_i_3620_);
v___x_3625_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3622_, v___x_3624_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3620_, v___x_3626_);
v_i_3620_ = v___x_3627_;
v_b_3622_ = v___x_3625_;
goto _start;
}
else
{
return v_b_3622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3629_, lean_object* v_i_3630_, lean_object* v_stop_3631_, lean_object* v_b_3632_){
_start:
{
size_t v_i_boxed_3633_; size_t v_stop_boxed_3634_; lean_object* v_res_3635_; 
v_i_boxed_3633_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_stop_boxed_3634_ = lean_unbox_usize(v_stop_3631_);
lean_dec(v_stop_3631_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3629_, v_i_boxed_3633_, v_stop_boxed_3634_, v_b_3632_);
lean_dec_ref(v_as_3629_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3636_, lean_object* v___x_3637_, lean_object* v_as_3638_, size_t v_sz_3639_, size_t v_i_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_usize_dec_lt(v_i_3640_, v_sz_3639_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
lean_dec(v___x_3637_);
lean_dec(v_sp_3636_);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_b_3641_);
return v___x_3646_;
}
else
{
lean_object* v_a_3647_; lean_object* v_fst_3648_; lean_object* v_snd_3649_; lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3685_; 
v_a_3647_ = lean_array_uget_borrowed(v_as_3638_, v_i_3640_);
v_fst_3648_ = lean_ctor_get(v_a_3647_, 0);
v_snd_3649_ = lean_ctor_get(v_a_3647_, 1);
v_fst_3650_ = lean_ctor_get(v_b_3641_, 0);
v_snd_3651_ = lean_ctor_get(v_b_3641_, 1);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_b_3641_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3653_ = v_b_3641_;
v_isShared_3654_ = v_isSharedCheck_3685_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_snd_3651_);
lean_inc(v_fst_3650_);
lean_dec(v_b_3641_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3685_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___y_3656_; lean_object* v_size_3676_; lean_object* v_buckets_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v_size_3676_ = lean_ctor_get(v_snd_3649_, 0);
v_buckets_3677_ = lean_ctor_get(v_snd_3649_, 1);
v___x_3678_ = lean_mk_empty_array_with_capacity(v_size_3676_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_array_get_size(v_buckets_3677_);
v___x_3681_ = lean_nat_dec_lt(v___x_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
v___y_3656_ = v___x_3678_;
goto v___jp_3655_;
}
else
{
size_t v___x_3682_; size_t v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = lean_usize_of_nat(v___x_3680_);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3677_, v___x_3682_, v___x_3683_, v___x_3678_);
v___y_3656_ = v___x_3684_;
goto v___jp_3655_;
}
v___jp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3654_ == 0)
{
v___x_3658_ = v___x_3653_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_fst_3650_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_snd_3651_);
v___x_3658_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
size_t v_sz_3659_; size_t v___x_3660_; lean_object* v___x_3661_; 
v_sz_3659_ = lean_array_size(v___y_3656_);
v___x_3660_ = ((size_t)0ULL);
lean_inc(v___x_3637_);
lean_inc(v_sp_3636_);
lean_inc(v_fst_3648_);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3648_, v_sp_3636_, v___x_3637_, v___y_3656_, v_sz_3659_, v___x_3660_, v___x_3658_, v___y_3642_, v___y_3643_);
lean_dec_ref(v___y_3656_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v_fst_3663_; lean_object* v_snd_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3674_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v_fst_3663_ = lean_ctor_get(v_a_3662_, 0);
v_snd_3664_ = lean_ctor_get(v_a_3662_, 1);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_a_3662_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3666_ = v_a_3662_;
v_isShared_3667_ = v_isSharedCheck_3674_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_snd_3664_);
lean_inc(v_fst_3663_);
lean_dec(v_a_3662_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3674_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_fst_3663_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_snd_3664_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
size_t v___x_3670_; size_t v___x_3671_; 
v___x_3670_ = ((size_t)1ULL);
v___x_3671_ = lean_usize_add(v_i_3640_, v___x_3670_);
v_i_3640_ = v___x_3671_;
v_b_3641_ = v___x_3669_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3637_);
lean_dec(v_sp_3636_);
return v___x_3661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3686_, lean_object* v___x_3687_, lean_object* v_as_3688_, lean_object* v_sz_3689_, lean_object* v_i_3690_, lean_object* v_b_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
size_t v_sz_boxed_3695_; size_t v_i_boxed_3696_; lean_object* v_res_3697_; 
v_sz_boxed_3695_ = lean_unbox_usize(v_sz_3689_);
lean_dec(v_sz_3689_);
v_i_boxed_3696_ = lean_unbox_usize(v_i_3690_);
lean_dec(v_i_3690_);
v_res_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3686_, v___x_3687_, v_as_3688_, v_sz_boxed_3695_, v_i_boxed_3696_, v_b_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_as_3688_);
return v_res_3697_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3698_, lean_object* v_as_3699_, size_t v_i_3700_, size_t v_stop_3701_){
_start:
{
uint8_t v___x_3702_; 
v___x_3702_ = lean_usize_dec_eq(v_i_3700_, v_stop_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; lean_object* v_snd_3704_; lean_object* v_size_3705_; uint8_t v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3703_ = lean_array_uget_borrowed(v_as_3699_, v_i_3700_);
v_snd_3704_ = lean_ctor_get(v___x_3703_, 1);
v_size_3705_ = lean_ctor_get(v_snd_3704_, 0);
v___x_3706_ = 1;
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_nat_dec_eq(v_size_3705_, v___x_3707_);
if (v___x_3708_ == 0)
{
return v___x_3706_;
}
else
{
if (v___y_3698_ == 0)
{
size_t v___x_3709_; size_t v___x_3710_; 
v___x_3709_ = ((size_t)1ULL);
v___x_3710_ = lean_usize_add(v_i_3700_, v___x_3709_);
v_i_3700_ = v___x_3710_;
goto _start;
}
else
{
return v___x_3706_;
}
}
}
else
{
uint8_t v___x_3712_; 
v___x_3712_ = 0;
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3713_, lean_object* v_as_3714_, lean_object* v_i_3715_, lean_object* v_stop_3716_){
_start:
{
uint8_t v___y_17529__boxed_3717_; size_t v_i_boxed_3718_; size_t v_stop_boxed_3719_; uint8_t v_res_3720_; lean_object* v_r_3721_; 
v___y_17529__boxed_3717_ = lean_unbox(v___y_3713_);
v_i_boxed_3718_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_stop_boxed_3719_ = lean_unbox_usize(v_stop_3716_);
lean_dec(v_stop_3716_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_17529__boxed_3717_, v_as_3714_, v_i_boxed_3718_, v_stop_boxed_3719_);
lean_dec_ref(v_as_3714_);
v_r_3721_ = lean_box(v_res_3720_);
return v_r_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3722_, lean_object* v_v_3723_, lean_object* v_t_3724_){
_start:
{
lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; 
if (lean_obj_tag(v_t_3724_) == 0)
{
lean_object* v_size_3739_; lean_object* v_k_3740_; lean_object* v_v_3741_; lean_object* v_l_3742_; lean_object* v_r_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_4003_; 
v_size_3739_ = lean_ctor_get(v_t_3724_, 0);
v_k_3740_ = lean_ctor_get(v_t_3724_, 1);
v_v_3741_ = lean_ctor_get(v_t_3724_, 2);
v_l_3742_ = lean_ctor_get(v_t_3724_, 3);
v_r_3743_ = lean_ctor_get(v_t_3724_, 4);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_t_3724_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3745_ = v_t_3724_;
v_isShared_3746_ = v_isSharedCheck_4003_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_r_3743_);
lean_inc(v_l_3742_);
lean_inc(v_v_3741_);
lean_inc(v_k_3740_);
lean_inc(v_size_3739_);
lean_dec(v_t_3724_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_4003_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; uint8_t v___y_3797_; lean_object* v_fst_3997_; lean_object* v_snd_3998_; lean_object* v_fst_3999_; lean_object* v_snd_4000_; uint8_t v___x_4001_; 
v_fst_3997_ = lean_ctor_get(v_k_3722_, 0);
v_snd_3998_ = lean_ctor_get(v_k_3722_, 1);
v_fst_3999_ = lean_ctor_get(v_k_3740_, 0);
v_snd_4000_ = lean_ctor_get(v_k_3740_, 1);
v___x_4001_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3997_, v_fst_3999_);
if (v___x_4001_ == 1)
{
uint8_t v___x_4002_; 
v___x_4002_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3998_, v_snd_4000_);
v___y_3797_ = v___x_4002_;
goto v___jp_3796_;
}
else
{
v___y_3797_ = v___x_4001_;
goto v___jp_3796_;
}
v___jp_3747_:
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = lean_nat_add(v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 3, v___y_3751_);
lean_ctor_set(v___x_3745_, 0, v___x_3755_);
v___x_3757_ = v___x_3745_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3759_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3759_, 3, v___y_3751_);
lean_ctor_set(v_reuseFailAlloc_3759_, 4, v_r_3743_);
v___x_3757_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3758_, 0, v___y_3750_);
lean_ctor_set(v___x_3758_, 1, v___y_3749_);
lean_ctor_set(v___x_3758_, 2, v___y_3748_);
lean_ctor_set(v___x_3758_, 3, v___y_3752_);
lean_ctor_set(v___x_3758_, 4, v___x_3757_);
return v___x_3758_;
}
}
v___jp_3760_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = lean_nat_add(v___y_3770_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec(v___y_3770_);
v___x_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set(v___x_3774_, 1, v___y_3766_);
lean_ctor_set(v___x_3774_, 2, v___y_3764_);
lean_ctor_set(v___x_3774_, 3, v___y_3771_);
lean_ctor_set(v___x_3774_, 4, v___y_3769_);
v___x_3775_ = lean_nat_add(v___y_3768_, v___y_3767_);
lean_dec(v___y_3767_);
if (lean_obj_tag(v___y_3765_) == 0)
{
lean_object* v_size_3776_; 
v_size_3776_ = lean_ctor_get(v___y_3765_, 0);
lean_inc(v_size_3776_);
v___y_3748_ = v___y_3762_;
v___y_3749_ = v___y_3761_;
v___y_3750_ = v___y_3763_;
v___y_3751_ = v___y_3765_;
v___y_3752_ = v___x_3774_;
v___y_3753_ = v___x_3775_;
v___y_3754_ = v_size_3776_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_unsigned_to_nat(0u);
v___y_3748_ = v___y_3762_;
v___y_3749_ = v___y_3761_;
v___y_3750_ = v___y_3763_;
v___y_3751_ = v___y_3765_;
v___y_3752_ = v___x_3774_;
v___y_3753_ = v___x_3775_;
v___y_3754_ = v___x_3777_;
goto v___jp_3747_;
}
}
v___jp_3778_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_nat_add(v___y_3783_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec(v___y_3783_);
v___x_3792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v_k_3740_);
lean_ctor_set(v___x_3792_, 2, v_v_3741_);
lean_ctor_set(v___x_3792_, 3, v_l_3742_);
lean_ctor_set(v___x_3792_, 4, v___y_3786_);
v___x_3793_ = lean_nat_add(v___y_3779_, v___y_3782_);
lean_dec(v___y_3782_);
if (lean_obj_tag(v___y_3780_) == 0)
{
lean_object* v_size_3794_; 
v_size_3794_ = lean_ctor_get(v___y_3780_, 0);
lean_inc(v_size_3794_);
v___y_3726_ = v___x_3792_;
v___y_3727_ = v___y_3780_;
v___y_3728_ = v___x_3793_;
v___y_3729_ = v___y_3781_;
v___y_3730_ = v___y_3784_;
v___y_3731_ = v___y_3785_;
v___y_3732_ = v___y_3788_;
v___y_3733_ = v___y_3787_;
v___y_3734_ = v___y_3789_;
v___y_3735_ = v_size_3794_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_unsigned_to_nat(0u);
v___y_3726_ = v___x_3792_;
v___y_3727_ = v___y_3780_;
v___y_3728_ = v___x_3793_;
v___y_3729_ = v___y_3781_;
v___y_3730_ = v___y_3784_;
v___y_3731_ = v___y_3785_;
v___y_3732_ = v___y_3788_;
v___y_3733_ = v___y_3787_;
v___y_3734_ = v___y_3789_;
v___y_3735_ = v___x_3795_;
goto v___jp_3725_;
}
}
v___jp_3796_:
{
switch(v___y_3797_)
{
case 0:
{
lean_object* v_impl_3798_; lean_object* v___x_3799_; 
lean_dec(v_size_3739_);
v_impl_3798_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3722_, v_v_3723_, v_l_3742_);
v___x_3799_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3743_) == 0)
{
lean_object* v_size_3800_; lean_object* v_size_3801_; lean_object* v_k_3802_; lean_object* v_v_3803_; lean_object* v_l_3804_; lean_object* v_r_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v_size_3800_ = lean_ctor_get(v_r_3743_, 0);
v_size_3801_ = lean_ctor_get(v_impl_3798_, 0);
v_k_3802_ = lean_ctor_get(v_impl_3798_, 1);
v_v_3803_ = lean_ctor_get(v_impl_3798_, 2);
v_l_3804_ = lean_ctor_get(v_impl_3798_, 3);
v_r_3805_ = lean_ctor_get(v_impl_3798_, 4);
v___x_3806_ = lean_unsigned_to_nat(3u);
v___x_3807_ = lean_nat_mul(v___x_3806_, v_size_3800_);
v___x_3808_ = lean_nat_dec_lt(v___x_3807_, v_size_3801_);
lean_dec(v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_del_object(v___x_3745_);
v___x_3809_ = lean_nat_add(v___x_3799_, v_size_3801_);
v___x_3810_ = lean_nat_add(v___x_3809_, v_size_3800_);
lean_dec(v___x_3809_);
v___x_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
lean_ctor_set(v___x_3811_, 1, v_k_3740_);
lean_ctor_set(v___x_3811_, 2, v_v_3741_);
lean_ctor_set(v___x_3811_, 3, v_impl_3798_);
lean_ctor_set(v___x_3811_, 4, v_r_3743_);
return v___x_3811_;
}
else
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3848_; 
lean_inc(v_r_3805_);
lean_inc(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
lean_inc(v_size_3801_);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_impl_3798_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; lean_object* v_unused_3853_; 
v_unused_3849_ = lean_ctor_get(v_impl_3798_, 4);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_impl_3798_, 3);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_impl_3798_, 2);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_impl_3798_, 1);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_impl_3798_, 0);
lean_dec(v_unused_3853_);
v___x_3813_ = v_impl_3798_;
v_isShared_3814_ = v_isSharedCheck_3848_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v_impl_3798_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3848_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v_size_3815_; lean_object* v_size_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_l_3819_; lean_object* v_r_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_size_3815_ = lean_ctor_get(v_l_3804_, 0);
v_size_3816_ = lean_ctor_get(v_r_3805_, 0);
v_k_3817_ = lean_ctor_get(v_r_3805_, 1);
v_v_3818_ = lean_ctor_get(v_r_3805_, 2);
v_l_3819_ = lean_ctor_get(v_r_3805_, 3);
v_r_3820_ = lean_ctor_get(v_r_3805_, 4);
v___x_3821_ = lean_unsigned_to_nat(2u);
v___x_3822_ = lean_nat_mul(v___x_3821_, v_size_3815_);
v___x_3823_ = lean_nat_dec_lt(v_size_3816_, v___x_3822_);
lean_dec(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_inc(v_r_3820_);
lean_inc(v_l_3819_);
lean_inc(v_v_3818_);
lean_inc(v_k_3817_);
lean_del_object(v___x_3813_);
lean_dec(v_r_3805_);
v___x_3824_ = lean_nat_add(v___x_3799_, v_size_3801_);
lean_dec(v_size_3801_);
v___x_3825_ = lean_nat_add(v___x_3824_, v_size_3800_);
lean_dec(v___x_3824_);
v___x_3826_ = lean_nat_add(v___x_3799_, v_size_3815_);
if (lean_obj_tag(v_l_3819_) == 0)
{
lean_object* v_size_3827_; 
v_size_3827_ = lean_ctor_get(v_l_3819_, 0);
lean_inc(v_size_3827_);
lean_inc(v_size_3800_);
v___y_3761_ = v_k_3817_;
v___y_3762_ = v_v_3818_;
v___y_3763_ = v___x_3825_;
v___y_3764_ = v_v_3803_;
v___y_3765_ = v_r_3820_;
v___y_3766_ = v_k_3802_;
v___y_3767_ = v_size_3800_;
v___y_3768_ = v___x_3799_;
v___y_3769_ = v_l_3819_;
v___y_3770_ = v___x_3826_;
v___y_3771_ = v_l_3804_;
v___y_3772_ = v_size_3827_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3800_);
v___y_3761_ = v_k_3817_;
v___y_3762_ = v_v_3818_;
v___y_3763_ = v___x_3825_;
v___y_3764_ = v_v_3803_;
v___y_3765_ = v_r_3820_;
v___y_3766_ = v_k_3802_;
v___y_3767_ = v_size_3800_;
v___y_3768_ = v___x_3799_;
v___y_3769_ = v_l_3819_;
v___y_3770_ = v___x_3826_;
v___y_3771_ = v_l_3804_;
v___y_3772_ = v___x_3828_;
goto v___jp_3760_;
}
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_del_object(v___x_3745_);
v___x_3829_ = lean_nat_add(v___x_3799_, v_size_3801_);
lean_dec(v_size_3801_);
v___x_3830_ = lean_nat_add(v___x_3829_, v_size_3800_);
lean_dec(v___x_3829_);
v___x_3831_ = lean_nat_add(v___x_3799_, v_size_3800_);
v___x_3832_ = lean_nat_add(v___x_3831_, v_size_3816_);
lean_dec(v___x_3831_);
lean_inc_ref(v_r_3743_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 4, v_r_3743_);
lean_ctor_set(v___x_3813_, 3, v_r_3805_);
lean_ctor_set(v___x_3813_, 2, v_v_3741_);
lean_ctor_set(v___x_3813_, 1, v_k_3740_);
lean_ctor_set(v___x_3813_, 0, v___x_3832_);
v___x_3834_ = v___x_3813_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v_r_3805_);
lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_r_3743_);
v___x_3834_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
v_isSharedCheck_3841_ = !lean_is_exclusive(v_r_3743_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; lean_object* v_unused_3843_; lean_object* v_unused_3844_; lean_object* v_unused_3845_; lean_object* v_unused_3846_; 
v_unused_3842_ = lean_ctor_get(v_r_3743_, 4);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_r_3743_, 3);
lean_dec(v_unused_3843_);
v_unused_3844_ = lean_ctor_get(v_r_3743_, 2);
lean_dec(v_unused_3844_);
v_unused_3845_ = lean_ctor_get(v_r_3743_, 1);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_r_3743_, 0);
lean_dec(v_unused_3846_);
v___x_3836_ = v_r_3743_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v_r_3743_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v___x_3834_);
lean_ctor_set(v___x_3836_, 3, v_l_3804_);
lean_ctor_set(v___x_3836_, 2, v_v_3803_);
lean_ctor_set(v___x_3836_, 1, v_k_3802_);
lean_ctor_set(v___x_3836_, 0, v___x_3830_);
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_3840_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_3840_, 4, v___x_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3854_; 
lean_del_object(v___x_3745_);
v_l_3854_ = lean_ctor_get(v_impl_3798_, 3);
if (lean_obj_tag(v_l_3854_) == 0)
{
lean_object* v_r_3855_; lean_object* v_k_3856_; lean_object* v_v_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3866_; 
lean_inc_ref(v_l_3854_);
v_r_3855_ = lean_ctor_get(v_impl_3798_, 4);
v_k_3856_ = lean_ctor_get(v_impl_3798_, 1);
v_v_3857_ = lean_ctor_get(v_impl_3798_, 2);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_impl_3798_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; 
v_unused_3867_ = lean_ctor_get(v_impl_3798_, 3);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_impl_3798_, 0);
lean_dec(v_unused_3868_);
v___x_3859_ = v_impl_3798_;
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_r_3855_);
lean_inc(v_v_3857_);
lean_inc(v_k_3856_);
lean_dec(v_impl_3798_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3855_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v_r_3855_);
lean_ctor_set(v___x_3859_, 2, v_v_3741_);
lean_ctor_set(v___x_3859_, 1, v_k_3740_);
lean_ctor_set(v___x_3859_, 0, v___x_3799_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_r_3855_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_r_3855_);
v___x_3863_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3861_);
lean_ctor_set(v___x_3864_, 1, v_k_3856_);
lean_ctor_set(v___x_3864_, 2, v_v_3857_);
lean_ctor_set(v___x_3864_, 3, v_l_3854_);
lean_ctor_set(v___x_3864_, 4, v___x_3863_);
return v___x_3864_;
}
}
}
else
{
lean_object* v_r_3869_; 
v_r_3869_ = lean_ctor_get(v_impl_3798_, 4);
lean_inc(v_r_3869_);
if (lean_obj_tag(v_r_3869_) == 0)
{
lean_object* v_k_3870_; lean_object* v_v_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3892_; 
lean_inc(v_l_3854_);
v_k_3870_ = lean_ctor_get(v_impl_3798_, 1);
v_v_3871_ = lean_ctor_get(v_impl_3798_, 2);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_impl_3798_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3893_ = lean_ctor_get(v_impl_3798_, 4);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_impl_3798_, 3);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3798_, 0);
lean_dec(v_unused_3895_);
v___x_3873_ = v_impl_3798_;
v_isShared_3874_ = v_isSharedCheck_3892_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_v_3871_);
lean_inc(v_k_3870_);
lean_dec(v_impl_3798_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3892_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v_k_3875_; lean_object* v_v_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3888_; 
v_k_3875_ = lean_ctor_get(v_r_3869_, 1);
v_v_3876_ = lean_ctor_get(v_r_3869_, 2);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_r_3869_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; 
v_unused_3889_ = lean_ctor_get(v_r_3869_, 4);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_r_3869_, 3);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_r_3869_, 0);
lean_dec(v_unused_3891_);
v___x_3878_ = v_r_3869_;
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_v_3876_);
lean_inc(v_k_3875_);
lean_dec(v_r_3869_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___x_3880_ = lean_unsigned_to_nat(3u);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 4, v_l_3854_);
lean_ctor_set(v___x_3878_, 3, v_l_3854_);
lean_ctor_set(v___x_3878_, 2, v_v_3871_);
lean_ctor_set(v___x_3878_, 1, v_k_3870_);
lean_ctor_set(v___x_3878_, 0, v___x_3799_);
v___x_3882_ = v___x_3878_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_k_3870_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_v_3871_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v_l_3854_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_l_3854_);
v___x_3882_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 4, v_l_3854_);
lean_ctor_set(v___x_3873_, 2, v_v_3741_);
lean_ctor_set(v___x_3873_, 1, v_k_3740_);
lean_ctor_set(v___x_3873_, 0, v___x_3799_);
v___x_3884_ = v___x_3873_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_l_3854_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v_l_3854_);
v___x_3884_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3880_);
lean_ctor_set(v___x_3885_, 1, v_k_3875_);
lean_ctor_set(v___x_3885_, 2, v_v_3876_);
lean_ctor_set(v___x_3885_, 3, v___x_3882_);
lean_ctor_set(v___x_3885_, 4, v___x_3884_);
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_unsigned_to_nat(2u);
v___x_3897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v_k_3740_);
lean_ctor_set(v___x_3897_, 2, v_v_3741_);
lean_ctor_set(v___x_3897_, 3, v_impl_3798_);
lean_ctor_set(v___x_3897_, 4, v_r_3869_);
return v___x_3897_;
}
}
}
}
case 1:
{
lean_object* v___x_3898_; 
lean_del_object(v___x_3745_);
lean_dec(v_v_3741_);
lean_dec(v_k_3740_);
v___x_3898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3898_, 0, v_size_3739_);
lean_ctor_set(v___x_3898_, 1, v_k_3722_);
lean_ctor_set(v___x_3898_, 2, v_v_3723_);
lean_ctor_set(v___x_3898_, 3, v_l_3742_);
lean_ctor_set(v___x_3898_, 4, v_r_3743_);
return v___x_3898_;
}
default: 
{
lean_object* v_impl_3899_; lean_object* v___x_3900_; 
lean_del_object(v___x_3745_);
lean_dec(v_size_3739_);
v_impl_3899_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3722_, v_v_3723_, v_r_3743_);
v___x_3900_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3742_) == 0)
{
lean_object* v_size_3901_; lean_object* v_size_3902_; lean_object* v_k_3903_; lean_object* v_v_3904_; lean_object* v_l_3905_; lean_object* v_r_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_size_3901_ = lean_ctor_get(v_l_3742_, 0);
v_size_3902_ = lean_ctor_get(v_impl_3899_, 0);
v_k_3903_ = lean_ctor_get(v_impl_3899_, 1);
v_v_3904_ = lean_ctor_get(v_impl_3899_, 2);
v_l_3905_ = lean_ctor_get(v_impl_3899_, 3);
v_r_3906_ = lean_ctor_get(v_impl_3899_, 4);
v___x_3907_ = lean_unsigned_to_nat(3u);
v___x_3908_ = lean_nat_mul(v___x_3907_, v_size_3901_);
v___x_3909_ = lean_nat_dec_lt(v___x_3908_, v_size_3902_);
lean_dec(v___x_3908_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_nat_add(v___x_3900_, v_size_3901_);
v___x_3911_ = lean_nat_add(v___x_3910_, v_size_3902_);
lean_dec(v___x_3910_);
v___x_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
lean_ctor_set(v___x_3912_, 1, v_k_3740_);
lean_ctor_set(v___x_3912_, 2, v_v_3741_);
lean_ctor_set(v___x_3912_, 3, v_l_3742_);
lean_ctor_set(v___x_3912_, 4, v_impl_3899_);
return v___x_3912_;
}
else
{
lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3947_; 
lean_inc(v_r_3906_);
lean_inc(v_l_3905_);
lean_inc(v_v_3904_);
lean_inc(v_k_3903_);
lean_inc(v_size_3902_);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_impl_3899_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; 
v_unused_3948_ = lean_ctor_get(v_impl_3899_, 4);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_impl_3899_, 3);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_impl_3899_, 2);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_impl_3899_, 1);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_impl_3899_, 0);
lean_dec(v_unused_3952_);
v___x_3914_ = v_impl_3899_;
v_isShared_3915_ = v_isSharedCheck_3947_;
goto v_resetjp_3913_;
}
else
{
lean_dec(v_impl_3899_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3947_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v_size_3916_; lean_object* v_k_3917_; lean_object* v_v_3918_; lean_object* v_l_3919_; lean_object* v_r_3920_; lean_object* v_size_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_size_3916_ = lean_ctor_get(v_l_3905_, 0);
v_k_3917_ = lean_ctor_get(v_l_3905_, 1);
v_v_3918_ = lean_ctor_get(v_l_3905_, 2);
v_l_3919_ = lean_ctor_get(v_l_3905_, 3);
v_r_3920_ = lean_ctor_get(v_l_3905_, 4);
v_size_3921_ = lean_ctor_get(v_r_3906_, 0);
v___x_3922_ = lean_unsigned_to_nat(2u);
v___x_3923_ = lean_nat_mul(v___x_3922_, v_size_3921_);
v___x_3924_ = lean_nat_dec_lt(v_size_3916_, v___x_3923_);
lean_dec(v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_inc(v_size_3921_);
lean_inc(v_r_3920_);
lean_inc(v_l_3919_);
lean_inc(v_v_3918_);
lean_inc(v_k_3917_);
lean_del_object(v___x_3914_);
lean_dec(v_l_3905_);
v___x_3925_ = lean_nat_add(v___x_3900_, v_size_3901_);
v___x_3926_ = lean_nat_add(v___x_3925_, v_size_3902_);
lean_dec(v_size_3902_);
if (lean_obj_tag(v_l_3919_) == 0)
{
lean_object* v_size_3927_; 
v_size_3927_ = lean_ctor_get(v_l_3919_, 0);
lean_inc(v_size_3927_);
v___y_3779_ = v___x_3900_;
v___y_3780_ = v_r_3920_;
v___y_3781_ = v_k_3903_;
v___y_3782_ = v_size_3921_;
v___y_3783_ = v___x_3925_;
v___y_3784_ = v_k_3917_;
v___y_3785_ = v___x_3926_;
v___y_3786_ = v_l_3919_;
v___y_3787_ = v_r_3906_;
v___y_3788_ = v_v_3918_;
v___y_3789_ = v_v_3904_;
v___y_3790_ = v_size_3927_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_unsigned_to_nat(0u);
v___y_3779_ = v___x_3900_;
v___y_3780_ = v_r_3920_;
v___y_3781_ = v_k_3903_;
v___y_3782_ = v_size_3921_;
v___y_3783_ = v___x_3925_;
v___y_3784_ = v_k_3917_;
v___y_3785_ = v___x_3926_;
v___y_3786_ = v_l_3919_;
v___y_3787_ = v_r_3906_;
v___y_3788_ = v_v_3918_;
v___y_3789_ = v_v_3904_;
v___y_3790_ = v___x_3928_;
goto v___jp_3778_;
}
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3929_ = lean_nat_add(v___x_3900_, v_size_3901_);
v___x_3930_ = lean_nat_add(v___x_3929_, v_size_3902_);
lean_dec(v_size_3902_);
v___x_3931_ = lean_nat_add(v___x_3929_, v_size_3916_);
lean_dec(v___x_3929_);
lean_inc_ref(v_l_3742_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 4, v_l_3905_);
lean_ctor_set(v___x_3914_, 3, v_l_3742_);
lean_ctor_set(v___x_3914_, 2, v_v_3741_);
lean_ctor_set(v___x_3914_, 1, v_k_3740_);
lean_ctor_set(v___x_3914_, 0, v___x_3931_);
v___x_3933_ = v___x_3914_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_l_3742_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_l_3905_);
v___x_3933_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
v_isSharedCheck_3940_ = !lean_is_exclusive(v_l_3742_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3941_ = lean_ctor_get(v_l_3742_, 4);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_l_3742_, 3);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_l_3742_, 2);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_l_3742_, 1);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_l_3742_, 0);
lean_dec(v_unused_3945_);
v___x_3935_ = v_l_3742_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_l_3742_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 4, v_r_3906_);
lean_ctor_set(v___x_3935_, 3, v___x_3933_);
lean_ctor_set(v___x_3935_, 2, v_v_3904_);
lean_ctor_set(v___x_3935_, 1, v_k_3903_);
lean_ctor_set(v___x_3935_, 0, v___x_3930_);
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_k_3903_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_v_3904_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_r_3906_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3953_; 
v_l_3953_ = lean_ctor_get(v_impl_3899_, 3);
lean_inc(v_l_3953_);
if (lean_obj_tag(v_l_3953_) == 0)
{
lean_object* v_r_3954_; lean_object* v_k_3955_; lean_object* v_v_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3977_; 
v_r_3954_ = lean_ctor_get(v_impl_3899_, 4);
v_k_3955_ = lean_ctor_get(v_impl_3899_, 1);
v_v_3956_ = lean_ctor_get(v_impl_3899_, 2);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_impl_3899_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; lean_object* v_unused_3979_; 
v_unused_3978_ = lean_ctor_get(v_impl_3899_, 3);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_impl_3899_, 0);
lean_dec(v_unused_3979_);
v___x_3958_ = v_impl_3899_;
v_isShared_3959_ = v_isSharedCheck_3977_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_r_3954_);
lean_inc(v_v_3956_);
lean_inc(v_k_3955_);
lean_dec(v_impl_3899_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3977_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_k_3960_; lean_object* v_v_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3973_; 
v_k_3960_ = lean_ctor_get(v_l_3953_, 1);
v_v_3961_ = lean_ctor_get(v_l_3953_, 2);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_l_3953_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; lean_object* v_unused_3975_; lean_object* v_unused_3976_; 
v_unused_3974_ = lean_ctor_get(v_l_3953_, 4);
lean_dec(v_unused_3974_);
v_unused_3975_ = lean_ctor_get(v_l_3953_, 3);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_l_3953_, 0);
lean_dec(v_unused_3976_);
v___x_3963_ = v_l_3953_;
v_isShared_3964_ = v_isSharedCheck_3973_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_v_3961_);
lean_inc(v_k_3960_);
lean_dec(v_l_3953_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3973_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3965_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3954_, 2);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 4, v_r_3954_);
lean_ctor_set(v___x_3963_, 3, v_r_3954_);
lean_ctor_set(v___x_3963_, 2, v_v_3741_);
lean_ctor_set(v___x_3963_, 1, v_k_3740_);
lean_ctor_set(v___x_3963_, 0, v___x_3900_);
v___x_3967_ = v___x_3963_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3972_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3972_, 3, v_r_3954_);
lean_ctor_set(v_reuseFailAlloc_3972_, 4, v_r_3954_);
v___x_3967_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3969_; 
lean_inc(v_r_3954_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 3, v_r_3954_);
lean_ctor_set(v___x_3958_, 0, v___x_3900_);
v___x_3969_ = v___x_3958_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_k_3955_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_v_3956_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_r_3954_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_r_3954_);
v___x_3969_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3965_);
lean_ctor_set(v___x_3970_, 1, v_k_3960_);
lean_ctor_set(v___x_3970_, 2, v_v_3961_);
lean_ctor_set(v___x_3970_, 3, v___x_3967_);
lean_ctor_set(v___x_3970_, 4, v___x_3969_);
return v___x_3970_;
}
}
}
}
}
else
{
lean_object* v_r_3980_; 
v_r_3980_ = lean_ctor_get(v_impl_3899_, 4);
lean_inc(v_r_3980_);
if (lean_obj_tag(v_r_3980_) == 0)
{
lean_object* v_k_3981_; lean_object* v_v_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3991_; 
v_k_3981_ = lean_ctor_get(v_impl_3899_, 1);
v_v_3982_ = lean_ctor_get(v_impl_3899_, 2);
v_isSharedCheck_3991_ = !lean_is_exclusive(v_impl_3899_);
if (v_isSharedCheck_3991_ == 0)
{
lean_object* v_unused_3992_; lean_object* v_unused_3993_; lean_object* v_unused_3994_; 
v_unused_3992_ = lean_ctor_get(v_impl_3899_, 4);
lean_dec(v_unused_3992_);
v_unused_3993_ = lean_ctor_get(v_impl_3899_, 3);
lean_dec(v_unused_3993_);
v_unused_3994_ = lean_ctor_get(v_impl_3899_, 0);
lean_dec(v_unused_3994_);
v___x_3984_ = v_impl_3899_;
v_isShared_3985_ = v_isSharedCheck_3991_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_v_3982_);
lean_inc(v_k_3981_);
lean_dec(v_impl_3899_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3991_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3986_ = lean_unsigned_to_nat(3u);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 4, v_l_3953_);
lean_ctor_set(v___x_3984_, 2, v_v_3741_);
lean_ctor_set(v___x_3984_, 1, v_k_3740_);
lean_ctor_set(v___x_3984_, 0, v___x_3900_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3990_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3990_, 3, v_l_3953_);
lean_ctor_set(v_reuseFailAlloc_3990_, 4, v_l_3953_);
v___x_3988_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3986_);
lean_ctor_set(v___x_3989_, 1, v_k_3981_);
lean_ctor_set(v___x_3989_, 2, v_v_3982_);
lean_ctor_set(v___x_3989_, 3, v___x_3988_);
lean_ctor_set(v___x_3989_, 4, v_r_3980_);
return v___x_3989_;
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_unsigned_to_nat(2u);
v___x_3996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
lean_ctor_set(v___x_3996_, 1, v_k_3740_);
lean_ctor_set(v___x_3996_, 2, v_v_3741_);
lean_ctor_set(v___x_3996_, 3, v_r_3980_);
lean_ctor_set(v___x_3996_, 4, v_impl_3899_);
return v___x_3996_;
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
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_unsigned_to_nat(1u);
v___x_4005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v_k_3722_);
lean_ctor_set(v___x_4005_, 2, v_v_3723_);
lean_ctor_set(v___x_4005_, 3, v_t_3724_);
lean_ctor_set(v___x_4005_, 4, v_t_3724_);
return v___x_4005_;
}
v___jp_3725_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_nat_add(v___y_3728_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec(v___y_3728_);
v___x_3737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___y_3729_);
lean_ctor_set(v___x_3737_, 2, v___y_3734_);
lean_ctor_set(v___x_3737_, 3, v___y_3727_);
lean_ctor_set(v___x_3737_, 4, v___y_3733_);
v___x_3738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3738_, 0, v___y_3731_);
lean_ctor_set(v___x_3738_, 1, v___y_3730_);
lean_ctor_set(v___x_3738_, 2, v___y_3732_);
lean_ctor_set(v___x_3738_, 3, v___y_3726_);
lean_ctor_set(v___x_3738_, 4, v___x_3737_);
return v___x_3738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_4006_, lean_object* v_k_4007_, lean_object* v_fallback_4008_){
_start:
{
if (lean_obj_tag(v_t_4006_) == 0)
{
lean_object* v_k_4009_; lean_object* v_v_4010_; lean_object* v_l_4011_; lean_object* v_r_4012_; uint8_t v___y_4014_; lean_object* v_fst_4017_; lean_object* v_snd_4018_; lean_object* v_fst_4019_; lean_object* v_snd_4020_; uint8_t v___x_4021_; 
v_k_4009_ = lean_ctor_get(v_t_4006_, 1);
v_v_4010_ = lean_ctor_get(v_t_4006_, 2);
v_l_4011_ = lean_ctor_get(v_t_4006_, 3);
v_r_4012_ = lean_ctor_get(v_t_4006_, 4);
v_fst_4017_ = lean_ctor_get(v_k_4007_, 0);
v_snd_4018_ = lean_ctor_get(v_k_4007_, 1);
v_fst_4019_ = lean_ctor_get(v_k_4009_, 0);
v_snd_4020_ = lean_ctor_get(v_k_4009_, 1);
v___x_4021_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_4017_, v_fst_4019_);
if (v___x_4021_ == 1)
{
uint8_t v___x_4022_; 
v___x_4022_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_4018_, v_snd_4020_);
v___y_4014_ = v___x_4022_;
goto v___jp_4013_;
}
else
{
v___y_4014_ = v___x_4021_;
goto v___jp_4013_;
}
v___jp_4013_:
{
switch(v___y_4014_)
{
case 0:
{
v_t_4006_ = v_l_4011_;
goto _start;
}
case 1:
{
lean_inc(v_v_4010_);
return v_v_4010_;
}
default: 
{
v_t_4006_ = v_r_4012_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_4008_);
return v_fallback_4008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_4023_, lean_object* v_k_4024_, lean_object* v_fallback_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4023_, v_k_4024_, v_fallback_4025_);
lean_dec(v_fallback_4025_);
lean_dec_ref(v_k_4024_);
lean_dec(v_t_4023_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_4027_, lean_object* v_as_4028_, size_t v_sz_4029_, size_t v_i_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_4035_; 
v___x_4035_ = lean_usize_dec_lt(v_i_4030_, v_sz_4029_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
lean_dec(v___x_4027_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_b_4031_);
return v___x_4036_;
}
else
{
lean_object* v_a_4037_; lean_object* v_fst_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4066_; 
v_a_4037_ = lean_array_uget(v_as_4028_, v_i_4030_);
v_fst_4038_ = lean_ctor_get(v_a_4037_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_a_4037_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v_a_4037_, 1);
lean_dec(v_unused_4067_);
v___x_4040_ = v_a_4037_;
v_isShared_4041_ = v_isSharedCheck_4066_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_fst_4038_);
lean_dec(v_a_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4066_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4038_);
v___x_4043_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4038_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___y_4046_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
if (lean_obj_tag(v_a_4044_) == 0)
{
lean_inc(v___x_4027_);
v___y_4046_ = v___x_4027_;
goto v___jp_4045_;
}
else
{
lean_object* v_val_4057_; 
v_val_4057_ = lean_ctor_get(v_a_4044_, 0);
lean_inc(v_val_4057_);
lean_dec_ref_known(v_a_4044_, 1);
v___y_4046_ = v_val_4057_;
goto v___jp_4045_;
}
v___jp_4045_:
{
lean_object* v___x_4048_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 1, v_fst_4038_);
lean_ctor_set(v___x_4040_, 0, v___y_4046_);
v___x_4048_ = v___x_4040_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___y_4046_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_fst_4038_);
v___x_4048_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; size_t v___x_4053_; size_t v___x_4054_; 
v___x_4049_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4031_, v___x_4048_, v___x_4042_);
v___x_4050_ = lean_unsigned_to_nat(1u);
v___x_4051_ = lean_nat_add(v___x_4049_, v___x_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4048_, v___x_4051_, v_b_4031_);
v___x_4053_ = ((size_t)1ULL);
v___x_4054_ = lean_usize_add(v_i_4030_, v___x_4053_);
v_i_4030_ = v___x_4054_;
v_b_4031_ = v___x_4052_;
goto _start;
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_del_object(v___x_4040_);
lean_dec(v_fst_4038_);
lean_dec(v_b_4031_);
lean_dec(v___x_4027_);
v_a_4058_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4043_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4043_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4068_, lean_object* v_as_4069_, lean_object* v_sz_4070_, lean_object* v_i_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_sz_boxed_4076_; size_t v_i_boxed_4077_; lean_object* v_res_4078_; 
v_sz_boxed_4076_ = lean_unbox_usize(v_sz_4070_);
lean_dec(v_sz_4070_);
v_i_boxed_4077_ = lean_unbox_usize(v_i_4071_);
lean_dec(v_i_4071_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4068_, v_as_4069_, v_sz_boxed_4076_, v_i_boxed_4077_, v_b_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec_ref(v_as_4069_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4079_, lean_object* v_init_4080_, lean_object* v_x_4081_){
_start:
{
if (lean_obj_tag(v_x_4081_) == 0)
{
lean_object* v_k_4083_; lean_object* v_v_4084_; lean_object* v_l_4085_; lean_object* v_r_4086_; uint8_t v___x_4087_; lean_object* v___x_4088_; lean_object* v_a_4089_; lean_object* v_a_4090_; lean_object* v_fst_4091_; lean_object* v_snd_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4106_; 
v_k_4083_ = lean_ctor_get(v_x_4081_, 1);
lean_inc(v_k_4083_);
v_v_4084_ = lean_ctor_get(v_x_4081_, 2);
lean_inc(v_v_4084_);
v_l_4085_ = lean_ctor_get(v_x_4081_, 3);
lean_inc(v_l_4085_);
v_r_4086_ = lean_ctor_get(v_x_4081_, 4);
lean_inc(v_r_4086_);
lean_dec_ref_known(v_x_4081_, 5);
v___x_4087_ = 1;
lean_inc_ref(v_fst_4079_);
v___x_4088_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4079_, v_init_4080_, v_l_4085_);
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___x_4088_);
v_a_4090_ = lean_ctor_get(v_a_4089_, 0);
lean_inc(v_a_4090_);
lean_dec(v_a_4089_);
v_fst_4091_ = lean_ctor_get(v_k_4083_, 0);
v_snd_4092_ = lean_ctor_get(v_k_4083_, 1);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_k_4083_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4094_ = v_k_4083_;
v_isShared_4095_ = v_isSharedCheck_4106_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_snd_4092_);
lean_inc(v_fst_4091_);
lean_dec(v_k_4083_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4106_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v_optName_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
v_optName_4096_ = lean_ctor_get(v_fst_4079_, 1);
lean_inc(v_optName_4096_);
v___x_4097_ = l_Lean_Name_toString(v_optName_4096_, v___x_4087_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 1);
v___x_4099_ = v___x_4094_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_fst_4091_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_snd_4092_);
v___x_4099_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
double v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4100_ = lean_float_of_nat(v_v_4084_);
v___x_4101_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4101_, 0, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4097_);
lean_ctor_set(v___x_4102_, 1, v___x_4099_);
lean_ctor_set(v___x_4102_, 2, v___x_4101_);
v___x_4103_ = lean_array_push(v_a_4090_, v___x_4102_);
v_init_4080_ = v___x_4103_;
v_x_4081_ = v_r_4086_;
goto _start;
}
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v_fst_4079_);
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_init_4080_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4109_, lean_object* v_init_4110_, lean_object* v_x_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4109_, v_init_4110_, v_x_4111_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4114_, lean_object* v_as_4115_, size_t v_sz_4116_, size_t v_i_4117_, lean_object* v_b_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_a_4123_; uint8_t v___x_4127_; 
v___x_4127_ = lean_usize_dec_lt(v_i_4117_, v_sz_4116_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; 
lean_dec(v___x_4114_);
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_b_4118_);
return v___x_4128_;
}
else
{
lean_object* v_a_4129_; lean_object* v_snd_4130_; lean_object* v_fst_4131_; lean_object* v_size_4132_; lean_object* v_buckets_4133_; lean_object* v___x_4134_; lean_object* v___y_4136_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v_a_4129_ = lean_array_uget_borrowed(v_as_4115_, v_i_4117_);
v_snd_4130_ = lean_ctor_get(v_a_4129_, 1);
v_fst_4131_ = lean_ctor_get(v_a_4129_, 0);
v_size_4132_ = lean_ctor_get(v_snd_4130_, 0);
v_buckets_4133_ = lean_ctor_get(v_snd_4130_, 1);
v___x_4134_ = lean_box(1);
v___x_4160_ = lean_mk_empty_array_with_capacity(v_size_4132_);
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = lean_array_get_size(v_buckets_4133_);
v___x_4163_ = lean_nat_dec_lt(v___x_4161_, v___x_4162_);
if (v___x_4163_ == 0)
{
v___y_4136_ = v___x_4160_;
goto v___jp_4135_;
}
else
{
size_t v___x_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v___x_4164_ = ((size_t)0ULL);
v___x_4165_ = lean_usize_of_nat(v___x_4162_);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4133_, v___x_4164_, v___x_4165_, v___x_4160_);
v___y_4136_ = v___x_4166_;
goto v___jp_4135_;
}
v___jp_4135_:
{
size_t v_sz_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v_sz_4137_ = lean_array_size(v___y_4136_);
v___x_4138_ = ((size_t)0ULL);
lean_inc(v___x_4114_);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4114_, v___y_4136_, v_sz_4137_, v___x_4138_, v___x_4134_, v___y_4119_, v___y_4120_);
lean_dec_ref(v___y_4136_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
lean_inc(v_fst_4131_);
v___x_4141_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4131_, v_b_4118_, v_a_4140_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v_a_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v_a_4143_ = lean_ctor_get(v_a_4142_, 0);
lean_inc(v_a_4143_);
lean_dec(v_a_4142_);
v_a_4123_ = v_a_4143_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec(v___x_4114_);
v_a_4144_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4141_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4141_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v_b_4118_);
lean_dec(v___x_4114_);
v_a_4152_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4139_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4139_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
v___jp_4122_:
{
size_t v___x_4124_; size_t v___x_4125_; 
v___x_4124_ = ((size_t)1ULL);
v___x_4125_ = lean_usize_add(v_i_4117_, v___x_4124_);
v_i_4117_ = v___x_4125_;
v_b_4118_ = v_a_4123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4167_, lean_object* v_as_4168_, lean_object* v_sz_4169_, lean_object* v_i_4170_, lean_object* v_b_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
size_t v_sz_boxed_4175_; size_t v_i_boxed_4176_; lean_object* v_res_4177_; 
v_sz_boxed_4175_ = lean_unbox_usize(v_sz_4169_);
lean_dec(v_sz_4169_);
v_i_boxed_4176_ = lean_unbox_usize(v_i_4170_);
lean_dec(v_i_4170_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4167_, v_as_4168_, v_sz_boxed_4175_, v_i_boxed_4176_, v_b_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_as_4168_);
return v_res_4177_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = l_Lean_maxRecDepth;
v___x_4185_ = l_Lean_Options_empty;
v___x_4186_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_4185_, v___x_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4187_, lean_object* v_linterOpts_4188_, lean_object* v_sp_4189_, lean_object* v_env_4190_, lean_object* v_mod_4191_){
_start:
{
lean_object* v_a_4194_; lean_object* v_msg_4198_; lean_object* v_a_4203_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; uint16_t v___x_4228_; uint8_t v___x_4229_; uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v_a_4245_; lean_object* v___y_4249_; lean_object* v___y_4252_; uint8_t v___y_4253_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; uint8_t v___y_4259_; uint8_t v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; uint8_t v___y_4334_; uint8_t v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v_fileName_4374_; lean_object* v_fileMap_4375_; lean_object* v_currNamespace_4376_; lean_object* v_openDecls_4377_; lean_object* v_initHeartbeats_4378_; lean_object* v_maxHeartbeats_4379_; lean_object* v_quotContext_4380_; lean_object* v_currMacroScope_4381_; lean_object* v_cancelTk_x3f_4382_; lean_object* v_inheritedTraceOptions_4383_; lean_object* v_currRecDepth_4384_; lean_object* v_ref_4385_; uint8_t v_suppressElabErrors_4386_; uint8_t v_checkDeprecated_4387_; uint8_t v_isRecordingDeps_4388_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; uint8_t v___y_4410_; lean_object* v_env_4431_; uint8_t v___x_4432_; uint8_t v___x_4433_; 
v___x_4217_ = l_Lean_Name_getRoot(v_mod_4191_);
v___x_4218_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4219_ = l_Lean_instInhabitedFileMap_default;
v___x_4220_ = l_Lean_Options_empty;
v___x_4221_ = lean_box(0);
v___x_4222_ = lean_box(0);
v___x_4223_ = lean_unsigned_to_nat(0u);
v___x_4224_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4225_ = l_Lean_firstFrontendMacroScope;
v___x_4226_ = lean_box(0);
v___x_4227_ = lean_box(0);
v___x_4228_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4229_ = 0;
v___x_4230_ = 0;
v___x_4231_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4232_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4233_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4234_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4235_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4237_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4238_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4239_ = 1;
v___x_4240_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4241_, 0, v_env_4190_);
lean_ctor_set(v___x_4241_, 1, v___x_4231_);
lean_ctor_set(v___x_4241_, 2, v___x_4232_);
lean_ctor_set(v___x_4241_, 3, v___x_4233_);
lean_ctor_set(v___x_4241_, 4, v___x_4234_);
lean_ctor_set(v___x_4241_, 5, v___x_4235_);
lean_ctor_set(v___x_4241_, 6, v___x_4237_);
lean_ctor_set(v___x_4241_, 7, v___x_4238_);
lean_ctor_set(v___x_4241_, 8, v___x_4240_);
lean_ctor_set(v___x_4241_, 9, v___x_4236_);
v___x_4242_ = lean_io_get_num_heartbeats();
v___x_4243_ = lean_st_mk_ref(v___x_4241_);
v___x_4406_ = l_Lean_inheritedTraceOptions;
v___x_4407_ = lean_st_ref_get(v___x_4406_);
v___x_4408_ = lean_st_ref_get(v___x_4243_);
v_env_4431_ = lean_ctor_get(v___x_4408_, 0);
lean_inc_ref(v_env_4431_);
lean_dec(v___x_4408_);
v___x_4432_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4431_);
lean_dec_ref(v_env_4431_);
v___x_4433_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4433_ == 0)
{
if (v___x_4432_ == 0)
{
v___y_4410_ = v___x_4239_;
goto v___jp_4409_;
}
else
{
v_fileName_4374_ = v___x_4218_;
v_fileMap_4375_ = v___x_4219_;
v_currNamespace_4376_ = v___x_4221_;
v_openDecls_4377_ = v___x_4222_;
v_initHeartbeats_4378_ = v___x_4242_;
v_maxHeartbeats_4379_ = v___x_4224_;
v_quotContext_4380_ = v___x_4221_;
v_currMacroScope_4381_ = v___x_4225_;
v_cancelTk_x3f_4382_ = v___x_4226_;
v_inheritedTraceOptions_4383_ = v___x_4407_;
v_currRecDepth_4384_ = v___x_4223_;
v_ref_4385_ = v___x_4227_;
v_suppressElabErrors_4386_ = v___x_4229_;
v_checkDeprecated_4387_ = v___x_4230_;
v_isRecordingDeps_4388_ = v___x_4229_;
goto v___jp_4373_;
}
}
else
{
if (v___x_4432_ == 0)
{
v_fileName_4374_ = v___x_4218_;
v_fileMap_4375_ = v___x_4219_;
v_currNamespace_4376_ = v___x_4221_;
v_openDecls_4377_ = v___x_4222_;
v_initHeartbeats_4378_ = v___x_4242_;
v_maxHeartbeats_4379_ = v___x_4224_;
v_quotContext_4380_ = v___x_4221_;
v_currMacroScope_4381_ = v___x_4225_;
v_cancelTk_x3f_4382_ = v___x_4226_;
v_inheritedTraceOptions_4383_ = v___x_4407_;
v_currRecDepth_4384_ = v___x_4223_;
v_ref_4385_ = v___x_4227_;
v_suppressElabErrors_4386_ = v___x_4229_;
v_checkDeprecated_4387_ = v___x_4230_;
v_isRecordingDeps_4388_ = v___x_4229_;
goto v___jp_4373_;
}
else
{
v___y_4410_ = v___x_4229_;
goto v___jp_4409_;
}
}
v___jp_4193_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_mk_io_user_error(v_a_4194_);
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
return v___x_4196_;
}
v___jp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = l_Lean_MessageData_toString(v_msg_4198_);
v___x_4200_ = lean_mk_io_user_error(v___x_4199_);
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
return v___x_4201_;
}
v___jp_4202_:
{
if (lean_obj_tag(v_a_4203_) == 0)
{
lean_object* v_msg_4204_; 
v_msg_4204_ = lean_ctor_get(v_a_4203_, 1);
lean_inc_ref(v_msg_4204_);
lean_dec_ref_known(v_a_4203_, 2);
v_msg_4198_ = v_msg_4204_;
goto v___jp_4197_;
}
else
{
lean_object* v_id_4205_; lean_object* v___x_4206_; 
v_id_4205_ = lean_ctor_get(v_a_4203_, 0);
lean_inc(v_id_4205_);
lean_dec_ref_known(v_a_4203_, 2);
v___x_4206_ = l_Lean_InternalExceptionId_getName(v_id_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec(v_id_4205_);
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4208_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4209_ = 1;
v___x_4210_ = l_Lean_Name_toString(v_a_4207_, v___x_4209_);
v___x_4211_ = lean_string_append(v___x_4208_, v___x_4210_);
lean_dec_ref(v___x_4210_);
v_a_4194_ = v___x_4211_;
goto v___jp_4193_;
}
else
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_dec_ref_known(v___x_4206_, 1);
v___x_4212_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4213_ = l_Nat_reprFast(v_id_4205_);
v___x_4214_ = lean_string_append(v___x_4212_, v___x_4213_);
lean_dec_ref(v___x_4213_);
v___x_4215_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4216_ = lean_string_append(v___x_4214_, v___x_4215_);
v_a_4194_ = v___x_4216_;
goto v___jp_4193_;
}
}
}
v___jp_4244_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = lean_st_ref_get(v___x_4243_);
lean_dec(v___x_4243_);
lean_dec(v___x_4246_);
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v_a_4245_);
return v___x_4247_;
}
v___jp_4248_:
{
lean_object* v_a_4250_; 
v_a_4250_ = lean_ctor_get(v___y_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___y_4249_);
v_a_4245_ = v_a_4250_;
goto v___jp_4244_;
}
v___jp_4251_:
{
switch(v___y_4253_)
{
case 0:
{
lean_dec(v_sp_4189_);
if (v___y_4259_ == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_dec_ref(v___y_4257_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v___y_4252_);
v___x_4260_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4191_, v___x_4239_);
v___x_4262_ = lean_string_append(v___x_4260_, v___x_4261_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4264_ = lean_string_append(v___x_4262_, v___x_4263_);
v___x_4265_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4264_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4267_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
v___x_4267_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4259_, v_a_4266_, v___y_4258_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4258_);
v___y_4249_ = v___x_4267_;
goto v___jp_4248_;
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4256_);
lean_dec(v___x_4243_);
v_a_4268_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4270_ = v___x_4265_;
v_isShared_4271_ = v_isSharedCheck_4277_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4265_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4277_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4272_ = lean_io_error_to_string(v_a_4268_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set_tag(v___x_4270_, 3);
lean_ctor_set(v___x_4270_, 0, v___x_4272_);
v___x_4274_ = v___x_4270_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_MessageData_ofFormat(v___x_4274_);
v_msg_4198_ = v___x_4275_;
goto v___jp_4197_;
}
}
}
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4278_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4191_, v___y_4259_);
v___x_4280_ = lean_string_append(v___x_4278_, v___x_4279_);
lean_dec_ref(v___x_4279_);
v___x_4281_ = lean_array_get_size(v___y_4257_);
lean_dec_ref(v___y_4257_);
v___x_4282_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4252_, v___y_4254_, v___x_4239_, v___x_4280_, v___x_4281_, v___x_4239_, v___y_4258_, v___y_4256_);
lean_dec_ref(v___y_4254_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l_Lean_MessageData_toString(v_a_4283_);
v___x_4285_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4259_, v_a_4286_, v___y_4258_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4258_);
v___y_4249_ = v___x_4287_;
goto v___jp_4248_;
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4256_);
lean_dec(v___x_4243_);
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
v_msg_4198_ = v___x_4295_;
goto v___jp_4197_;
}
}
}
}
else
{
lean_object* v_a_4298_; 
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4256_);
lean_dec(v___x_4243_);
v_a_4298_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4282_, 1);
v_a_4203_ = v_a_4298_;
goto v___jp_4202_;
}
}
}
case 1:
{
lean_object* v___x_4299_; lean_object* v_env_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; size_t v_sz_4304_; size_t v___x_4305_; lean_object* v___x_4306_; 
lean_dec_ref(v___y_4257_);
lean_dec_ref(v___y_4254_);
lean_dec(v_mod_4191_);
v___x_4299_ = lean_st_ref_get(v___y_4256_);
v_env_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_ref(v_env_4300_);
lean_dec(v___x_4299_);
v___x_4301_ = l_Lean_Environment_mainModule(v_env_4300_);
lean_dec_ref(v_env_4300_);
v___x_4302_ = lean_box(v___y_4255_);
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4236_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v_sz_4304_ = lean_array_size(v___y_4252_);
v___x_4305_ = ((size_t)0ULL);
v___x_4306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4189_, v___x_4301_, v___y_4252_, v_sz_4304_, v___x_4305_, v___x_4303_, v___y_4258_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v___y_4252_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v_fst_4308_; lean_object* v_snd_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v_fst_4308_ = lean_ctor_get(v_a_4307_, 0);
lean_inc(v_fst_4308_);
v_snd_4309_ = lean_ctor_get(v_a_4307_, 1);
lean_inc(v_snd_4309_);
lean_dec(v_a_4307_);
v___x_4310_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4310_, 0, v_fst_4308_);
v___x_4311_ = lean_unbox(v_snd_4309_);
lean_dec(v_snd_4309_);
lean_ctor_set_uint8(v___x_4310_, sizeof(void*)*1, v___x_4311_);
v_a_4245_ = v___x_4310_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4312_; 
lean_dec(v___x_4243_);
v_a_4312_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4306_, 1);
v_a_4203_ = v_a_4312_;
goto v___jp_4202_;
}
}
default: 
{
lean_object* v___x_4313_; lean_object* v_env_4314_; lean_object* v___x_4315_; size_t v_sz_4316_; size_t v___x_4317_; lean_object* v___x_4318_; 
lean_dec_ref(v___y_4257_);
lean_dec_ref(v___y_4254_);
lean_dec(v_mod_4191_);
lean_dec(v_sp_4189_);
v___x_4313_ = lean_st_ref_get(v___y_4256_);
v_env_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc_ref(v_env_4314_);
lean_dec(v___x_4313_);
v___x_4315_ = l_Lean_Environment_mainModule(v_env_4314_);
lean_dec_ref(v_env_4314_);
v_sz_4316_ = lean_array_size(v___y_4252_);
v___x_4317_ = ((size_t)0ULL);
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4315_, v___y_4252_, v_sz_4316_, v___x_4317_, v___x_4236_, v___y_4258_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v___y_4252_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 2);
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
v_a_4245_ = v___x_4324_;
goto v___jp_4244_;
}
}
}
else
{
lean_object* v_a_4327_; 
lean_dec(v___x_4243_);
v_a_4327_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4318_, 1);
v_a_4203_ = v_a_4327_;
goto v___jp_4202_;
}
}
}
}
v___jp_4328_:
{
lean_object* v___x_4335_; 
lean_inc_ref(v___y_4332_);
v___x_4335_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4330_, v___y_4332_, v___y_4333_, v___y_4331_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = lean_array_get_size(v_a_4336_);
v___x_4338_ = lean_nat_dec_lt(v___x_4223_, v___x_4337_);
if (v___x_4338_ == 0)
{
v___y_4252_ = v_a_4336_;
v___y_4253_ = v___y_4329_;
v___y_4254_ = v___y_4330_;
v___y_4255_ = v___y_4334_;
v___y_4256_ = v___y_4331_;
v___y_4257_ = v___y_4332_;
v___y_4258_ = v___y_4333_;
v___y_4259_ = v___x_4338_;
goto v___jp_4251_;
}
else
{
if (v___x_4338_ == 0)
{
v___y_4252_ = v_a_4336_;
v___y_4253_ = v___y_4329_;
v___y_4254_ = v___y_4330_;
v___y_4255_ = v___y_4334_;
v___y_4256_ = v___y_4331_;
v___y_4257_ = v___y_4332_;
v___y_4258_ = v___y_4333_;
v___y_4259_ = v___x_4338_;
goto v___jp_4251_;
}
else
{
size_t v___x_4339_; size_t v___x_4340_; uint8_t v___x_4341_; 
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = lean_usize_of_nat(v___x_4337_);
v___x_4341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4334_, v_a_4336_, v___x_4339_, v___x_4340_);
v___y_4252_ = v_a_4336_;
v___y_4253_ = v___y_4329_;
v___y_4254_ = v___y_4330_;
v___y_4255_ = v___y_4334_;
v___y_4256_ = v___y_4331_;
v___y_4257_ = v___y_4332_;
v___y_4258_ = v___y_4333_;
v___y_4259_ = v___x_4341_;
goto v___jp_4251_;
}
}
}
else
{
lean_object* v_a_4342_; 
lean_dec_ref(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___x_4243_);
lean_dec(v_mod_4191_);
lean_dec(v_sp_4189_);
v_a_4342_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4335_, 1);
v_a_4203_ = v_a_4342_;
goto v___jp_4202_;
}
}
v___jp_4343_:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4348_, v___y_4347_, v___y_4346_);
lean_dec(v___y_4348_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = lean_array_get_size(v_a_4350_);
v___x_4352_ = lean_nat_dec_eq(v___x_4351_, v___x_4223_);
if (v___x_4352_ == 0)
{
v___y_4329_ = v___y_4344_;
v___y_4330_ = v___y_4345_;
v___y_4331_ = v___y_4346_;
v___y_4332_ = v_a_4350_;
v___y_4333_ = v___y_4347_;
v___y_4334_ = v___x_4352_;
goto v___jp_4328_;
}
else
{
uint8_t v___x_4353_; uint8_t v___x_4354_; 
v___x_4353_ = 0;
v___x_4354_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4344_, v___x_4353_);
if (v___x_4354_ == 0)
{
v___y_4329_ = v___y_4344_;
v___y_4330_ = v___y_4345_;
v___y_4331_ = v___y_4346_;
v___y_4332_ = v_a_4350_;
v___y_4333_ = v___y_4347_;
v___y_4334_ = v___x_4354_;
goto v___jp_4328_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_dec(v_a_4350_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v_sp_4189_);
v___x_4355_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4191_, v___x_4354_);
v___x_4357_ = lean_string_append(v___x_4355_, v___x_4356_);
lean_dec_ref(v___x_4356_);
v___x_4358_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4359_ = lean_string_append(v___x_4357_, v___x_4358_);
v___x_4360_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4359_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v___x_4361_; 
lean_dec_ref_known(v___x_4360_, 1);
v___x_4361_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4245_ = v___x_4361_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4371_; 
lean_dec(v___x_4243_);
v_a_4362_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4364_ = v___x_4360_;
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4360_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4366_ = lean_io_error_to_string(v_a_4362_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set_tag(v___x_4364_, 3);
lean_ctor_set(v___x_4364_, 0, v___x_4366_);
v___x_4368_ = v___x_4364_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_MessageData_ofFormat(v___x_4368_);
v_msg_4198_ = v___x_4369_;
goto v___jp_4197_;
}
}
}
}
}
}
else
{
lean_object* v_a_4372_; 
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___x_4243_);
lean_dec(v_mod_4191_);
lean_dec(v_sp_4189_);
v_a_4372_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4349_, 1);
v_a_4203_ = v_a_4372_;
goto v___jp_4202_;
}
}
v___jp_4373_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4389_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4381_);
lean_inc(v_quotContext_4380_);
lean_inc(v_maxHeartbeats_4379_);
lean_inc(v_openDecls_4377_);
lean_inc(v_currNamespace_4376_);
lean_inc_ref(v_fileMap_4375_);
lean_inc_ref(v_fileName_4374_);
v___x_4390_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4390_, 0, v_fileName_4374_);
lean_ctor_set(v___x_4390_, 1, v_fileMap_4375_);
lean_ctor_set(v___x_4390_, 2, v___x_4220_);
lean_ctor_set(v___x_4390_, 3, v___x_4389_);
lean_ctor_set(v___x_4390_, 4, v_currNamespace_4376_);
lean_ctor_set(v___x_4390_, 5, v_openDecls_4377_);
lean_ctor_set(v___x_4390_, 6, v_initHeartbeats_4378_);
lean_ctor_set(v___x_4390_, 7, v_maxHeartbeats_4379_);
lean_ctor_set(v___x_4390_, 8, v_quotContext_4380_);
lean_ctor_set(v___x_4390_, 9, v_currMacroScope_4381_);
lean_ctor_set(v___x_4390_, 10, v_cancelTk_x3f_4382_);
lean_ctor_set(v___x_4390_, 11, v_inheritedTraceOptions_4383_);
lean_inc(v_ref_4385_);
v___x_4391_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v_currRecDepth_4384_);
lean_ctor_set(v___x_4391_, 2, v_ref_4385_);
lean_ctor_set_uint16(v___x_4391_, sizeof(void*)*3, v___x_4228_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*3 + 2, v_suppressElabErrors_4386_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*3 + 3, v_checkDeprecated_4387_);
lean_ctor_set_uint8(v___x_4391_, sizeof(void*)*3 + 4, v_isRecordingDeps_4388_);
v___x_4392_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4217_, v___x_4243_);
lean_dec(v___x_4217_);
if (lean_obj_tag(v___x_4392_) == 0)
{
uint8_t v_lintOnly_4393_; 
v_lintOnly_4393_ = lean_ctor_get_uint8(v_args_4187_, sizeof(void*)*4);
if (v_lintOnly_4393_ == 0)
{
lean_object* v_a_4394_; uint8_t v_mode_4395_; 
lean_dec_ref(v_linterOpts_4188_);
v_a_4394_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4392_, 1);
v_mode_4395_ = lean_ctor_get_uint8(v_args_4187_, sizeof(void*)*4 + 1);
lean_inc(v___x_4243_);
v___y_4344_ = v_mode_4395_;
v___y_4345_ = v_a_4394_;
v___y_4346_ = v___x_4243_;
v___y_4347_ = v___x_4391_;
v___y_4348_ = v___x_4226_;
goto v___jp_4343_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4404_; 
v_a_4396_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4398_ = v___x_4392_;
v_isShared_4399_ = v_isSharedCheck_4404_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4392_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4404_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
uint8_t v_mode_4400_; lean_object* v___x_4402_; 
v_mode_4400_ = lean_ctor_get_uint8(v_args_4187_, sizeof(void*)*4 + 1);
if (v_isShared_4399_ == 0)
{
lean_ctor_set_tag(v___x_4398_, 1);
lean_ctor_set(v___x_4398_, 0, v_linterOpts_4188_);
v___x_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_linterOpts_4188_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_inc(v___x_4243_);
v___y_4344_ = v_mode_4400_;
v___y_4345_ = v_a_4396_;
v___y_4346_ = v___x_4243_;
v___y_4347_ = v___x_4391_;
v___y_4348_ = v___x_4402_;
goto v___jp_4343_;
}
}
}
}
else
{
lean_object* v_a_4405_; 
lean_dec_ref_known(v___x_4391_, 3);
lean_dec(v___x_4243_);
lean_dec(v_mod_4191_);
lean_dec(v_sp_4189_);
lean_dec_ref(v_linterOpts_4188_);
v_a_4405_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4392_, 1);
v_a_4203_ = v_a_4405_;
goto v___jp_4202_;
}
}
v___jp_4409_:
{
lean_object* v___x_4411_; lean_object* v_env_4412_; lean_object* v_nextMacroScope_4413_; lean_object* v_ngen_4414_; lean_object* v_auxDeclNGen_4415_; lean_object* v_traceState_4416_; lean_object* v_recordedDeps_4417_; lean_object* v_messages_4418_; lean_object* v_infoState_4419_; lean_object* v_snapshotTasks_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4429_; 
v___x_4411_ = lean_st_ref_take(v___x_4243_);
v_env_4412_ = lean_ctor_get(v___x_4411_, 0);
v_nextMacroScope_4413_ = lean_ctor_get(v___x_4411_, 1);
v_ngen_4414_ = lean_ctor_get(v___x_4411_, 2);
v_auxDeclNGen_4415_ = lean_ctor_get(v___x_4411_, 3);
v_traceState_4416_ = lean_ctor_get(v___x_4411_, 4);
v_recordedDeps_4417_ = lean_ctor_get(v___x_4411_, 6);
v_messages_4418_ = lean_ctor_get(v___x_4411_, 7);
v_infoState_4419_ = lean_ctor_get(v___x_4411_, 8);
v_snapshotTasks_4420_ = lean_ctor_get(v___x_4411_, 9);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; 
v_unused_4430_ = lean_ctor_get(v___x_4411_, 5);
lean_dec(v_unused_4430_);
v___x_4422_ = v___x_4411_;
v_isShared_4423_ = v_isSharedCheck_4429_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_snapshotTasks_4420_);
lean_inc(v_infoState_4419_);
lean_inc(v_messages_4418_);
lean_inc(v_recordedDeps_4417_);
lean_inc(v_traceState_4416_);
lean_inc(v_auxDeclNGen_4415_);
lean_inc(v_ngen_4414_);
lean_inc(v_nextMacroScope_4413_);
lean_inc(v_env_4412_);
lean_dec(v___x_4411_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4429_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = l_Lean_Kernel_enableDiag(v_env_4412_, v___y_4410_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 5, v___x_4235_);
lean_ctor_set(v___x_4422_, 0, v___x_4424_);
v___x_4426_ = v___x_4422_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_nextMacroScope_4413_);
lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_ngen_4414_);
lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_auxDeclNGen_4415_);
lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_traceState_4416_);
lean_ctor_set(v_reuseFailAlloc_4428_, 5, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4428_, 6, v_recordedDeps_4417_);
lean_ctor_set(v_reuseFailAlloc_4428_, 7, v_messages_4418_);
lean_ctor_set(v_reuseFailAlloc_4428_, 8, v_infoState_4419_);
lean_ctor_set(v_reuseFailAlloc_4428_, 9, v_snapshotTasks_4420_);
v___x_4426_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4427_; 
v___x_4427_ = lean_st_ref_put(v___x_4243_, v___x_4426_);
v_fileName_4374_ = v___x_4218_;
v_fileMap_4375_ = v___x_4219_;
v_currNamespace_4376_ = v___x_4221_;
v_openDecls_4377_ = v___x_4222_;
v_initHeartbeats_4378_ = v___x_4242_;
v_maxHeartbeats_4379_ = v___x_4224_;
v_quotContext_4380_ = v___x_4221_;
v_currMacroScope_4381_ = v___x_4225_;
v_cancelTk_x3f_4382_ = v___x_4226_;
v_inheritedTraceOptions_4383_ = v___x_4407_;
v_currRecDepth_4384_ = v___x_4223_;
v_ref_4385_ = v___x_4227_;
v_suppressElabErrors_4386_ = v___x_4229_;
v_checkDeprecated_4387_ = v___x_4230_;
v_isRecordingDeps_4388_ = v___x_4229_;
goto v___jp_4373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4434_, lean_object* v_linterOpts_4435_, lean_object* v_sp_4436_, lean_object* v_env_4437_, lean_object* v_mod_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4434_, v_linterOpts_4435_, v_sp_4436_, v_env_4437_, v_mod_4438_);
lean_dec_ref(v_args_4434_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4441_, lean_object* v_t_4442_, lean_object* v_k_4443_, lean_object* v_fallback_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4442_, v_k_4443_, v_fallback_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4446_, lean_object* v_t_4447_, lean_object* v_k_4448_, lean_object* v_fallback_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4446_, v_t_4447_, v_k_4448_, v_fallback_4449_);
lean_dec(v_fallback_4449_);
lean_dec_ref(v_k_4448_);
lean_dec(v_t_4447_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4451_, lean_object* v_k_4452_, lean_object* v_v_4453_, lean_object* v_t_4454_, lean_object* v_hl_4455_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4452_, v_v_4453_, v_t_4454_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4457_, lean_object* v_init_4458_, lean_object* v_x_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4457_, v_init_4458_, v_x_4459_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4464_, lean_object* v_init_4465_, lean_object* v_x_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4464_, v_init_4465_, v_x_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4471_, lean_object* v_constName_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4472_, v___y_4473_, v___y_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4477_, lean_object* v_constName_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4477_, v_constName_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4483_, lean_object* v_ref_4484_, lean_object* v_constName_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4484_, v_constName_4485_, v___y_4486_, v___y_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4490_, lean_object* v_ref_4491_, lean_object* v_constName_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4490_, v_ref_4491_, v_constName_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v_ref_4491_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4497_, lean_object* v_ref_4498_, lean_object* v_msg_4499_, lean_object* v_declHint_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4498_, v_msg_4499_, v_declHint_4500_, v___y_4501_, v___y_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4505_, lean_object* v_ref_4506_, lean_object* v_msg_4507_, lean_object* v_declHint_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4505_, v_ref_4506_, v_msg_4507_, v_declHint_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v_ref_4506_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4513_, lean_object* v_declHint_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4513_, v_declHint_4514_, v___y_4516_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4519_, lean_object* v_declHint_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4519_, v_declHint_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4525_, lean_object* v_ref_4526_, lean_object* v_msg_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4526_, v_msg_4527_, v___y_4528_, v___y_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4532_, lean_object* v_ref_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4532_, v_ref_4533_, v_msg_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v_ref_4533_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4539_, lean_object* v_msg_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4540_, v___y_4541_, v___y_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4545_, lean_object* v_msg_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4545_, v_msg_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4551_){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; uint32_t v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4553_ = l_Std_Format_defWidth;
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = l_Std_Format_pretty(v_s_4551_, v___x_4553_, v___x_4554_, v___x_4554_);
v___x_4556_ = 10;
v___x_4557_ = lean_string_push(v___x_4555_, v___x_4556_);
v___x_4558_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4559_, lean_object* v_a_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4559_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4562_, size_t v_sz_4563_, size_t v_i_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_){
_start:
{
uint8_t v___x_4568_; 
v___x_4568_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; 
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v_b_4565_);
return v___x_4569_;
}
else
{
lean_object* v___x_4570_; lean_object* v_a_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v_ref_4574_; lean_object* v___x_4575_; 
v___x_4570_ = lean_box(0);
v_a_4571_ = lean_array_uget_borrowed(v_as_4562_, v_i_4564_);
v___x_4572_ = lean_box(0);
lean_inc(v_a_4571_);
v___x_4573_ = l_Lean_MessageData_format(v_a_4571_, v___x_4572_);
v_ref_4574_ = lean_ctor_get(v___y_4566_, 2);
v___x_4575_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4573_);
if (lean_obj_tag(v___x_4575_) == 0)
{
size_t v___x_4576_; size_t v___x_4577_; 
lean_dec_ref_known(v___x_4575_, 1);
v___x_4576_ = ((size_t)1ULL);
v___x_4577_ = lean_usize_add(v_i_4564_, v___x_4576_);
v_i_4564_ = v___x_4577_;
v_b_4565_ = v___x_4570_;
goto _start;
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4590_; 
v_a_4579_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4581_ = v___x_4575_;
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4575_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v___x_4583_ = lean_io_error_to_string(v_a_4579_);
v___x_4584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
v___x_4585_ = l_Lean_MessageData_ofFormat(v___x_4584_);
lean_inc(v_ref_4574_);
v___x_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4586_, 0, v_ref_4574_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4586_);
v___x_4588_ = v___x_4581_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4591_, lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_b_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
size_t v_sz_boxed_4597_; size_t v_i_boxed_4598_; lean_object* v_res_4599_; 
v_sz_boxed_4597_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4598_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4591_, v_sz_boxed_4597_, v_i_boxed_4598_, v_b_4594_, v___y_4595_);
lean_dec_ref(v___y_4595_);
lean_dec_ref(v_as_4591_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4600_, lean_object* v_entries_4601_, lean_object* v_____r_4602_, uint8_t v_anyFailed_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v___x_4607_; size_t v_sz_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v___x_4607_ = lean_box(0);
v_sz_4608_ = lean_array_size(v_errors_4600_);
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4600_, v_sz_4608_, v___x_4609_, v___x_4607_, v___y_4604_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4619_; 
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4619_ == 0)
{
lean_object* v_unused_4620_; 
v_unused_4620_ = lean_ctor_get(v___x_4610_, 0);
lean_dec(v_unused_4620_);
v___x_4612_ = v___x_4610_;
v_isShared_4613_ = v_isSharedCheck_4619_;
goto v_resetjp_4611_;
}
else
{
lean_dec(v___x_4610_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4619_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4614_ = lean_box(v_anyFailed_4603_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_entries_4601_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4615_);
v___x_4617_ = v___x_4612_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_dec_ref(v_entries_4601_);
v_a_4621_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4610_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4610_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4629_, lean_object* v_entries_4630_, lean_object* v_____r_4631_, lean_object* v_anyFailed_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
uint8_t v_anyFailed_boxed_4636_; lean_object* v_res_4637_; 
v_anyFailed_boxed_4636_ = lean_unbox(v_anyFailed_4632_);
v_res_4637_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4629_, v_entries_4630_, v_____r_4631_, v_anyFailed_boxed_4636_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec_ref(v_errors_4629_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4638_, lean_object* v_env_4639_, lean_object* v_mod_4640_){
_start:
{
lean_object* v_a_4643_; lean_object* v_a_4647_; uint8_t v_anyFailed_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; uint16_t v___x_4675_; uint8_t v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___y_4693_; lean_object* v_fileName_4709_; lean_object* v_fileMap_4710_; lean_object* v_currNamespace_4711_; lean_object* v_openDecls_4712_; lean_object* v_initHeartbeats_4713_; lean_object* v_maxHeartbeats_4714_; lean_object* v_quotContext_4715_; lean_object* v_currMacroScope_4716_; lean_object* v_cancelTk_x3f_4717_; lean_object* v_inheritedTraceOptions_4718_; lean_object* v_currRecDepth_4719_; lean_object* v_ref_4720_; uint8_t v_suppressElabErrors_4721_; uint8_t v_checkDeprecated_4722_; uint8_t v_isRecordingDeps_4723_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; uint8_t v___y_4746_; lean_object* v_env_4767_; uint8_t v___x_4768_; uint8_t v___x_4769_; 
v_anyFailed_4664_ = 0;
v___x_4665_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4666_ = l_Lean_instInhabitedFileMap_default;
v___x_4667_ = l_Lean_Options_empty;
v___x_4668_ = lean_box(0);
v___x_4669_ = lean_box(0);
v___x_4670_ = lean_unsigned_to_nat(0u);
v___x_4671_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4672_ = l_Lean_firstFrontendMacroScope;
v___x_4673_ = lean_box(0);
v___x_4674_ = lean_box(0);
v___x_4675_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4676_ = 0;
v___x_4677_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4678_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4679_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4680_ = lean_unsigned_to_nat(32u);
v___x_4681_ = lean_mk_empty_array_with_capacity(v___x_4680_);
lean_dec_ref(v___x_4681_);
v___x_4682_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4683_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4685_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4686_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4687_ = 1;
v___x_4688_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4689_, 0, v_env_4639_);
lean_ctor_set(v___x_4689_, 1, v___x_4677_);
lean_ctor_set(v___x_4689_, 2, v___x_4678_);
lean_ctor_set(v___x_4689_, 3, v___x_4679_);
lean_ctor_set(v___x_4689_, 4, v___x_4682_);
lean_ctor_set(v___x_4689_, 5, v___x_4683_);
lean_ctor_set(v___x_4689_, 6, v___x_4685_);
lean_ctor_set(v___x_4689_, 7, v___x_4686_);
lean_ctor_set(v___x_4689_, 8, v___x_4688_);
lean_ctor_set(v___x_4689_, 9, v___x_4684_);
v___x_4690_ = lean_io_get_num_heartbeats();
v___x_4691_ = lean_st_mk_ref(v___x_4689_);
v___x_4742_ = l_Lean_inheritedTraceOptions;
v___x_4743_ = lean_st_ref_get(v___x_4742_);
v___x_4744_ = lean_st_ref_get(v___x_4691_);
v_env_4767_ = lean_ctor_get(v___x_4744_, 0);
lean_inc_ref(v_env_4767_);
lean_dec(v___x_4744_);
v___x_4768_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4767_);
lean_dec_ref(v_env_4767_);
v___x_4769_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4769_ == 0)
{
if (v___x_4768_ == 0)
{
v___y_4746_ = v___x_4687_;
goto v___jp_4745_;
}
else
{
v_fileName_4709_ = v___x_4665_;
v_fileMap_4710_ = v___x_4666_;
v_currNamespace_4711_ = v___x_4668_;
v_openDecls_4712_ = v___x_4669_;
v_initHeartbeats_4713_ = v___x_4690_;
v_maxHeartbeats_4714_ = v___x_4671_;
v_quotContext_4715_ = v___x_4668_;
v_currMacroScope_4716_ = v___x_4672_;
v_cancelTk_x3f_4717_ = v___x_4673_;
v_inheritedTraceOptions_4718_ = v___x_4743_;
v_currRecDepth_4719_ = v___x_4670_;
v_ref_4720_ = v___x_4674_;
v_suppressElabErrors_4721_ = v_anyFailed_4664_;
v_checkDeprecated_4722_ = v___x_4676_;
v_isRecordingDeps_4723_ = v_anyFailed_4664_;
goto v___jp_4708_;
}
}
else
{
if (v___x_4768_ == 0)
{
v_fileName_4709_ = v___x_4665_;
v_fileMap_4710_ = v___x_4666_;
v_currNamespace_4711_ = v___x_4668_;
v_openDecls_4712_ = v___x_4669_;
v_initHeartbeats_4713_ = v___x_4690_;
v_maxHeartbeats_4714_ = v___x_4671_;
v_quotContext_4715_ = v___x_4668_;
v_currMacroScope_4716_ = v___x_4672_;
v_cancelTk_x3f_4717_ = v___x_4673_;
v_inheritedTraceOptions_4718_ = v___x_4743_;
v_currRecDepth_4719_ = v___x_4670_;
v_ref_4720_ = v___x_4674_;
v_suppressElabErrors_4721_ = v_anyFailed_4664_;
v_checkDeprecated_4722_ = v___x_4676_;
v_isRecordingDeps_4723_ = v_anyFailed_4664_;
goto v___jp_4708_;
}
else
{
v___y_4746_ = v_anyFailed_4664_;
goto v___jp_4745_;
}
}
v___jp_4642_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_mk_io_user_error(v_a_4643_);
v___x_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
v___jp_4646_:
{
if (lean_obj_tag(v_a_4647_) == 0)
{
lean_object* v_msg_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v_msg_4648_ = lean_ctor_get(v_a_4647_, 1);
lean_inc_ref(v_msg_4648_);
lean_dec_ref_known(v_a_4647_, 2);
v___x_4649_ = l_Lean_MessageData_toString(v_msg_4648_);
v___x_4650_ = lean_mk_io_user_error(v___x_4649_);
v___x_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
return v___x_4651_;
}
else
{
lean_object* v_id_4652_; lean_object* v___x_4653_; 
v_id_4652_ = lean_ctor_get(v_a_4647_, 0);
lean_inc(v_id_4652_);
lean_dec_ref_known(v_a_4647_, 2);
v___x_4653_ = l_Lean_InternalExceptionId_getName(v_id_4652_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
lean_dec(v_id_4652_);
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4653_, 1);
v___x_4655_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4656_ = 1;
v___x_4657_ = l_Lean_Name_toString(v_a_4654_, v___x_4656_);
v___x_4658_ = lean_string_append(v___x_4655_, v___x_4657_);
lean_dec_ref(v___x_4657_);
v_a_4643_ = v___x_4658_;
goto v___jp_4642_;
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_dec_ref_known(v___x_4653_, 1);
v___x_4659_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4660_ = l_Nat_reprFast(v_id_4652_);
v___x_4661_ = lean_string_append(v___x_4659_, v___x_4660_);
lean_dec_ref(v___x_4660_);
v___x_4662_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4663_ = lean_string_append(v___x_4661_, v___x_4662_);
v_a_4643_ = v___x_4663_;
goto v___jp_4642_;
}
}
}
v___jp_4692_:
{
if (lean_obj_tag(v___y_4693_) == 0)
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4706_; 
v_a_4694_ = lean_ctor_get(v___y_4693_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___y_4693_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4696_ = v___y_4693_;
v_isShared_4697_ = v_isSharedCheck_4706_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___y_4693_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4706_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v_fst_4699_; lean_object* v_snd_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4704_; 
v___x_4698_ = lean_st_ref_get(v___x_4691_);
lean_dec(v___x_4691_);
lean_dec(v___x_4698_);
v_fst_4699_ = lean_ctor_get(v_a_4694_, 0);
lean_inc(v_fst_4699_);
v_snd_4700_ = lean_ctor_get(v_a_4694_, 1);
lean_inc(v_snd_4700_);
lean_dec(v_a_4694_);
v___x_4701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4701_, 0, v_fst_4699_);
v___x_4702_ = lean_unbox(v_snd_4700_);
lean_dec(v_snd_4700_);
lean_ctor_set_uint8(v___x_4701_, sizeof(void*)*1, v___x_4702_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4701_);
v___x_4704_ = v___x_4696_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4701_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
else
{
lean_object* v_a_4707_; 
lean_dec(v___x_4691_);
v_a_4707_ = lean_ctor_get(v___y_4693_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___y_4693_, 1);
v_a_4647_ = v_a_4707_;
goto v___jp_4646_;
}
}
v___jp_4708_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4724_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4717_);
lean_inc(v_currMacroScope_4716_);
lean_inc(v_quotContext_4715_);
lean_inc(v_maxHeartbeats_4714_);
lean_inc(v_openDecls_4712_);
lean_inc(v_currNamespace_4711_);
lean_inc_ref(v_fileMap_4710_);
lean_inc_ref(v_fileName_4709_);
v___x_4725_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4725_, 0, v_fileName_4709_);
lean_ctor_set(v___x_4725_, 1, v_fileMap_4710_);
lean_ctor_set(v___x_4725_, 2, v___x_4667_);
lean_ctor_set(v___x_4725_, 3, v___x_4724_);
lean_ctor_set(v___x_4725_, 4, v_currNamespace_4711_);
lean_ctor_set(v___x_4725_, 5, v_openDecls_4712_);
lean_ctor_set(v___x_4725_, 6, v_initHeartbeats_4713_);
lean_ctor_set(v___x_4725_, 7, v_maxHeartbeats_4714_);
lean_ctor_set(v___x_4725_, 8, v_quotContext_4715_);
lean_ctor_set(v___x_4725_, 9, v_currMacroScope_4716_);
lean_ctor_set(v___x_4725_, 10, v_cancelTk_x3f_4717_);
lean_ctor_set(v___x_4725_, 11, v_inheritedTraceOptions_4718_);
lean_inc(v_ref_4720_);
v___x_4726_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
lean_ctor_set(v___x_4726_, 1, v_currRecDepth_4719_);
lean_ctor_set(v___x_4726_, 2, v_ref_4720_);
lean_ctor_set_uint16(v___x_4726_, sizeof(void*)*3, v___x_4675_);
lean_ctor_set_uint8(v___x_4726_, sizeof(void*)*3 + 2, v_suppressElabErrors_4721_);
lean_ctor_set_uint8(v___x_4726_, sizeof(void*)*3 + 3, v_checkDeprecated_4722_);
lean_ctor_set_uint8(v___x_4726_, sizeof(void*)*3 + 4, v_isRecordingDeps_4723_);
v___x_4727_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4726_, v___x_4691_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
v___x_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4729_, 0, v_sp_4638_);
lean_ctor_set(v___x_4729_, 1, v_mod_4640_);
v___x_4730_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4728_, v___x_4729_, v___x_4726_, v___x_4691_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v_entries_4732_; lean_object* v_errors_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v_entries_4732_ = lean_ctor_get(v_a_4731_, 0);
lean_inc_ref(v_entries_4732_);
v_errors_4733_ = lean_ctor_get(v_a_4731_, 1);
lean_inc_ref(v_errors_4733_);
lean_dec(v_a_4731_);
v___x_4734_ = lean_array_get_size(v_errors_4733_);
v___x_4735_ = lean_nat_dec_eq(v___x_4734_, v___x_4670_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_box(0);
v___x_4737_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4733_, v_entries_4732_, v___x_4736_, v___x_4687_, v___x_4726_, v___x_4691_);
lean_dec_ref_known(v___x_4726_, 3);
lean_dec_ref(v_errors_4733_);
v___y_4693_ = v___x_4737_;
goto v___jp_4692_;
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = lean_box(0);
v___x_4739_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4733_, v_entries_4732_, v___x_4738_, v_anyFailed_4664_, v___x_4726_, v___x_4691_);
lean_dec_ref_known(v___x_4726_, 3);
lean_dec_ref(v_errors_4733_);
v___y_4693_ = v___x_4739_;
goto v___jp_4692_;
}
}
else
{
lean_object* v_a_4740_; 
lean_dec_ref_known(v___x_4726_, 3);
lean_dec(v___x_4691_);
v_a_4740_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4740_);
lean_dec_ref_known(v___x_4730_, 1);
v_a_4647_ = v_a_4740_;
goto v___jp_4646_;
}
}
else
{
lean_object* v_a_4741_; 
lean_dec_ref_known(v___x_4726_, 3);
lean_dec(v___x_4691_);
lean_dec(v_mod_4640_);
lean_dec(v_sp_4638_);
v_a_4741_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4727_, 1);
v_a_4647_ = v_a_4741_;
goto v___jp_4646_;
}
}
v___jp_4745_:
{
lean_object* v___x_4747_; lean_object* v_env_4748_; lean_object* v_nextMacroScope_4749_; lean_object* v_ngen_4750_; lean_object* v_auxDeclNGen_4751_; lean_object* v_traceState_4752_; lean_object* v_recordedDeps_4753_; lean_object* v_messages_4754_; lean_object* v_infoState_4755_; lean_object* v_snapshotTasks_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4765_; 
v___x_4747_ = lean_st_ref_take(v___x_4691_);
v_env_4748_ = lean_ctor_get(v___x_4747_, 0);
v_nextMacroScope_4749_ = lean_ctor_get(v___x_4747_, 1);
v_ngen_4750_ = lean_ctor_get(v___x_4747_, 2);
v_auxDeclNGen_4751_ = lean_ctor_get(v___x_4747_, 3);
v_traceState_4752_ = lean_ctor_get(v___x_4747_, 4);
v_recordedDeps_4753_ = lean_ctor_get(v___x_4747_, 6);
v_messages_4754_ = lean_ctor_get(v___x_4747_, 7);
v_infoState_4755_ = lean_ctor_get(v___x_4747_, 8);
v_snapshotTasks_4756_ = lean_ctor_get(v___x_4747_, 9);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4765_ == 0)
{
lean_object* v_unused_4766_; 
v_unused_4766_ = lean_ctor_get(v___x_4747_, 5);
lean_dec(v_unused_4766_);
v___x_4758_ = v___x_4747_;
v_isShared_4759_ = v_isSharedCheck_4765_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_snapshotTasks_4756_);
lean_inc(v_infoState_4755_);
lean_inc(v_messages_4754_);
lean_inc(v_recordedDeps_4753_);
lean_inc(v_traceState_4752_);
lean_inc(v_auxDeclNGen_4751_);
lean_inc(v_ngen_4750_);
lean_inc(v_nextMacroScope_4749_);
lean_inc(v_env_4748_);
lean_dec(v___x_4747_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4765_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4760_ = l_Lean_Kernel_enableDiag(v_env_4748_, v___y_4746_);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 5, v___x_4683_);
lean_ctor_set(v___x_4758_, 0, v___x_4760_);
v___x_4762_ = v___x_4758_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_nextMacroScope_4749_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_ngen_4750_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_auxDeclNGen_4751_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v_traceState_4752_);
lean_ctor_set(v_reuseFailAlloc_4764_, 5, v___x_4683_);
lean_ctor_set(v_reuseFailAlloc_4764_, 6, v_recordedDeps_4753_);
lean_ctor_set(v_reuseFailAlloc_4764_, 7, v_messages_4754_);
lean_ctor_set(v_reuseFailAlloc_4764_, 8, v_infoState_4755_);
lean_ctor_set(v_reuseFailAlloc_4764_, 9, v_snapshotTasks_4756_);
v___x_4762_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_st_ref_put(v___x_4691_, v___x_4762_);
v_fileName_4709_ = v___x_4665_;
v_fileMap_4710_ = v___x_4666_;
v_currNamespace_4711_ = v___x_4668_;
v_openDecls_4712_ = v___x_4669_;
v_initHeartbeats_4713_ = v___x_4690_;
v_maxHeartbeats_4714_ = v___x_4671_;
v_quotContext_4715_ = v___x_4668_;
v_currMacroScope_4716_ = v___x_4672_;
v_cancelTk_x3f_4717_ = v___x_4673_;
v_inheritedTraceOptions_4718_ = v___x_4743_;
v_currRecDepth_4719_ = v___x_4670_;
v_ref_4720_ = v___x_4674_;
v_suppressElabErrors_4721_ = v_anyFailed_4664_;
v_checkDeprecated_4722_ = v___x_4676_;
v_isRecordingDeps_4723_ = v_anyFailed_4664_;
goto v___jp_4708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4770_, lean_object* v_env_4771_, lean_object* v_mod_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4770_, v_env_4771_, v_mod_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4775_, size_t v_sz_4776_, size_t v_i_4777_, lean_object* v_b_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4775_, v_sz_4776_, v_i_4777_, v_b_4778_, v___y_4779_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4783_, lean_object* v_sz_4784_, lean_object* v_i_4785_, lean_object* v_b_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
size_t v_sz_boxed_4790_; size_t v_i_boxed_4791_; lean_object* v_res_4792_; 
v_sz_boxed_4790_ = lean_unbox_usize(v_sz_4784_);
lean_dec(v_sz_4784_);
v_i_boxed_4791_ = lean_unbox_usize(v_i_4785_);
lean_dec(v_i_4785_);
v_res_4792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4783_, v_sz_boxed_4790_, v_i_boxed_4791_, v_b_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec_ref(v_as_4783_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = lean_enable_initializer_execution();
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = lean_compacted_region_free(v_region_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4800_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4806_, lean_object* v_k_4807_, uint8_t v_v_4808_){
_start:
{
lean_object* v_map_4809_; uint8_t v_hasTrace_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4824_; 
v_map_4809_ = lean_ctor_get(v_o_4806_, 0);
v_hasTrace_4810_ = lean_ctor_get_uint8(v_o_4806_, sizeof(void*)*1);
v_isSharedCheck_4824_ = !lean_is_exclusive(v_o_4806_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4812_ = v_o_4806_;
v_isShared_4813_ = v_isSharedCheck_4824_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_map_4809_);
lean_dec(v_o_4806_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4824_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4814_, 0, v_v_4808_);
lean_inc(v_k_4807_);
v___x_4815_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4807_, v___x_4814_, v_map_4809_);
if (v_hasTrace_4810_ == 0)
{
lean_object* v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4819_; 
v___x_4816_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4817_ = l_Lean_Name_isPrefixOf(v___x_4816_, v_k_4807_);
lean_dec(v_k_4807_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4815_);
v___x_4819_ = v___x_4812_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4815_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
lean_ctor_set_uint8(v___x_4819_, sizeof(void*)*1, v___x_4817_);
return v___x_4819_;
}
}
else
{
lean_object* v___x_4822_; 
lean_dec(v_k_4807_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4815_);
v___x_4822_ = v___x_4812_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4815_);
lean_ctor_set_uint8(v_reuseFailAlloc_4823_, sizeof(void*)*1, v_hasTrace_4810_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4825_, lean_object* v_k_4826_, lean_object* v_v_4827_){
_start:
{
uint8_t v_v_boxed_4828_; lean_object* v_res_4829_; 
v_v_boxed_4828_ = lean_unbox(v_v_4827_);
v_res_4829_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4825_, v_k_4826_, v_v_boxed_4828_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4830_){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; uint32_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4832_ = lean_unsigned_to_nat(80u);
v___x_4833_ = l_Lean_Json_pretty(v_s_4830_, v___x_4832_);
v___x_4834_ = 10;
v___x_4835_ = lean_string_push(v___x_4833_, v___x_4834_);
v___x_4836_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4837_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4840_, size_t v_sz_4841_, size_t v_i_4842_, lean_object* v_b_4843_){
_start:
{
uint8_t v___x_4845_; 
v___x_4845_ = lean_usize_dec_lt(v_i_4842_, v_sz_4841_);
if (v___x_4845_ == 0)
{
lean_object* v___x_4846_; 
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v_b_4843_);
return v___x_4846_;
}
else
{
lean_object* v___x_4847_; lean_object* v_a_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4847_ = lean_box(0);
v_a_4848_ = lean_array_uget_borrowed(v_as_4840_, v_i_4842_);
lean_inc(v_a_4848_);
v___x_4849_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4848_);
v___x_4850_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4849_);
if (lean_obj_tag(v___x_4850_) == 0)
{
size_t v___x_4851_; size_t v___x_4852_; 
lean_dec_ref_known(v___x_4850_, 1);
v___x_4851_ = ((size_t)1ULL);
v___x_4852_ = lean_usize_add(v_i_4842_, v___x_4851_);
v_i_4842_ = v___x_4852_;
v_b_4843_ = v___x_4847_;
goto _start;
}
else
{
return v___x_4850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4854_, lean_object* v_sz_4855_, lean_object* v_i_4856_, lean_object* v_b_4857_, lean_object* v___y_4858_){
_start:
{
size_t v_sz_boxed_4859_; size_t v_i_boxed_4860_; lean_object* v_res_4861_; 
v_sz_boxed_4859_ = lean_unbox_usize(v_sz_4855_);
lean_dec(v_sz_4855_);
v_i_boxed_4860_ = lean_unbox_usize(v_i_4856_);
lean_dec(v_i_4856_);
v_res_4861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4854_, v_sz_boxed_4859_, v_i_boxed_4860_, v_b_4857_);
lean_dec_ref(v_as_4854_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4862_, size_t v_sz_4863_, size_t v_i_4864_, lean_object* v_bs_4865_){
_start:
{
uint8_t v_anyUnlocated_4866_; 
v_anyUnlocated_4866_ = lean_usize_dec_lt(v_i_4864_, v_sz_4863_);
if (v_anyUnlocated_4866_ == 0)
{
return v_bs_4865_;
}
else
{
lean_object* v___x_4867_; uint8_t v_anyFailed_4868_; lean_object* v_v_4869_; lean_object* v_bs_x27_4870_; lean_object* v___x_4871_; size_t v___x_4872_; size_t v___x_4873_; lean_object* v___x_4874_; 
v___x_4867_ = lean_unsigned_to_nat(0u);
v_anyFailed_4868_ = lean_nat_dec_eq(v___x_4862_, v___x_4867_);
v_v_4869_ = lean_array_uget(v_bs_4865_, v_i_4864_);
v_bs_x27_4870_ = lean_array_uset(v_bs_4865_, v_i_4864_, v___x_4867_);
v___x_4871_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4871_, 0, v_v_4869_);
lean_ctor_set_uint8(v___x_4871_, sizeof(void*)*1, v_anyFailed_4868_);
lean_ctor_set_uint8(v___x_4871_, sizeof(void*)*1 + 1, v_anyUnlocated_4866_);
lean_ctor_set_uint8(v___x_4871_, sizeof(void*)*1 + 2, v_anyFailed_4868_);
v___x_4872_ = ((size_t)1ULL);
v___x_4873_ = lean_usize_add(v_i_4864_, v___x_4872_);
v___x_4874_ = lean_array_uset(v_bs_x27_4870_, v_i_4864_, v___x_4871_);
v_i_4864_ = v___x_4873_;
v_bs_4865_ = v___x_4874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4876_, lean_object* v_sz_4877_, lean_object* v_i_4878_, lean_object* v_bs_4879_){
_start:
{
size_t v_sz_boxed_4880_; size_t v_i_boxed_4881_; lean_object* v_res_4882_; 
v_sz_boxed_4880_ = lean_unbox_usize(v_sz_4877_);
lean_dec(v_sz_4877_);
v_i_boxed_4881_ = lean_unbox_usize(v_i_4878_);
lean_dec(v_i_4878_);
v_res_4882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4876_, v_sz_boxed_4880_, v_i_boxed_4881_, v_bs_4879_);
lean_dec(v___x_4876_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4883_, size_t v_i_4884_, size_t v_stop_4885_, lean_object* v_b_4886_){
_start:
{
uint8_t v___x_4887_; 
v___x_4887_ = lean_usize_dec_eq(v_i_4884_, v_stop_4885_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v_fst_4889_; lean_object* v_snd_4890_; uint8_t v___x_4891_; lean_object* v___x_4892_; size_t v___x_4893_; size_t v___x_4894_; 
v___x_4888_ = lean_array_uget_borrowed(v_as_4883_, v_i_4884_);
v_fst_4889_ = lean_ctor_get(v___x_4888_, 0);
v_snd_4890_ = lean_ctor_get(v___x_4888_, 1);
v___x_4891_ = lean_unbox(v_snd_4890_);
lean_inc(v_fst_4889_);
v___x_4892_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4886_, v_fst_4889_, v___x_4891_);
v___x_4893_ = ((size_t)1ULL);
v___x_4894_ = lean_usize_add(v_i_4884_, v___x_4893_);
v_i_4884_ = v___x_4894_;
v_b_4886_ = v___x_4892_;
goto _start;
}
else
{
return v_b_4886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4896_, lean_object* v_i_4897_, lean_object* v_stop_4898_, lean_object* v_b_4899_){
_start:
{
size_t v_i_boxed_4900_; size_t v_stop_boxed_4901_; lean_object* v_res_4902_; 
v_i_boxed_4900_ = lean_unbox_usize(v_i_4897_);
lean_dec(v_i_4897_);
v_stop_boxed_4901_ = lean_unbox_usize(v_stop_4898_);
lean_dec(v_stop_4898_);
v_res_4902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4896_, v_i_boxed_4900_, v_stop_boxed_4901_, v_b_4899_);
lean_dec_ref(v_as_4896_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4912_, lean_object* v_checkImports_4913_, lean_object* v_args_4914_, lean_object* v___x_4915_, lean_object* v_as_4916_, size_t v_sz_4917_, size_t v_i_4918_, lean_object* v_b_4919_){
_start:
{
lean_object* v_a_4922_; lean_object* v___x_4926_; uint8_t v_anyFailed_4927_; uint8_t v_anyUnlocated_4928_; lean_object* v___x_4929_; lean_object* v_envLinterModule_4930_; uint8_t v___x_4931_; 
v___x_4926_ = lean_unsigned_to_nat(0u);
v_anyFailed_4927_ = lean_nat_dec_eq(v___x_4912_, v___x_4926_);
v_anyUnlocated_4928_ = 1;
v___x_4929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4930_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4930_, 0, v___x_4929_);
lean_ctor_set_uint8(v_envLinterModule_4930_, sizeof(void*)*1, v_anyFailed_4927_);
lean_ctor_set_uint8(v_envLinterModule_4930_, sizeof(void*)*1 + 1, v_anyUnlocated_4928_);
lean_ctor_set_uint8(v_envLinterModule_4930_, sizeof(void*)*1 + 2, v_anyFailed_4927_);
v___x_4931_ = lean_usize_dec_lt(v_i_4918_, v_sz_4917_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; 
lean_dec_ref_known(v_envLinterModule_4930_, 1);
lean_dec(v___x_4915_);
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v_b_4919_);
return v___x_4932_;
}
else
{
lean_object* v_snd_4933_; lean_object* v_snd_4934_; lean_object* v_snd_4935_; lean_object* v_snd_4936_; lean_object* v_fst_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_5246_; 
v_snd_4933_ = lean_ctor_get(v_b_4919_, 1);
lean_inc(v_snd_4933_);
v_snd_4934_ = lean_ctor_get(v_snd_4933_, 1);
lean_inc(v_snd_4934_);
v_snd_4935_ = lean_ctor_get(v_snd_4934_, 1);
lean_inc(v_snd_4935_);
v_snd_4936_ = lean_ctor_get(v_snd_4935_, 1);
lean_inc(v_snd_4936_);
v_fst_4937_ = lean_ctor_get(v_b_4919_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v_b_4919_);
if (v_isSharedCheck_5246_ == 0)
{
lean_object* v_unused_5247_; 
v_unused_5247_ = lean_ctor_get(v_b_4919_, 1);
lean_dec(v_unused_5247_);
v___x_4939_ = v_b_4919_;
v_isShared_4940_ = v_isSharedCheck_5246_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_fst_4937_);
lean_dec(v_b_4919_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_5246_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_fst_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_5244_; 
v_fst_4941_ = lean_ctor_get(v_snd_4933_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v_snd_4933_);
if (v_isSharedCheck_5244_ == 0)
{
lean_object* v_unused_5245_; 
v_unused_5245_ = lean_ctor_get(v_snd_4933_, 1);
lean_dec(v_unused_5245_);
v___x_4943_ = v_snd_4933_;
v_isShared_4944_ = v_isSharedCheck_5244_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_fst_4941_);
lean_dec(v_snd_4933_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_5244_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v_fst_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_5242_; 
v_fst_4945_ = lean_ctor_get(v_snd_4934_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v_snd_4934_);
if (v_isSharedCheck_5242_ == 0)
{
lean_object* v_unused_5243_; 
v_unused_5243_ = lean_ctor_get(v_snd_4934_, 1);
lean_dec(v_unused_5243_);
v___x_4947_ = v_snd_4934_;
v_isShared_4948_ = v_isSharedCheck_5242_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_fst_4945_);
lean_dec(v_snd_4934_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_5242_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v_fst_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_5240_; 
v_fst_4949_ = lean_ctor_get(v_snd_4935_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_snd_4935_);
if (v_isSharedCheck_5240_ == 0)
{
lean_object* v_unused_5241_; 
v_unused_5241_ = lean_ctor_get(v_snd_4935_, 1);
lean_dec(v_unused_5241_);
v___x_4951_ = v_snd_4935_;
v_isShared_4952_ = v_isSharedCheck_5240_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_fst_4949_);
lean_dec(v_snd_4935_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_5240_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v_fst_4953_; lean_object* v_snd_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5239_; 
v_fst_4953_ = lean_ctor_get(v_snd_4936_, 0);
v_snd_4954_ = lean_ctor_get(v_snd_4936_, 1);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_snd_4936_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_4956_ = v_snd_4936_;
v_isShared_4957_ = v_isSharedCheck_5239_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_snd_4954_);
lean_inc(v_fst_4953_);
lean_dec(v_snd_4936_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5239_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4958_; lean_object* v_a_4959_; lean_object* v___y_4961_; lean_object* v___y_4962_; uint8_t v_anyFailed_4963_; uint8_t v_anyUnlocated_4964_; lean_object* v_records_4965_; lean_object* v_codeQualityEntries_4966_; lean_object* v___y_5113_; lean_object* v___y_5114_; uint8_t v_anyFailed_5115_; uint8_t v_anyUnlocated_5116_; lean_object* v_records_5117_; lean_object* v_codeQualityEntries_5118_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_4958_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_4959_ = lean_array_uget_borrowed(v_as_4916_, v_i_4918_);
v___x_5176_ = lean_enable_initializer_execution();
lean_inc(v_a_4959_);
v___x_5177_ = l_Lean_findOLean(v_a_4959_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5179_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5178_);
lean_dec_ref_known(v___x_5177_, 1);
v___x_5179_ = l_Lean_readModuleData(v_a_5178_);
lean_dec(v_a_5178_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; lean_object* v_fst_5181_; lean_object* v_snd_5182_; uint8_t v___x_5183_; uint8_t v___y_5185_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref_known(v___x_5179_, 1);
v_fst_5181_ = lean_ctor_get(v_a_5180_, 0);
lean_inc(v_fst_5181_);
v_snd_5182_ = lean_ctor_get(v_a_5180_, 1);
lean_inc(v_snd_5182_);
lean_dec(v_a_5180_);
v___x_5183_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5181_);
lean_dec(v_fst_5181_);
if (v___x_5183_ == 0)
{
uint8_t v___x_5221_; 
v___x_5221_ = 2;
v___y_5185_ = v___x_5221_;
goto v___jp_5184_;
}
else
{
uint8_t v___x_5222_; 
v___x_5222_ = 1;
v___y_5185_ = v___x_5222_;
goto v___jp_5184_;
}
v___jp_5184_:
{
lean_object* v___x_5186_; 
v___x_5186_ = lean_compacted_region_free(v_snd_5182_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; uint32_t v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
lean_dec_ref_known(v___x_5186_, 1);
lean_inc(v_a_4959_);
v___x_5187_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5187_, 0, v_a_4959_);
lean_ctor_set_uint8(v___x_5187_, sizeof(void*)*1, v_anyFailed_4927_);
lean_ctor_set_uint8(v___x_5187_, sizeof(void*)*1 + 1, v_anyUnlocated_4928_);
lean_ctor_set_uint8(v___x_5187_, sizeof(void*)*1 + 2, v_anyFailed_4927_);
v___x_5188_ = lean_unsigned_to_nat(2u);
v___x_5189_ = lean_mk_empty_array_with_capacity(v___x_5188_);
v___x_5190_ = lean_array_push(v___x_5189_, v___x_5187_);
v___x_5191_ = lean_array_push(v___x_5190_, v_envLinterModule_4930_);
v___x_5192_ = l_Array_append___redArg(v___x_5191_, v_checkImports_4913_);
v___x_5193_ = l_Lean_Options_empty;
v___x_5194_ = 1024;
v___x_5195_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5196_ = lean_box(1);
v___x_5197_ = l_Lean_importModules(v___x_5192_, v___x_5193_, v___x_5194_, v___x_5195_, v_anyFailed_4927_, v_anyUnlocated_4928_, v___y_5185_, v___x_5196_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v_linterOverrides_5199_; lean_object* v___x_5200_; uint8_t v___x_5201_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5197_, 1);
v_linterOverrides_5199_ = lean_ctor_get(v_args_4914_, 0);
v___x_5200_ = lean_array_get_size(v_linterOverrides_5199_);
v___x_5201_ = lean_nat_dec_lt(v___x_4926_, v___x_5200_);
if (v___x_5201_ == 0)
{
v___y_5136_ = v_a_5198_;
v___y_5137_ = v___x_5193_;
goto v___jp_5135_;
}
else
{
size_t v___x_5202_; size_t v___x_5203_; lean_object* v___x_5204_; 
v___x_5202_ = ((size_t)0ULL);
v___x_5203_ = lean_usize_of_nat(v___x_5200_);
v___x_5204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5199_, v___x_5202_, v___x_5203_, v___x_5193_);
v___y_5136_ = v_a_5198_;
v___y_5137_ = v___x_5204_;
goto v___jp_5135_;
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_dec(v_fst_4949_);
lean_del_object(v___x_4947_);
lean_dec(v_fst_4945_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_fst_4937_);
lean_dec(v___x_4915_);
v_a_5205_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5197_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5197_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_dec(v_fst_4949_);
lean_del_object(v___x_4947_);
lean_dec(v_fst_4945_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_fst_4937_);
lean_dec_ref_known(v_envLinterModule_4930_, 1);
lean_dec(v___x_4915_);
v_a_5213_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5186_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5186_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
}
else
{
lean_object* v_a_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5230_; 
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_dec(v_fst_4949_);
lean_del_object(v___x_4947_);
lean_dec(v_fst_4945_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_fst_4937_);
lean_dec_ref_known(v_envLinterModule_4930_, 1);
lean_dec(v___x_4915_);
v_a_5223_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5225_ = v___x_5179_;
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_a_5223_);
lean_dec(v___x_5179_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v___x_5228_; 
if (v_isShared_5226_ == 0)
{
v___x_5228_ = v___x_5225_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_dec(v_fst_4949_);
lean_del_object(v___x_4947_);
lean_dec(v_fst_4945_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_fst_4937_);
lean_dec_ref_known(v_envLinterModule_4930_, 1);
lean_dec(v___x_4915_);
v_a_5231_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5177_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5177_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
v___jp_4960_:
{
uint8_t v_mode_4967_; uint8_t v___x_4968_; uint8_t v___x_4969_; 
v_mode_4967_ = lean_ctor_get_uint8(v_args_4914_, sizeof(void*)*4 + 1);
v___x_4968_ = 2;
v___x_4969_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4967_, v___x_4968_);
if (v___x_4969_ == 0)
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = l_Lean_Name_getRoot(v_a_4959_);
lean_inc(v___x_4915_);
v___x_4971_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4914_, v___y_4961_, v___x_4915_, v___y_4962_, v___x_4970_, v_fst_4953_);
lean_dec_ref(v___y_4961_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v_outcome_4973_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref_known(v___x_4971_, 1);
v_outcome_4973_ = lean_ctor_get(v_a_4972_, 0);
if (lean_obj_tag(v_outcome_4973_) == 0)
{
uint8_t v_failed_4974_; 
v_failed_4974_ = lean_ctor_get_uint8(v_outcome_4973_, 0);
if (v_failed_4974_ == 0)
{
lean_object* v_checkedModules_4975_; lean_object* v___x_4977_; 
v_checkedModules_4975_ = lean_ctor_get(v_a_4972_, 1);
lean_inc(v_checkedModules_4975_);
lean_dec(v_a_4972_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v_checkedModules_4975_);
v___x_4977_ = v___x_4956_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_checkedModules_4975_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_snd_4954_);
v___x_4977_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
lean_object* v___x_4979_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_4977_);
lean_ctor_set(v___x_4951_, 0, v_codeQualityEntries_4966_);
v___x_4979_ = v___x_4951_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_codeQualityEntries_4966_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4981_; 
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_4979_);
lean_ctor_set(v___x_4947_, 0, v_records_4965_);
v___x_4981_ = v___x_4947_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_records_4965_);
lean_ctor_set(v_reuseFailAlloc_4990_, 1, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4982_ = lean_box(v_anyUnlocated_4964_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_4981_);
lean_ctor_set(v___x_4943_, 0, v___x_4982_);
v___x_4984_ = v___x_4943_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v___x_4981_);
v___x_4984_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4985_ = lean_box(v_anyFailed_4963_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_4984_);
lean_ctor_set(v___x_4939_, 0, v___x_4985_);
v___x_4987_ = v___x_4939_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v___x_4984_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
v_a_4922_ = v___x_4987_;
goto v___jp_4921_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4993_; lean_object* v___x_4995_; 
v_checkedModules_4993_ = lean_ctor_get(v_a_4972_, 1);
lean_inc(v_checkedModules_4993_);
lean_dec(v_a_4972_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v_checkedModules_4993_);
v___x_4995_ = v___x_4956_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_checkedModules_4993_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_snd_4954_);
v___x_4995_ = v_reuseFailAlloc_5010_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4997_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_4995_);
lean_ctor_set(v___x_4951_, 0, v_codeQualityEntries_4966_);
v___x_4997_ = v___x_4951_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_codeQualityEntries_4966_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_5009_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4999_; 
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_4997_);
lean_ctor_set(v___x_4947_, 0, v_records_4965_);
v___x_4999_ = v___x_4947_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_records_4965_);
lean_ctor_set(v_reuseFailAlloc_5008_, 1, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5008_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_5000_ = lean_box(v_anyUnlocated_4964_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_4999_);
lean_ctor_set(v___x_4943_, 0, v___x_5000_);
v___x_5002_ = v___x_4943_;
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
v___x_5003_ = lean_box(v_anyUnlocated_4928_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_5002_);
lean_ctor_set(v___x_4939_, 0, v___x_5003_);
v___x_5005_ = v___x_4939_;
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
v_a_4922_ = v___x_5005_;
goto v___jp_4921_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_5011_; lean_object* v_records_5012_; uint8_t v_unlocated_5013_; lean_object* v___x_5014_; 
lean_inc_ref(v_outcome_4973_);
v_checkedModules_5011_ = lean_ctor_get(v_a_4972_, 1);
lean_inc(v_checkedModules_5011_);
lean_dec(v_a_4972_);
v_records_5012_ = lean_ctor_get(v_outcome_4973_, 0);
lean_inc_ref(v_records_5012_);
v_unlocated_5013_ = lean_ctor_get_uint8(v_outcome_4973_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4973_, 1);
v___x_5014_ = l_Array_append___redArg(v_records_4965_, v_records_5012_);
lean_dec_ref(v_records_5012_);
if (v_unlocated_5013_ == 0)
{
lean_object* v___x_5016_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v_checkedModules_5011_);
v___x_5016_ = v___x_4956_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_checkedModules_5011_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_snd_4954_);
v___x_5016_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5018_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_5016_);
lean_ctor_set(v___x_4951_, 0, v_codeQualityEntries_4966_);
v___x_5018_ = v___x_4951_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_codeQualityEntries_4966_);
lean_ctor_set(v_reuseFailAlloc_5030_, 1, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5020_; 
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_5018_);
lean_ctor_set(v___x_4947_, 0, v___x_5014_);
v___x_5020_ = v___x_4947_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5029_, 1, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5021_ = lean_box(v_anyUnlocated_4964_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_5020_);
lean_ctor_set(v___x_4943_, 0, v___x_5021_);
v___x_5023_ = v___x_4943_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5021_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5020_);
v___x_5023_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5024_ = lean_box(v_anyFailed_4963_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_5023_);
lean_ctor_set(v___x_4939_, 0, v___x_5024_);
v___x_5026_ = v___x_4939_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5023_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
v_a_4922_ = v___x_5026_;
goto v___jp_4921_;
}
}
}
}
}
}
else
{
lean_object* v___x_5033_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v_checkedModules_5011_);
v___x_5033_ = v___x_4956_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_checkedModules_5011_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_snd_4954_);
v___x_5033_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5035_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_5033_);
lean_ctor_set(v___x_4951_, 0, v_codeQualityEntries_4966_);
v___x_5035_ = v___x_4951_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_codeQualityEntries_4966_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v___x_5033_);
v___x_5035_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
lean_object* v___x_5037_; 
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_5035_);
lean_ctor_set(v___x_4947_, 0, v___x_5014_);
v___x_5037_ = v___x_4947_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5035_);
v___x_5037_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5040_; 
v___x_5038_ = lean_box(v_anyUnlocated_4928_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_5037_);
lean_ctor_set(v___x_4943_, 0, v___x_5038_);
v___x_5040_ = v___x_4943_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5038_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v___x_5037_);
v___x_5040_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
lean_object* v___x_5041_; lean_object* v___x_5043_; 
v___x_5041_ = lean_box(v_anyFailed_4963_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_5040_);
lean_ctor_set(v___x_4939_, 0, v___x_5041_);
v___x_5043_ = v___x_4939_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___x_5040_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
v_a_4922_ = v___x_5043_;
goto v___jp_4921_;
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
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec_ref(v_codeQualityEntries_4966_);
lean_dec_ref(v_records_4965_);
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_del_object(v___x_4951_);
lean_del_object(v___x_4947_);
lean_del_object(v___x_4943_);
lean_del_object(v___x_4939_);
lean_dec(v___x_4915_);
v_a_5049_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_4971_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_4971_);
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
else
{
lean_object* v___x_5057_; lean_object* v_fst_5058_; lean_object* v_snd_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5111_; 
lean_del_object(v___x_4939_);
v___x_5057_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4914_, v___y_4961_, v___y_4962_, v_a_4959_, v_snd_4954_);
lean_dec_ref(v___y_4961_);
v_fst_5058_ = lean_ctor_get(v___x_5057_, 0);
v_snd_5059_ = lean_ctor_get(v___x_5057_, 1);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5061_ = v___x_5057_;
v_isShared_5062_ = v_isSharedCheck_5111_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_snd_5059_);
lean_inc(v_fst_5058_);
lean_dec(v___x_5057_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5111_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = l_Array_append___redArg(v_codeQualityEntries_4966_, v_fst_5058_);
lean_dec(v_fst_5058_);
lean_inc(v_a_4959_);
lean_inc(v___x_4915_);
v___x_5064_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4915_, v___y_4962_, v_a_4959_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; lean_object* v_entries_5066_; uint8_t v_failed_5067_; lean_object* v___x_5068_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___x_5064_, 1);
v_entries_5066_ = lean_ctor_get(v_a_5065_, 0);
lean_inc_ref(v_entries_5066_);
v_failed_5067_ = lean_ctor_get_uint8(v_a_5065_, sizeof(void*)*1);
lean_dec(v_a_5065_);
v___x_5068_ = l_Array_append___redArg(v___x_5063_, v_entries_5066_);
lean_dec_ref(v_entries_5066_);
if (v_failed_5067_ == 0)
{
lean_object* v___x_5070_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 0, v_fst_4953_);
v___x_5070_ = v___x_5061_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_fst_4953_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_snd_5059_);
v___x_5070_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5072_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 1, v___x_5070_);
lean_ctor_set(v___x_4956_, 0, v___x_5068_);
v___x_5072_ = v___x_4956_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5074_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_5072_);
lean_ctor_set(v___x_4951_, 0, v_records_4965_);
v___x_5074_ = v___x_4951_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_records_4965_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5077_; 
v___x_5075_ = lean_box(v_anyUnlocated_4964_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_5074_);
lean_ctor_set(v___x_4947_, 0, v___x_5075_);
v___x_5077_ = v___x_4947_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5075_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v___x_5074_);
v___x_5077_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5078_ = lean_box(v_anyFailed_4963_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_5077_);
lean_ctor_set(v___x_4943_, 0, v___x_5078_);
v___x_5080_ = v___x_4943_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v___x_5077_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
v_a_4922_ = v___x_5080_;
goto v___jp_4921_;
}
}
}
}
}
}
else
{
lean_object* v___x_5087_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 0, v_fst_4953_);
v___x_5087_ = v___x_5061_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_fst_4953_);
lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_snd_5059_);
v___x_5087_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5089_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 1, v___x_5087_);
lean_ctor_set(v___x_4956_, 0, v___x_5068_);
v___x_5089_ = v___x_4956_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
lean_object* v___x_5091_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 1, v___x_5089_);
lean_ctor_set(v___x_4951_, 0, v_records_4965_);
v___x_5091_ = v___x_4951_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_records_4965_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5092_ = lean_box(v_anyUnlocated_4964_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_5091_);
lean_ctor_set(v___x_4947_, 0, v___x_5092_);
v___x_5094_ = v___x_4947_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5091_);
v___x_5094_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; lean_object* v___x_5097_; 
v___x_5095_ = lean_box(v_anyUnlocated_4928_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___x_5094_);
lean_ctor_set(v___x_4943_, 0, v___x_5095_);
v___x_5097_ = v___x_4943_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5095_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v___x_5094_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
v_a_4922_ = v___x_5097_;
goto v___jp_4921_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v___x_5063_);
lean_del_object(v___x_5061_);
lean_dec(v_snd_5059_);
lean_dec_ref(v_records_4965_);
lean_del_object(v___x_4956_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_del_object(v___x_4947_);
lean_del_object(v___x_4943_);
lean_dec(v___x_4915_);
v_a_5103_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5064_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5064_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
v___jp_5112_:
{
lean_object* v___x_5119_; 
lean_inc(v_a_4959_);
lean_inc_ref(v___y_5114_);
lean_inc(v___x_4915_);
lean_inc_ref(v___y_5113_);
v___x_5119_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4914_, v___y_5113_, v___x_4915_, v___y_5114_, v_a_4959_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
switch(lean_obj_tag(v_a_5120_))
{
case 0:
{
uint8_t v_failed_5121_; 
v_failed_5121_ = lean_ctor_get_uint8(v_a_5120_, 0);
lean_dec_ref_known(v_a_5120_, 0);
if (v_failed_5121_ == 0)
{
v___y_4961_ = v___y_5113_;
v___y_4962_ = v___y_5114_;
v_anyFailed_4963_ = v_anyFailed_5115_;
v_anyUnlocated_4964_ = v_anyUnlocated_5116_;
v_records_4965_ = v_records_5117_;
v_codeQualityEntries_4966_ = v_codeQualityEntries_5118_;
goto v___jp_4960_;
}
else
{
v___y_4961_ = v___y_5113_;
v___y_4962_ = v___y_5114_;
v_anyFailed_4963_ = v_anyUnlocated_4928_;
v_anyUnlocated_4964_ = v_anyUnlocated_5116_;
v_records_4965_ = v_records_5117_;
v_codeQualityEntries_4966_ = v_codeQualityEntries_5118_;
goto v___jp_4960_;
}
}
case 1:
{
lean_object* v_records_5122_; uint8_t v_unlocated_5123_; lean_object* v___x_5124_; 
v_records_5122_ = lean_ctor_get(v_a_5120_, 0);
lean_inc_ref(v_records_5122_);
v_unlocated_5123_ = lean_ctor_get_uint8(v_a_5120_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5120_, 1);
v___x_5124_ = l_Array_append___redArg(v_records_5117_, v_records_5122_);
lean_dec_ref(v_records_5122_);
if (v_unlocated_5123_ == 0)
{
v___y_4961_ = v___y_5113_;
v___y_4962_ = v___y_5114_;
v_anyFailed_4963_ = v_anyFailed_5115_;
v_anyUnlocated_4964_ = v_anyUnlocated_5116_;
v_records_4965_ = v___x_5124_;
v_codeQualityEntries_4966_ = v_codeQualityEntries_5118_;
goto v___jp_4960_;
}
else
{
v___y_4961_ = v___y_5113_;
v___y_4962_ = v___y_5114_;
v_anyFailed_4963_ = v_anyFailed_5115_;
v_anyUnlocated_4964_ = v_anyUnlocated_4928_;
v_records_4965_ = v___x_5124_;
v_codeQualityEntries_4966_ = v_codeQualityEntries_5118_;
goto v___jp_4960_;
}
}
default: 
{
lean_object* v_entries_5125_; lean_object* v___x_5126_; 
v_entries_5125_ = lean_ctor_get(v_a_5120_, 0);
lean_inc_ref(v_entries_5125_);
lean_dec_ref_known(v_a_5120_, 1);
v___x_5126_ = l_Array_append___redArg(v_codeQualityEntries_5118_, v_entries_5125_);
lean_dec_ref(v_entries_5125_);
v___y_4961_ = v___y_5113_;
v___y_4962_ = v___y_5114_;
v_anyFailed_4963_ = v_anyFailed_5115_;
v_anyUnlocated_4964_ = v_anyUnlocated_5116_;
v_records_4965_ = v_records_5117_;
v_codeQualityEntries_4966_ = v___x_5126_;
goto v___jp_4960_;
}
}
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec_ref(v_codeQualityEntries_5118_);
lean_dec_ref(v_records_5117_);
lean_dec_ref(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_del_object(v___x_4947_);
lean_del_object(v___x_4943_);
lean_del_object(v___x_4939_);
lean_dec(v___x_4915_);
v_a_5127_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5119_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5119_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
v___jp_5135_:
{
lean_object* v___x_5138_; lean_object* v_toEnvExtension_5139_; lean_object* v_asyncMode_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v_merged_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5174_; 
v___x_5138_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5139_ = lean_ctor_get(v___x_5138_, 0);
v_asyncMode_5140_ = lean_ctor_get(v_toEnvExtension_5139_, 2);
v___x_5141_ = lean_box(0);
lean_inc_ref(v___y_5136_);
v___x_5142_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4958_, v___x_5138_, v___y_5136_, v_asyncMode_5140_, v___x_5141_, v_anyFailed_4927_);
v_merged_5143_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5174_ == 0)
{
lean_object* v_unused_5175_; 
v_unused_5175_ = lean_ctor_get(v___x_5142_, 1);
lean_dec(v_unused_5175_);
v___x_5145_ = v___x_5142_;
v_isShared_5146_ = v_isSharedCheck_5174_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_merged_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5174_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 1, v_merged_5143_);
lean_ctor_set(v___x_5145_, 0, v___y_5137_);
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___y_5137_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v_merged_5143_);
v___x_5148_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4914_, v___x_5148_, v___y_5136_, v_a_4959_);
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
uint8_t v___x_5151_; 
v___x_5151_ = lean_unbox(v_fst_4937_);
lean_dec(v_fst_4937_);
if (v___x_5151_ == 0)
{
uint8_t v_failed_5152_; uint8_t v___x_5153_; 
v_failed_5152_ = lean_ctor_get_uint8(v_a_5150_, 0);
lean_dec_ref_known(v_a_5150_, 0);
v___x_5153_ = lean_unbox(v_fst_4941_);
lean_dec(v_fst_4941_);
v___y_5113_ = v___x_5148_;
v___y_5114_ = v___y_5136_;
v_anyFailed_5115_ = v_failed_5152_;
v_anyUnlocated_5116_ = v___x_5153_;
v_records_5117_ = v_fst_4945_;
v_codeQualityEntries_5118_ = v_fst_4949_;
goto v___jp_5112_;
}
else
{
uint8_t v___x_5154_; 
lean_dec_ref_known(v_a_5150_, 0);
v___x_5154_ = lean_unbox(v_fst_4941_);
lean_dec(v_fst_4941_);
v___y_5113_ = v___x_5148_;
v___y_5114_ = v___y_5136_;
v_anyFailed_5115_ = v_anyUnlocated_4928_;
v_anyUnlocated_5116_ = v___x_5154_;
v_records_5117_ = v_fst_4945_;
v_codeQualityEntries_5118_ = v_fst_4949_;
goto v___jp_5112_;
}
}
case 1:
{
lean_object* v_records_5155_; uint8_t v_unlocated_5156_; lean_object* v___x_5157_; 
v_records_5155_ = lean_ctor_get(v_a_5150_, 0);
lean_inc_ref(v_records_5155_);
v_unlocated_5156_ = lean_ctor_get_uint8(v_a_5150_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5150_, 1);
v___x_5157_ = l_Array_append___redArg(v_fst_4945_, v_records_5155_);
lean_dec_ref(v_records_5155_);
if (v_unlocated_5156_ == 0)
{
uint8_t v___x_5158_; uint8_t v___x_5159_; 
v___x_5158_ = lean_unbox(v_fst_4937_);
lean_dec(v_fst_4937_);
v___x_5159_ = lean_unbox(v_fst_4941_);
lean_dec(v_fst_4941_);
v___y_5113_ = v___x_5148_;
v___y_5114_ = v___y_5136_;
v_anyFailed_5115_ = v___x_5158_;
v_anyUnlocated_5116_ = v___x_5159_;
v_records_5117_ = v___x_5157_;
v_codeQualityEntries_5118_ = v_fst_4949_;
goto v___jp_5112_;
}
else
{
uint8_t v___x_5160_; 
lean_dec(v_fst_4941_);
v___x_5160_ = lean_unbox(v_fst_4937_);
lean_dec(v_fst_4937_);
v___y_5113_ = v___x_5148_;
v___y_5114_ = v___y_5136_;
v_anyFailed_5115_ = v___x_5160_;
v_anyUnlocated_5116_ = v_anyUnlocated_4928_;
v_records_5117_ = v___x_5157_;
v_codeQualityEntries_5118_ = v_fst_4949_;
goto v___jp_5112_;
}
}
default: 
{
lean_object* v_entries_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; uint8_t v___x_5164_; 
v_entries_5161_ = lean_ctor_get(v_a_5150_, 0);
lean_inc_ref(v_entries_5161_);
lean_dec_ref_known(v_a_5150_, 1);
v___x_5162_ = l_Array_append___redArg(v_fst_4949_, v_entries_5161_);
lean_dec_ref(v_entries_5161_);
v___x_5163_ = lean_unbox(v_fst_4937_);
lean_dec(v_fst_4937_);
v___x_5164_ = lean_unbox(v_fst_4941_);
lean_dec(v_fst_4941_);
v___y_5113_ = v___x_5148_;
v___y_5114_ = v___y_5136_;
v_anyFailed_5115_ = v___x_5163_;
v_anyUnlocated_5116_ = v___x_5164_;
v_records_5117_ = v_fst_4945_;
v_codeQualityEntries_5118_ = v___x_5162_;
goto v___jp_5112_;
}
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec_ref(v___x_5148_);
lean_dec_ref(v___y_5136_);
lean_del_object(v___x_4956_);
lean_dec(v_snd_4954_);
lean_dec(v_fst_4953_);
lean_del_object(v___x_4951_);
lean_dec(v_fst_4949_);
lean_del_object(v___x_4947_);
lean_dec(v_fst_4945_);
lean_del_object(v___x_4943_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_fst_4937_);
lean_dec(v___x_4915_);
v_a_5165_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5149_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5149_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
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
v___jp_4921_:
{
size_t v___x_4923_; size_t v___x_4924_; 
v___x_4923_ = ((size_t)1ULL);
v___x_4924_ = lean_usize_add(v_i_4918_, v___x_4923_);
v_i_4918_ = v___x_4924_;
v_b_4919_ = v_a_4922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5248_, lean_object* v_checkImports_5249_, lean_object* v_args_5250_, lean_object* v___x_5251_, lean_object* v_as_5252_, lean_object* v_sz_5253_, lean_object* v_i_5254_, lean_object* v_b_5255_, lean_object* v___y_5256_){
_start:
{
size_t v_sz_boxed_5257_; size_t v_i_boxed_5258_; lean_object* v_res_5259_; 
v_sz_boxed_5257_ = lean_unbox_usize(v_sz_5253_);
lean_dec(v_sz_5253_);
v_i_boxed_5258_ = lean_unbox_usize(v_i_5254_);
lean_dec(v_i_5254_);
v_res_5259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5248_, v_checkImports_5249_, v_args_5250_, v___x_5251_, v_as_5252_, v_sz_boxed_5257_, v_i_boxed_5258_, v_b_5255_);
lean_dec_ref(v_as_5252_);
lean_dec_ref(v_args_5250_);
lean_dec_ref(v_checkImports_5249_);
lean_dec(v___x_5248_);
return v_res_5259_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5260_ = l_Lean_NameSet_empty;
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v___x_5260_);
return v___x_5261_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5262_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5263_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
lean_ctor_set(v___x_5264_, 1, v___x_5262_);
return v___x_5264_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5265_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5266_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5266_);
lean_ctor_set(v___x_5267_, 1, v___x_5265_);
return v___x_5267_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5269_; lean_object* v___x_5270_; 
v___x_5269_ = 0;
v___x_5270_ = lean_box_uint32(v___x_5269_);
return v___x_5270_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5271_; lean_object* v___x_5272_; 
v___x_5271_ = 1;
v___x_5272_ = lean_box_uint32(v___x_5271_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5273_){
_start:
{
lean_object* v_mods_5275_; uint8_t v_mode_5276_; lean_object* v_checks_5277_; lean_object* v_srcSearchPath_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; uint8_t v_anyFailed_5281_; 
v_mods_5275_ = lean_ctor_get(v_args_5273_, 1);
lean_inc_ref(v_mods_5275_);
v_mode_5276_ = lean_ctor_get_uint8(v_args_5273_, sizeof(void*)*4 + 1);
v_checks_5277_ = lean_ctor_get(v_args_5273_, 2);
v_srcSearchPath_5278_ = lean_ctor_get(v_args_5273_, 3);
v___x_5279_ = lean_array_get_size(v_mods_5275_);
v___x_5280_ = lean_unsigned_to_nat(0u);
v_anyFailed_5281_ = lean_nat_dec_eq(v___x_5279_, v___x_5280_);
if (v_anyFailed_5281_ == 0)
{
size_t v_sz_5282_; size_t v___x_5283_; lean_object* v_checkImports_5284_; lean_object* v___x_5285_; 
v_sz_5282_ = lean_array_size(v_checks_5277_);
v___x_5283_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5277_);
v_checkImports_5284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5279_, v_sz_5282_, v___x_5283_, v_checks_5277_);
v___x_5285_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; size_t v_sz_5293_; lean_object* v___x_5294_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
lean_inc(v_srcSearchPath_5278_);
v___x_5287_ = l_List_appendTR___redArg(v_srcSearchPath_5278_, v_a_5286_);
v___x_5288_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5289_ = lean_box(v_anyFailed_5281_);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
lean_ctor_set(v___x_5290_, 1, v___x_5288_);
v___x_5291_ = lean_box(v_anyFailed_5281_);
v___x_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
lean_ctor_set(v___x_5292_, 1, v___x_5290_);
v_sz_5293_ = lean_array_size(v_mods_5275_);
v___x_5294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5279_, v_checkImports_5284_, v_args_5273_, v___x_5287_, v_mods_5275_, v_sz_5293_, v___x_5283_, v___x_5292_);
lean_dec_ref(v_mods_5275_);
lean_dec_ref(v_args_5273_);
lean_dec_ref(v_checkImports_5284_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5366_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5297_ = v___x_5294_;
v_isShared_5298_ = v_isSharedCheck_5366_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5294_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5366_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
switch(v_mode_5276_)
{
case 0:
{
lean_object* v_fst_5299_; uint8_t v___x_5300_; 
v_fst_5299_ = lean_ctor_get(v_a_5295_, 0);
lean_inc(v_fst_5299_);
lean_dec(v_a_5295_);
v___x_5300_ = lean_unbox(v_fst_5299_);
lean_dec(v_fst_5299_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5301_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5301_);
v___x_5303_ = v___x_5297_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
else
{
lean_object* v___x_5305_; lean_object* v___x_5307_; 
v___x_5305_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5305_);
v___x_5307_ = v___x_5297_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5305_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
case 1:
{
lean_object* v_snd_5309_; lean_object* v_snd_5310_; lean_object* v_fst_5311_; lean_object* v_fst_5312_; lean_object* v___x_5313_; 
v_snd_5309_ = lean_ctor_get(v_a_5295_, 1);
lean_inc(v_snd_5309_);
lean_del_object(v___x_5297_);
lean_dec(v_a_5295_);
v_snd_5310_ = lean_ctor_get(v_snd_5309_, 1);
lean_inc(v_snd_5310_);
v_fst_5311_ = lean_ctor_get(v_snd_5309_, 0);
lean_inc(v_fst_5311_);
lean_dec(v_snd_5309_);
v_fst_5312_ = lean_ctor_get(v_snd_5310_, 0);
lean_inc(v_fst_5312_);
lean_dec(v_snd_5310_);
v___x_5313_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5312_);
lean_dec(v_fst_5312_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5326_; 
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; 
v_unused_5327_ = lean_ctor_get(v___x_5313_, 0);
lean_dec(v_unused_5327_);
v___x_5315_ = v___x_5313_;
v_isShared_5316_ = v_isSharedCheck_5326_;
goto v_resetjp_5314_;
}
else
{
lean_dec(v___x_5313_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5326_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
uint8_t v___x_5317_; 
v___x_5317_ = lean_unbox(v_fst_5311_);
lean_dec(v_fst_5311_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; lean_object* v___x_5320_; 
v___x_5318_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5318_);
v___x_5320_ = v___x_5315_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5318_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
else
{
lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5322_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5322_);
v___x_5324_ = v___x_5315_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
lean_dec(v_fst_5311_);
v_a_5328_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5313_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_dec(v___x_5313_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
default: 
{
lean_object* v_snd_5336_; lean_object* v_snd_5337_; lean_object* v_snd_5338_; lean_object* v_fst_5339_; lean_object* v_fst_5340_; lean_object* v___x_5341_; size_t v_sz_5342_; lean_object* v___x_5343_; 
v_snd_5336_ = lean_ctor_get(v_a_5295_, 1);
lean_del_object(v___x_5297_);
v_snd_5337_ = lean_ctor_get(v_snd_5336_, 1);
v_snd_5338_ = lean_ctor_get(v_snd_5337_, 1);
lean_inc(v_snd_5338_);
v_fst_5339_ = lean_ctor_get(v_a_5295_, 0);
lean_inc(v_fst_5339_);
lean_dec(v_a_5295_);
v_fst_5340_ = lean_ctor_get(v_snd_5338_, 0);
lean_inc(v_fst_5340_);
lean_dec(v_snd_5338_);
v___x_5341_ = lean_box(0);
v_sz_5342_ = lean_array_size(v_fst_5340_);
v___x_5343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5340_, v_sz_5342_, v___x_5283_, v___x_5341_);
lean_dec(v_fst_5340_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5356_; 
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v___x_5343_, 0);
lean_dec(v_unused_5357_);
v___x_5345_ = v___x_5343_;
v_isShared_5346_ = v_isSharedCheck_5356_;
goto v_resetjp_5344_;
}
else
{
lean_dec(v___x_5343_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5356_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
uint8_t v___x_5347_; 
v___x_5347_ = lean_unbox(v_fst_5339_);
lean_dec(v_fst_5339_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; lean_object* v___x_5350_; 
v___x_5348_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5348_);
v___x_5350_ = v___x_5345_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
else
{
lean_object* v___x_5352_; lean_object* v___x_5354_; 
v___x_5352_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5352_);
v___x_5354_ = v___x_5345_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5352_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec(v_fst_5339_);
v_a_5358_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5343_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5343_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
v_a_5367_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5294_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5294_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
else
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
lean_dec_ref(v_checkImports_5284_);
lean_dec_ref(v_mods_5275_);
lean_dec_ref(v_args_5273_);
v_a_5375_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5377_ = v___x_5285_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5285_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
else
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
lean_dec_ref(v_mods_5275_);
lean_dec_ref(v_args_5273_);
v___x_5383_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5384_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5383_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5392_; 
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5392_ == 0)
{
lean_object* v_unused_5393_; 
v_unused_5393_ = lean_ctor_get(v___x_5384_, 0);
lean_dec(v_unused_5393_);
v___x_5386_ = v___x_5384_;
v_isShared_5387_ = v_isSharedCheck_5392_;
goto v_resetjp_5385_;
}
else
{
lean_dec(v___x_5384_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5392_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5388_; lean_object* v___x_5390_; 
v___x_5388_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 0, v___x_5388_);
v___x_5390_ = v___x_5386_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5388_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
v_a_5394_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5384_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5384_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Lake_BuiltinLint_run(v_args_5402_);
return v_res_5404_;
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
