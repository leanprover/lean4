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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_env_1752_; lean_object* v___x_1753_; lean_object* v_env_1754_; lean_object* v___x_1755_; lean_object* v_toEnvExtension_1756_; lean_object* v_asyncMode_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1750_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1751_ = lean_st_ref_get(v___y_1748_);
v_env_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_env_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = lean_st_ref_get(v___y_1748_);
v_env_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_env_1754_);
lean_dec(v___x_1753_);
v___x_1755_ = l_Lean_declRangeExt;
v_toEnvExtension_1756_ = lean_ctor_get(v___x_1755_, 0);
v_asyncMode_1757_ = lean_ctor_get(v_toEnvExtension_1756_, 2);
v___x_1758_ = 0;
lean_inc(v_declName_1747_);
v___x_1759_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1750_, v___x_1755_, v_env_1752_, v_declName_1747_, v_asyncMode_1757_, v___x_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = 1;
v___x_1761_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1750_, v___x_1755_, v_env_1754_, v_declName_1747_, v_asyncMode_1757_, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; 
lean_dec_ref(v_env_1754_);
lean_dec(v_declName_1747_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1759_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1764_, v___y_1765_);
lean_dec(v___y_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(lean_object* v_declName_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v_env_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1771_ = lean_st_ref_get(v___y_1769_);
v_env_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref(v_env_1772_);
lean_dec(v___x_1771_);
v___x_1773_ = l_Lean_isRecCore(v_env_1772_, v_declName_1768_);
v___x_1774_ = lean_box(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1776_, v___y_1777_);
lean_dec(v___y_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(lean_object* v_declName_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_ranges_1785_; lean_object* v___x_1791_; lean_object* v_env_1792_; lean_object* v___x_1793_; lean_object* v_a_1794_; uint8_t v___x_1799_; 
v___x_1791_ = lean_st_ref_get(v___y_1782_);
v_env_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc_ref_n(v_env_1792_, 2);
lean_dec(v___x_1791_);
lean_inc_n(v_declName_1780_, 2);
v___x_1793_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1780_, v___y_1782_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
v___x_1799_ = l_Lean_isAuxRecursor(v_env_1792_, v_declName_1780_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
lean_inc(v_declName_1780_);
v___x_1800_ = l_Lean_isNoConfusion(v_env_1792_, v_declName_1780_);
if (v___x_1800_ == 0)
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_unbox(v_a_1794_);
lean_dec(v_a_1794_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v_a_1803_; 
lean_inc(v_declName_1780_);
v___x_1802_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1780_, v___y_1782_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v_ranges_1785_ = v_a_1803_;
goto v___jp_1784_;
}
else
{
goto v___jp_1795_;
}
}
else
{
lean_dec(v_a_1794_);
goto v___jp_1795_;
}
}
else
{
lean_dec(v_a_1794_);
lean_dec_ref(v_env_1792_);
goto v___jp_1795_;
}
v___jp_1784_:
{
if (lean_obj_tag(v_ranges_1785_) == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = l_Lean_builtinDeclRanges;
v___x_1787_ = lean_st_ref_get(v___x_1786_);
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1787_, v_declName_1780_);
lean_dec(v_declName_1780_);
lean_dec(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; 
lean_dec(v_declName_1780_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_ranges_1785_);
return v___x_1790_;
}
}
v___jp_1795_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_a_1798_; 
v___x_1796_ = l_Lean_Name_getPrefix(v_declName_1780_);
v___x_1797_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v___x_1796_, v___y_1782_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v_ranges_1785_ = v_a_1798_;
goto v___jp_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0___boxed(lean_object* v_declName_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_declName_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(lean_object* v_failMod_1809_, lean_object* v_site_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
if (lean_obj_tag(v_site_1810_) == 0)
{
lean_object* v_name_1814_; lean_object* v___x_1815_; 
v_name_1814_ = lean_ctor_get(v_site_1810_, 0);
lean_inc(v_name_1814_);
lean_dec_ref_known(v_site_1810_, 1);
v___x_1815_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_name_1814_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1837_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1837_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1837_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_a_1816_) == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1836_; 
v_val_1824_ = lean_ctor_get(v_a_1816_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_a_1816_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1826_ = v_a_1816_;
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_val_1824_);
lean_dec(v_a_1816_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_range_1828_; lean_object* v_pos_1829_; lean_object* v___x_1831_; 
v_range_1828_ = lean_ctor_get(v_val_1824_, 0);
lean_inc_ref(v_range_1828_);
lean_dec(v_val_1824_);
v_pos_1829_ = lean_ctor_get(v_range_1828_, 0);
lean_inc_ref(v_pos_1829_);
lean_dec_ref(v_range_1828_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_pos_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_pos_1829_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1831_);
v___x_1833_ = v___x_1818_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1815_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1815_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_n_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1877_; 
v_n_1846_ = lean_ctor_get(v_site_1810_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_site_1810_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1848_ = v_site_1810_;
v_isShared_1849_ = v_isSharedCheck_1877_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_n_1846_);
lean_dec(v_site_1810_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1877_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v_env_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_st_ref_get(v_a_1812_);
v_env_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc_ref(v_env_1851_);
lean_dec(v___x_1850_);
v___x_1852_ = l_Lean_getVersoModuleDoc_x3f(v_env_1851_, v_failMod_1809_);
lean_dec_ref(v_env_1851_);
if (lean_obj_tag(v___x_1852_) == 1)
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1872_; 
v_val_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1872_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1872_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_array_get_size(v_val_1853_);
v___x_1858_ = lean_nat_dec_lt(v_n_1846_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_del_object(v___x_1855_);
lean_dec(v_val_1853_);
lean_dec(v_n_1846_);
v___x_1859_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1859_);
v___x_1861_ = v___x_1848_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v_declarationRange_1864_; lean_object* v_pos_1865_; lean_object* v___x_1867_; 
v___x_1863_ = lean_array_fget(v_val_1853_, v_n_1846_);
lean_dec(v_n_1846_);
lean_dec(v_val_1853_);
v_declarationRange_1864_ = lean_ctor_get(v___x_1863_, 2);
lean_inc_ref(v_declarationRange_1864_);
lean_dec(v___x_1863_);
v_pos_1865_ = lean_ctor_get(v_declarationRange_1864_, 0);
lean_inc_ref(v_pos_1865_);
lean_dec_ref(v_declarationRange_1864_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_pos_1865_);
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_pos_1865_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1867_);
v___x_1869_ = v___x_1848_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec(v___x_1852_);
lean_dec(v_n_1846_);
v___x_1873_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1873_);
v___x_1875_ = v___x_1848_;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f___boxed(lean_object* v_failMod_1878_, lean_object* v_site_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_failMod_1878_, v_site_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_failMod_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(lean_object* v_declName_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___redArg(v_declName_1884_, v___y_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0___boxed(lean_object* v_declName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__0(v_declName_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(lean_object* v_declName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___redArg(v_declName_1894_, v___y_1896_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1___boxed(lean_object* v_declName_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0_spec__1(v_declName_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(lean_object* v_x_1907_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
lean_object* v_name_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_name_1908_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_name_1908_);
lean_dec_ref_known(v_x_1907_, 1);
v___x_1909_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__0));
v___x_1910_ = 1;
v___x_1911_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1908_, v___x_1910_);
v___x_1912_ = lean_string_append(v___x_1909_, v___x_1911_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
return v___x_1914_;
}
else
{
lean_object* v_n_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_n_1915_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_n_1915_);
lean_dec_ref_known(v_x_1907_, 1);
v___x_1916_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__2));
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_add(v_n_1915_, v___x_1917_);
lean_dec(v_n_1915_);
v___x_1919_ = l_Nat_reprFast(v___x_1918_);
v___x_1920_ = lean_string_append(v___x_1916_, v___x_1919_);
lean_dec_ref(v___x_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(lean_object* v_o_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_env_1926_; lean_object* v___x_1927_; lean_object* v_toEnvExtension_1928_; lean_object* v_asyncMode_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v_merged_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v___x_1924_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1925_ = lean_st_ref_get(v___y_1922_);
v_env_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc_ref(v_env_1926_);
lean_dec(v___x_1925_);
v___x_1927_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1928_ = lean_ctor_get(v___x_1927_, 0);
v_asyncMode_1929_ = lean_ctor_get(v_toEnvExtension_1928_, 2);
v___x_1930_ = lean_box(0);
v___x_1931_ = 0;
v___x_1932_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1924_, v___x_1927_, v_env_1926_, v_asyncMode_1929_, v___x_1930_, v___x_1931_);
v_merged_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1932_, 1);
lean_dec(v_unused_1942_);
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_merged_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_merged_1933_);
lean_ctor_set(v___x_1935_, 0, v_o_1921_);
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_o_1921_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_merged_1933_);
v___x_1938_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg___boxed(lean_object* v_o_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1943_, v___y_1944_);
lean_dec(v___y_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(lean_object* v_o_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_o_1947_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___boxed(lean_object* v_o_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0(v_o_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(lean_object* v_opts_1957_, lean_object* v_opt_1958_){
_start:
{
lean_object* v_name_1959_; lean_object* v_defValue_1960_; lean_object* v_map_1961_; lean_object* v___x_1962_; 
v_name_1959_ = lean_ctor_get(v_opt_1958_, 0);
v_defValue_1960_ = lean_ctor_get(v_opt_1958_, 1);
v_map_1961_ = lean_ctor_get(v_opts_1957_, 0);
v___x_1962_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1961_, v_name_1959_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_inc(v_defValue_1960_);
return v_defValue_1960_;
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1962_, 1);
if (lean_obj_tag(v_val_1963_) == 3)
{
lean_object* v_v_1964_; 
v_v_1964_ = lean_ctor_get(v_val_1963_, 0);
lean_inc(v_v_1964_);
lean_dec_ref_known(v_val_1963_, 1);
return v_v_1964_;
}
else
{
lean_dec(v_val_1963_);
lean_inc(v_defValue_1960_);
return v_defValue_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2___boxed(lean_object* v_opts_1965_, lean_object* v_opt_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v_opts_1965_, v_opt_1966_);
lean_dec_ref(v_opt_1966_);
lean_dec_ref(v_opts_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(lean_object* v_c_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_options_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
v_options_1972_ = lean_ctor_get(v_c_1968_, 6);
lean_inc_ref(v_options_1972_);
lean_dec_ref(v_c_1968_);
v___x_1973_ = l_Lean_Options_toLinterOptions___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__0___redArg(v_options_1972_, v___y_1970_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1978_ = l_Lean_linter_doc_deferred;
v___x_1979_ = l_Lean_Linter_getLinterValue(v___x_1978_, v_a_1974_);
lean_dec(v_a_1974_);
v___x_1980_ = lean_box(v___x_1979_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1980_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0___boxed(lean_object* v_c_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__0(v_c_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(lean_object* v_pkgRoot_1990_, lean_object* v_docCheckedModules_1991_, uint8_t v___y_1992_, lean_object* v_m_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_Name_isPrefixOf(v_pkgRoot_1990_, v_m_1993_);
if (v___x_1994_ == 0)
{
return v___x_1994_;
}
else
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_NameSet_contains(v_docCheckedModules_1991_, v_m_1993_);
if (v___x_1995_ == 0)
{
return v___y_1992_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = 0;
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed(lean_object* v_pkgRoot_1997_, lean_object* v_docCheckedModules_1998_, lean_object* v___y_1999_, lean_object* v_m_2000_){
_start:
{
uint8_t v___y_7541__boxed_2001_; uint8_t v_res_2002_; lean_object* v_r_2003_; 
v___y_7541__boxed_2001_ = lean_unbox(v___y_1999_);
v_res_2002_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1(v_pkgRoot_1997_, v_docCheckedModules_1998_, v___y_7541__boxed_2001_, v_m_2000_);
lean_dec(v_m_2000_);
lean_dec(v_docCheckedModules_1998_);
lean_dec(v_pkgRoot_1997_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(uint8_t v___x_2011_, lean_object* v_sp_2012_, lean_object* v_as_2013_, size_t v_sz_2014_, size_t v_i_2015_, lean_object* v_b_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_a_2021_; uint8_t v_unlocated_2025_; 
v_unlocated_2025_ = lean_usize_dec_lt(v_i_2015_, v_sz_2014_);
if (v_unlocated_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v_sp_2012_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_b_2016_);
return v___x_2026_;
}
else
{
lean_object* v_a_2027_; lean_object* v_snd_2028_; lean_object* v_fst_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2151_; 
v_a_2027_ = lean_array_uget_borrowed(v_as_2013_, v_i_2015_);
v_snd_2028_ = lean_ctor_get(v_a_2027_, 1);
lean_inc(v_snd_2028_);
v_fst_2029_ = lean_ctor_get(v_snd_2028_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_snd_2028_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_snd_2028_, 1);
lean_dec(v_unused_2152_);
v___x_2031_ = v_snd_2028_;
v_isShared_2032_ = v_isSharedCheck_2151_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_fst_2029_);
lean_dec(v_snd_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2151_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fst_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2150_; 
v_fst_2033_ = lean_ctor_get(v_a_2027_, 0);
v_fst_2034_ = lean_ctor_get(v_b_2016_, 0);
v_snd_2035_ = lean_ctor_get(v_b_2016_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_b_2016_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2037_ = v_b_2016_;
v_isShared_2038_ = v_isSharedCheck_2150_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_inc(v_fst_2034_);
lean_dec(v_b_2016_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2150_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_site_2039_; lean_object* v___x_2040_; 
v_site_2039_ = lean_ctor_get(v_fst_2029_, 0);
lean_inc_ref_n(v_site_2039_, 2);
lean_dec(v_fst_2029_);
v___x_2040_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f(v_fst_2033_, v_site_2039_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
if (lean_obj_tag(v_a_2041_) == 0)
{
lean_object* v___x_2042_; lean_object* v_name_2043_; lean_object* v_ref_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_snd_2035_);
v___x_2042_ = l_Lean_linter_doc_deferred;
v_name_2043_ = lean_ctor_get(v___x_2042_, 0);
v_ref_2044_ = lean_ctor_get(v___y_2017_, 2);
lean_inc(v_fst_2033_);
v___x_2045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2033_, v___x_2011_);
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__0));
v___x_2047_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2039_);
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__1));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_string_append(v___x_2050_, v___x_2045_);
lean_dec_ref(v___x_2045_);
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_2053_ = lean_string_append(v___x_2051_, v___x_2052_);
lean_inc(v_name_2043_);
v___x_2054_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2043_, v___x_2011_);
v___x_2055_ = lean_string_append(v___x_2053_, v___x_2054_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2057_ = lean_string_append(v___x_2055_, v___x_2056_);
v___x_2058_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2058_, 1);
lean_del_object(v___x_2031_);
v___x_2059_ = lean_box(v_unlocated_2025_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v___x_2059_);
v___x_2061_ = v___x_2037_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_fst_2034_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
v_a_2021_ = v___x_2061_;
goto v___jp_2020_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2037_);
lean_dec(v_fst_2034_);
lean_dec(v_sp_2012_);
v_a_2063_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2065_ = v___x_2058_;
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2058_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2067_ = lean_io_error_to_string(v_a_2063_);
v___x_2068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
v___x_2069_ = l_Lean_MessageData_ofFormat(v___x_2068_);
lean_inc(v_ref_2044_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2069_);
lean_ctor_set(v___x_2031_, 0, v_ref_2044_);
v___x_2071_ = v___x_2031_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_ref_2044_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2071_);
v___x_2073_ = v___x_2065_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_site_2039_);
v_val_2077_ = lean_ctor_get(v_a_2041_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2079_ = v_a_2041_;
v_isShared_2080_ = v_isSharedCheck_2141_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v_a_2041_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2141_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_ref_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_ref_2081_ = lean_ctor_get(v___y_2017_, 2);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2033_);
lean_inc(v_sp_2012_);
v___x_2083_ = l_Lean_SearchPath_findWithExt(v_sp_2012_, v___x_2082_, v_fst_2033_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
if (lean_obj_tag(v_a_2084_) == 0)
{
lean_object* v___x_2085_; lean_object* v_name_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec(v_val_2077_);
lean_dec(v_snd_2035_);
v___x_2085_ = l_Lean_linter_doc_deferred;
v_name_2086_ = lean_ctor_get(v___x_2085_, 0);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
lean_inc(v_fst_2033_);
v___x_2088_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2033_, v___x_2011_);
v___x_2089_ = lean_string_append(v___x_2087_, v___x_2088_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_2091_ = lean_string_append(v___x_2089_, v___x_2090_);
lean_inc(v_name_2086_);
v___x_2092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2086_, v___x_2011_);
v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_2095_ = lean_string_append(v___x_2093_, v___x_2094_);
v___x_2096_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2095_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
lean_dec_ref_known(v___x_2096_, 1);
lean_del_object(v___x_2079_);
lean_del_object(v___x_2031_);
v___x_2097_ = lean_box(v_unlocated_2025_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v___x_2097_);
v___x_2099_ = v___x_2037_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_fst_2034_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
v_a_2021_ = v___x_2099_;
goto v___jp_2020_;
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2116_; 
lean_del_object(v___x_2037_);
lean_dec(v_fst_2034_);
lean_dec(v_sp_2012_);
v_a_2101_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2103_ = v___x_2096_;
v_isShared_2104_ = v_isSharedCheck_2116_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2096_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2116_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_io_error_to_string(v_a_2101_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 3);
lean_ctor_set(v___x_2079_, 0, v___x_2105_);
v___x_2107_ = v___x_2079_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = l_Lean_MessageData_ofFormat(v___x_2107_);
lean_inc(v_ref_2081_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2108_);
lean_ctor_set(v___x_2031_, 0, v_ref_2081_);
v___x_2110_ = v___x_2031_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_ref_2081_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2110_);
v___x_2112_ = v___x_2103_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
}
else
{
lean_object* v_val_2117_; lean_object* v___x_2118_; lean_object* v_name_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_del_object(v___x_2079_);
lean_del_object(v___x_2031_);
v_val_2117_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v_a_2084_, 1);
v___x_2118_ = l_Lean_linter_doc_deferred;
v_name_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_name_2119_);
v___x_2120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2120_, 0, v_val_2117_);
lean_ctor_set(v___x_2120_, 1, v_val_2077_);
lean_ctor_set(v___x_2120_, 2, v_name_2119_);
v___x_2121_ = lean_array_push(v_fst_2034_, v___x_2120_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2121_);
v___x_2123_ = v___x_2037_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_snd_2035_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
v_a_2021_ = v___x_2123_;
goto v___jp_2020_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_val_2077_);
lean_del_object(v___x_2037_);
lean_dec(v_snd_2035_);
lean_dec(v_fst_2034_);
lean_dec(v_sp_2012_);
v_a_2125_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2127_ = v___x_2083_;
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2083_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2140_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_io_error_to_string(v_a_2125_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 3);
lean_ctor_set(v___x_2079_, 0, v___x_2129_);
v___x_2131_ = v___x_2079_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_MessageData_ofFormat(v___x_2131_);
lean_inc(v_ref_2081_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2132_);
lean_ctor_set(v___x_2031_, 0, v_ref_2081_);
v___x_2134_ = v___x_2031_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_ref_2081_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2134_);
v___x_2136_ = v___x_2127_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
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
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_site_2039_);
lean_del_object(v___x_2037_);
lean_dec(v_snd_2035_);
lean_dec(v_fst_2034_);
lean_del_object(v___x_2031_);
lean_dec(v_sp_2012_);
v_a_2142_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2040_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2040_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
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
v___jp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; 
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2015_, v___x_2022_);
v_i_2015_ = v___x_2023_;
v_b_2016_ = v_a_2021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___boxed(lean_object* v___x_2153_, lean_object* v_sp_2154_, lean_object* v_as_2155_, lean_object* v_sz_2156_, lean_object* v_i_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v___x_7565__boxed_2162_; size_t v_sz_boxed_2163_; size_t v_i_boxed_2164_; lean_object* v_res_2165_; 
v___x_7565__boxed_2162_ = lean_unbox(v___x_2153_);
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2156_);
lean_dec(v_sz_2156_);
v_i_boxed_2164_ = lean_unbox_usize(v_i_2157_);
lean_dec(v_i_2157_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_7565__boxed_2162_, v_sp_2154_, v_as_2155_, v_sz_boxed_2163_, v_i_boxed_2164_, v_b_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_as_2155_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(lean_object* v_sp_2172_, uint8_t v___y_2173_, lean_object* v_as_2174_, size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_a_2181_; uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_sp_2172_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_b_2177_);
return v___x_2186_;
}
else
{
lean_object* v_a_2187_; lean_object* v_snd_2188_; lean_object* v_fst_2189_; lean_object* v_fst_2190_; lean_object* v_snd_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2284_; 
v_a_2187_ = lean_array_uget_borrowed(v_as_2174_, v_i_2176_);
v_snd_2188_ = lean_ctor_get(v_a_2187_, 1);
lean_inc(v_snd_2188_);
v_fst_2189_ = lean_ctor_get(v_snd_2188_, 0);
lean_inc(v_fst_2189_);
v_fst_2190_ = lean_ctor_get(v_a_2187_, 0);
v_snd_2191_ = lean_ctor_get(v_snd_2188_, 1);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_snd_2188_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_snd_2188_, 0);
lean_dec(v_unused_2285_);
v___x_2193_ = v_snd_2188_;
v_isShared_2194_ = v_isSharedCheck_2284_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snd_2191_);
lean_dec(v_snd_2188_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2284_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_site_2195_; lean_object* v_sourceString_2196_; lean_object* v___x_2197_; lean_object* v___y_2199_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_site_2195_ = lean_ctor_get(v_fst_2189_, 0);
lean_inc_ref(v_site_2195_);
v_sourceString_2196_ = lean_ctor_get(v_fst_2189_, 2);
lean_inc_ref(v_sourceString_2196_);
lean_dec(v_fst_2189_);
v___x_2197_ = lean_box(0);
v___x_2276_ = lean_string_utf8_byte_size(v_sourceString_2196_);
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = lean_nat_dec_eq(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__4));
v___x_2280_ = lean_string_append(v___x_2279_, v_sourceString_2196_);
lean_dec_ref(v_sourceString_2196_);
v___x_2281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__5));
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
v___y_2199_ = v___x_2282_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2283_; 
lean_dec_ref(v_sourceString_2196_);
v___x_2283_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___y_2199_ = v___x_2283_;
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v_ref_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_ref_2200_ = lean_ctor_get(v___y_2178_, 2);
v___x_2201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v_fst_2190_);
lean_inc(v_sp_2172_);
v___x_2202_ = l_Lean_SearchPath_findWithExt(v_sp_2172_, v___x_2201_, v_fst_2190_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
if (lean_obj_tag(v_a_2203_) == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2204_ = l_Lean_MessageData_toString(v_snd_2191_);
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__0));
lean_inc(v_fst_2190_);
v___x_2206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2190_, v___y_2173_);
v___x_2207_ = lean_string_append(v___x_2205_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__1));
v___x_2209_ = lean_string_append(v___x_2207_, v___x_2208_);
v___x_2210_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2195_);
v___x_2211_ = lean_string_append(v___x_2209_, v___x_2210_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = lean_string_append(v___x_2211_, v___y_2199_);
lean_dec_ref(v___y_2199_);
v___x_2213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2214_ = lean_string_append(v___x_2212_, v___x_2213_);
v___x_2215_ = lean_string_append(v___x_2214_, v___x_2204_);
lean_dec_ref(v___x_2204_);
v___x_2216_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref_known(v___x_2216_, 1);
lean_del_object(v___x_2193_);
v_a_2181_ = v___x_2197_;
goto v___jp_2180_;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_sp_2172_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2230_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2230_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2221_ = lean_io_error_to_string(v_a_2217_);
v___x_2222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
v___x_2223_ = l_Lean_MessageData_ofFormat(v___x_2222_);
lean_inc(v_ref_2200_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v___x_2223_);
lean_ctor_set(v___x_2193_, 0, v_ref_2200_);
v___x_2225_ = v___x_2193_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_ref_2200_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2225_);
v___x_2227_ = v___x_2219_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v_val_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2261_; 
v_val_2231_ = lean_ctor_get(v_a_2203_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2203_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2233_ = v_a_2203_;
v_isShared_2234_ = v_isSharedCheck_2261_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_val_2231_);
lean_dec(v_a_2203_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2261_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2235_ = l_Lean_MessageData_toString(v_snd_2191_);
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__3));
v___x_2237_ = lean_string_append(v_val_2231_, v___x_2236_);
v___x_2238_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite(v_site_2195_);
v___x_2239_ = lean_string_append(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_string_append(v___x_2239_, v___y_2199_);
lean_dec_ref(v___y_2199_);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___closed__2));
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2242_, v___x_2235_);
lean_dec_ref(v___x_2235_);
v___x_2244_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_dec_ref_known(v___x_2244_, 1);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2193_);
v_a_2181_ = v___x_2197_;
goto v___jp_2180_;
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_sp_2172_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_io_error_to_string(v_a_2245_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 3);
lean_ctor_set(v___x_2233_, 0, v___x_2249_);
v___x_2251_ = v___x_2233_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2252_ = l_Lean_MessageData_ofFormat(v___x_2251_);
lean_inc(v_ref_2200_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v___x_2252_);
lean_ctor_set(v___x_2193_, 0, v_ref_2200_);
v___x_2254_ = v___x_2193_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_ref_2200_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2254_);
v___x_2256_ = v___x_2247_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
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
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_site_2195_);
lean_dec(v_snd_2191_);
lean_dec(v_sp_2172_);
v_a_2262_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2264_ = v___x_2202_;
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2202_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2266_ = lean_io_error_to_string(v_a_2262_);
v___x_2267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___x_2268_ = l_Lean_MessageData_ofFormat(v___x_2267_);
lean_inc(v_ref_2200_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 1, v___x_2268_);
lean_ctor_set(v___x_2193_, 0, v_ref_2200_);
v___x_2270_ = v___x_2193_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_ref_2200_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2270_);
v___x_2272_ = v___x_2264_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
}
v___jp_2180_:
{
size_t v___x_2182_; size_t v___x_2183_; 
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_add(v_i_2176_, v___x_2182_);
v_i_2176_ = v___x_2183_;
v_b_2177_ = v_a_2181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg___boxed(lean_object* v_sp_2286_, lean_object* v___y_2287_, lean_object* v_as_2288_, lean_object* v_sz_2289_, lean_object* v_i_2290_, lean_object* v_b_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v___y_7847__boxed_2294_; size_t v_sz_boxed_2295_; size_t v_i_boxed_2296_; lean_object* v_res_2297_; 
v___y_7847__boxed_2294_ = lean_unbox(v___y_2287_);
v_sz_boxed_2295_ = lean_unbox_usize(v_sz_2289_);
lean_dec(v_sz_2289_);
v_i_boxed_2296_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_res_2297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2286_, v___y_7847__boxed_2294_, v_as_2288_, v_sz_boxed_2295_, v_i_boxed_2296_, v_b_2291_, v___y_2292_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v_as_2288_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(lean_object* v_pkgRoot_2298_, lean_object* v_as_2299_, size_t v_sz_2300_, size_t v_i_2301_, lean_object* v_b_2302_){
_start:
{
lean_object* v_a_2305_; uint8_t v___x_2309_; 
v___x_2309_ = lean_usize_dec_lt(v_i_2301_, v_sz_2300_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v_b_2302_);
return v___x_2310_;
}
else
{
lean_object* v_a_2311_; uint8_t v___x_2312_; 
v_a_2311_ = lean_array_uget_borrowed(v_as_2299_, v_i_2301_);
v___x_2312_ = l_Lean_Name_isPrefixOf(v_pkgRoot_2298_, v_a_2311_);
if (v___x_2312_ == 0)
{
v_a_2305_ = v_b_2302_;
goto v___jp_2304_;
}
else
{
lean_object* v___x_2313_; 
lean_inc(v_a_2311_);
v___x_2313_ = l_Lean_NameSet_insert(v_b_2302_, v_a_2311_);
v_a_2305_ = v___x_2313_;
goto v___jp_2304_;
}
}
v___jp_2304_:
{
size_t v___x_2306_; size_t v___x_2307_; 
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_add(v_i_2301_, v___x_2306_);
v_i_2301_ = v___x_2307_;
v_b_2302_ = v_a_2305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1___boxed(lean_object* v_pkgRoot_2314_, lean_object* v_as_2315_, lean_object* v_sz_2316_, lean_object* v_i_2317_, lean_object* v_b_2318_, lean_object* v___y_2319_){
_start:
{
size_t v_sz_boxed_2320_; size_t v_i_boxed_2321_; lean_object* v_res_2322_; 
v_sz_boxed_2320_ = lean_unbox_usize(v_sz_2316_);
lean_dec(v_sz_2316_);
v_i_boxed_2321_ = lean_unbox_usize(v_i_2317_);
lean_dec(v_i_2317_);
v_res_2322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2314_, v_as_2315_, v_sz_boxed_2320_, v_i_boxed_2321_, v_b_2318_);
lean_dec_ref(v_as_2315_);
lean_dec(v_pkgRoot_2314_);
return v_res_2322_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = l_Lean_Options_empty;
v___x_2330_ = l_Lean_Core_getMaxHeartbeats(v___x_2329_);
return v___x_2330_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6(void){
_start:
{
lean_object* v___x_2331_; uint16_t v___x_2332_; 
v___x_2331_ = l_Lean_Options_empty;
v___x_2332_ = l_Lean_OptionFlags_ofOptions(v___x_2331_);
return v___x_2332_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = l_Lean_firstFrontendMacroScope;
v___x_2335_ = lean_nat_add(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_unsigned_to_nat(32u);
v___x_2347_ = lean_mk_empty_array_with_capacity(v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13(void){
_start:
{
size_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = ((size_t)5ULL);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = lean_unsigned_to_nat(32u);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2351_);
v___x_2353_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__12);
v___x_2354_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2352_);
lean_ctor_set(v___x_2354_, 2, v___x_2350_);
lean_ctor_set(v___x_2354_, 3, v___x_2350_);
lean_ctor_set_usize(v___x_2354_, 4, v___x_2349_);
return v___x_2354_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14(void){
_start:
{
lean_object* v___x_2355_; uint64_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2356_ = 0ULL;
v___x_2357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set_uint64(v___x_2357_, sizeof(void*)*1, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15(void){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2358_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = l_Lean_Options_empty;
v___x_2365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2366_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v___x_2364_);
lean_ctor_set(v___x_2366_, 2, v___x_2365_);
lean_ctor_set(v___x_2366_, 3, v___x_2363_);
lean_ctor_set(v___x_2366_, 4, v___x_2363_);
lean_ctor_set(v___x_2366_, 5, v___x_2363_);
return v___x_2366_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = l_Lean_NameSet_empty;
v___x_2368_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
lean_ctor_set(v___x_2369_, 2, v___x_2367_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v_unlocated_2372_; lean_object* v___x_2373_; 
v___x_2370_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__13);
v___x_2371_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__16);
v_unlocated_2372_ = 1;
v___x_2373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2371_);
lean_ctor_set(v___x_2373_, 2, v___x_2370_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*3, v_unlocated_2372_);
return v___x_2373_;
}
}
static uint16_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21(void){
_start:
{
uint16_t v___x_2374_; uint16_t v___x_2375_; uint16_t v___x_2376_; 
v___x_2374_ = 512;
v___x_2375_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2376_ = lean_uint16_land(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static uint8_t _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22(void){
_start:
{
uint16_t v___x_2377_; uint16_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2377_ = 0;
v___x_2378_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__21);
v___x_2379_ = lean_uint16_dec_eq(v___x_2378_, v___x_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(lean_object* v_args_2380_, lean_object* v_linterOpts_2381_, lean_object* v_sp_2382_, lean_object* v_env_2383_, lean_object* v_pkgRoot_2384_, lean_object* v_docCheckedModules_2385_){
_start:
{
lean_object* v___y_2388_; lean_object* v_a_2392_; uint8_t v___y_2396_; lean_object* v_a_2397_; lean_object* v___y_2414_; lean_object* v_a_2415_; lean_object* v___y_2440_; uint8_t v___y_2441_; uint8_t v_lintOnly_2443_; uint8_t v_mode_2444_; lean_object* v___f_2445_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2450_; uint8_t v___y_2451_; uint16_t v___y_2452_; lean_object* v___y_2453_; lean_object* v_fileName_2454_; lean_object* v_fileMap_2455_; lean_object* v_currNamespace_2456_; lean_object* v_openDecls_2457_; lean_object* v_initHeartbeats_2458_; lean_object* v_maxHeartbeats_2459_; lean_object* v_quotContext_2460_; lean_object* v_currMacroScope_2461_; lean_object* v_cancelTk_x3f_2462_; lean_object* v_inheritedTraceOptions_2463_; lean_object* v_currRecDepth_2464_; lean_object* v_ref_2465_; uint8_t v_suppressElabErrors_2466_; uint8_t v_checkDeprecated_2467_; uint8_t v_isRecordingDeps_2468_; lean_object* v___y_2469_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; uint16_t v___y_2506_; uint8_t v___y_2507_; lean_object* v___y_2508_; uint8_t v___y_2546_; 
v_lintOnly_2443_ = lean_ctor_get_uint8(v_args_2380_, sizeof(void*)*4);
v_mode_2444_ = lean_ctor_get_uint8(v_args_2380_, sizeof(void*)*4 + 1);
v___f_2445_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__3));
if (v_lintOnly_2443_ == 0)
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = l_Lean_linter_doc_deferred;
v___x_2589_ = l_Lean_Linter_getLinterValue(v___x_2588_, v_linterOpts_2381_);
v___y_2546_ = v___x_2589_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2590_; lean_object* v_name_2591_; uint8_t v___x_2592_; 
v___x_2590_ = l_Lean_linter_doc_deferred;
v_name_2591_ = lean_ctor_get(v___x_2590_, 0);
v___x_2592_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_2591_, v_linterOpts_2381_);
v___y_2546_ = v___x_2592_;
goto v___jp_2545_;
}
v___jp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2388_);
lean_ctor_set(v___x_2389_, 1, v_docCheckedModules_2385_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_mk_io_user_error(v_a_2392_);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
v___jp_2395_:
{
if (lean_obj_tag(v_a_2397_) == 0)
{
lean_object* v_msg_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_msg_2398_ = lean_ctor_get(v_a_2397_, 1);
lean_inc_ref(v_msg_2398_);
lean_dec_ref_known(v_a_2397_, 2);
v___x_2399_ = l_Lean_MessageData_toString(v_msg_2398_);
v___x_2400_ = lean_mk_io_user_error(v___x_2399_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
else
{
lean_object* v_id_2402_; lean_object* v___x_2403_; 
v_id_2402_ = lean_ctor_get(v_a_2397_, 0);
lean_inc(v_id_2402_);
lean_dec_ref_known(v_a_2397_, 2);
v___x_2403_ = l_Lean_InternalExceptionId_getName(v_id_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_id_2402_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_2406_ = l_Lean_Name_toString(v_a_2404_, v___y_2396_);
v___x_2407_ = lean_string_append(v___x_2405_, v___x_2406_);
lean_dec_ref(v___x_2406_);
v_a_2392_ = v___x_2407_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref_known(v___x_2403_, 1);
v___x_2408_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_2409_ = l_Nat_reprFast(v_id_2402_);
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_2412_ = lean_string_append(v___x_2410_, v___x_2411_);
v_a_2392_ = v___x_2412_;
goto v___jp_2391_;
}
}
}
v___jp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_moduleNames_2418_; size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2416_ = lean_st_ref_get(v___y_2414_);
lean_dec(v___y_2414_);
lean_dec(v___x_2416_);
v___x_2417_ = l_Lean_Environment_header(v_env_2383_);
lean_dec_ref(v_env_2383_);
v_moduleNames_2418_ = lean_ctor_get(v___x_2417_, 4);
lean_inc_ref(v_moduleNames_2418_);
lean_dec_ref(v___x_2417_);
v_sz_2419_ = lean_array_size(v_moduleNames_2418_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__1(v_pkgRoot_2384_, v_moduleNames_2418_, v_sz_2419_, v___x_2420_, v_docCheckedModules_2385_);
lean_dec_ref(v_moduleNames_2418_);
lean_dec(v_pkgRoot_2384_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v_a_2415_);
lean_ctor_set(v___x_2426_, 1, v_a_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v_a_2415_);
v_a_2431_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2421_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2421_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
v___jp_2439_:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2442_, 0, v___y_2441_);
v___y_2414_ = v___y_2440_;
v_a_2415_ = v___x_2442_;
goto v___jp_2413_;
}
v___jp_2446_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2470_ = l_Lean_maxRecDepth;
v___x_2471_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___y_2447_, v___x_2470_);
lean_inc_ref(v___y_2447_);
v___x_2472_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2472_, 0, v_fileName_2454_);
lean_ctor_set(v___x_2472_, 1, v_fileMap_2455_);
lean_ctor_set(v___x_2472_, 2, v___y_2447_);
lean_ctor_set(v___x_2472_, 3, v___x_2471_);
lean_ctor_set(v___x_2472_, 4, v_currNamespace_2456_);
lean_ctor_set(v___x_2472_, 5, v_openDecls_2457_);
lean_ctor_set(v___x_2472_, 6, v_initHeartbeats_2458_);
lean_ctor_set(v___x_2472_, 7, v_maxHeartbeats_2459_);
lean_ctor_set(v___x_2472_, 8, v_quotContext_2460_);
lean_ctor_set(v___x_2472_, 9, v_currMacroScope_2461_);
lean_ctor_set(v___x_2472_, 10, v_cancelTk_x3f_2462_);
lean_ctor_set(v___x_2472_, 11, v_inheritedTraceOptions_2463_);
v___x_2473_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v_currRecDepth_2464_);
lean_ctor_set(v___x_2473_, 2, v_ref_2465_);
lean_ctor_set_uint16(v___x_2473_, sizeof(void*)*3, v___y_2452_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*3 + 2, v_suppressElabErrors_2466_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*3 + 3, v_checkDeprecated_2467_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*3 + 4, v_isRecordingDeps_2468_);
v___x_2474_ = l_Lean_Doc_DeferredCheck_run(v___y_2448_, v___f_2445_, v___x_2473_, v___y_2469_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; uint8_t v___x_2476_; uint8_t v___x_2477_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = 1;
v___x_2477_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2444_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; size_t v_sz_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___y_2469_);
v___x_2478_ = lean_box(0);
v_sz_2479_ = lean_array_size(v_a_2475_);
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2382_, v___y_2451_, v_a_2475_, v_sz_2479_, v___x_2480_, v___x_2478_, v___x_2473_);
lean_dec_ref_known(v___x_2473_, 3);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
lean_dec_ref_known(v___x_2481_, 1);
v___x_2482_ = lean_array_get_size(v_a_2475_);
lean_dec(v_a_2475_);
v___x_2483_ = lean_nat_dec_eq(v___x_2482_, v___y_2450_);
lean_dec(v___y_2450_);
if (v___x_2483_ == 0)
{
v___y_2440_ = v___y_2453_;
v___y_2441_ = v___y_2451_;
goto v___jp_2439_;
}
else
{
v___y_2440_ = v___y_2453_;
v___y_2441_ = v___x_2477_;
goto v___jp_2439_;
}
}
else
{
lean_object* v_a_2484_; 
lean_dec(v_a_2475_);
lean_dec(v___y_2453_);
lean_dec(v___y_2450_);
lean_dec(v_docCheckedModules_2385_);
lean_dec(v_pkgRoot_2384_);
lean_dec_ref(v_env_2383_);
v_a_2484_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2481_, 1);
v___y_2396_ = v___y_2451_;
v_a_2397_ = v_a_2484_;
goto v___jp_2395_;
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; size_t v_sz_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2485_ = lean_mk_empty_array_with_capacity(v___y_2450_);
lean_dec(v___y_2450_);
v___x_2486_ = lean_box(v___y_2449_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v_sz_2488_ = lean_array_size(v_a_2475_);
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4(v___x_2477_, v_sp_2382_, v_a_2475_, v_sz_2488_, v___x_2489_, v___x_2487_, v___x_2473_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref_known(v___x_2473_, 3);
lean_dec(v_a_2475_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v_fst_2492_ = lean_ctor_get(v_a_2491_, 0);
lean_inc(v_fst_2492_);
v_snd_2493_ = lean_ctor_get(v_a_2491_, 1);
lean_inc(v_snd_2493_);
lean_dec(v_a_2491_);
v___x_2494_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2494_, 0, v_fst_2492_);
v___x_2495_ = lean_unbox(v_snd_2493_);
lean_dec(v_snd_2493_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*1, v___x_2495_);
v___y_2414_ = v___y_2453_;
v_a_2415_ = v___x_2494_;
goto v___jp_2413_;
}
else
{
lean_object* v_a_2496_; 
lean_dec(v___y_2453_);
lean_dec(v_docCheckedModules_2385_);
lean_dec(v_pkgRoot_2384_);
lean_dec_ref(v_env_2383_);
v_a_2496_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2490_, 1);
v___y_2396_ = v___y_2451_;
v_a_2397_ = v_a_2496_;
goto v___jp_2395_;
}
}
}
else
{
lean_object* v_a_2497_; 
lean_dec_ref_known(v___x_2473_, 3);
lean_dec(v___y_2469_);
lean_dec(v___y_2453_);
lean_dec(v___y_2450_);
lean_dec(v_docCheckedModules_2385_);
lean_dec(v_pkgRoot_2384_);
lean_dec_ref(v_env_2383_);
lean_dec(v_sp_2382_);
v_a_2497_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2474_, 1);
v___y_2396_ = v___y_2451_;
v_a_2397_ = v_a_2497_;
goto v___jp_2395_;
}
}
v___jp_2498_:
{
lean_object* v___x_2509_; lean_object* v_env_2510_; lean_object* v_nextMacroScope_2511_; lean_object* v_ngen_2512_; lean_object* v_auxDeclNGen_2513_; lean_object* v_traceState_2514_; lean_object* v_recordedDeps_2515_; lean_object* v_messages_2516_; lean_object* v_infoState_2517_; lean_object* v_snapshotTasks_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2543_; 
v___x_2509_ = lean_st_ref_take(v___y_2508_);
v_env_2510_ = lean_ctor_get(v___x_2509_, 0);
v_nextMacroScope_2511_ = lean_ctor_get(v___x_2509_, 1);
v_ngen_2512_ = lean_ctor_get(v___x_2509_, 2);
v_auxDeclNGen_2513_ = lean_ctor_get(v___x_2509_, 3);
v_traceState_2514_ = lean_ctor_get(v___x_2509_, 4);
v_recordedDeps_2515_ = lean_ctor_get(v___x_2509_, 6);
v_messages_2516_ = lean_ctor_get(v___x_2509_, 7);
v_infoState_2517_ = lean_ctor_get(v___x_2509_, 8);
v_snapshotTasks_2518_ = lean_ctor_get(v___x_2509_, 9);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2509_, 5);
lean_dec(v_unused_2544_);
v___x_2520_ = v___x_2509_;
v_isShared_2521_ = v_isSharedCheck_2543_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_snapshotTasks_2518_);
lean_inc(v_infoState_2517_);
lean_inc(v_messages_2516_);
lean_inc(v_recordedDeps_2515_);
lean_inc(v_traceState_2514_);
lean_inc(v_auxDeclNGen_2513_);
lean_inc(v_ngen_2512_);
lean_inc(v_nextMacroScope_2511_);
lean_inc(v_env_2510_);
lean_dec(v___x_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2543_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = l_Lean_Kernel_enableDiag(v_env_2510_, v___y_2501_);
lean_inc_ref(v___y_2502_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 5, v___y_2502_);
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_nextMacroScope_2511_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_ngen_2512_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_auxDeclNGen_2513_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_traceState_2514_);
lean_ctor_set(v_reuseFailAlloc_2542_, 5, v___y_2502_);
lean_ctor_set(v_reuseFailAlloc_2542_, 6, v_recordedDeps_2515_);
lean_ctor_set(v_reuseFailAlloc_2542_, 7, v_messages_2516_);
lean_ctor_set(v_reuseFailAlloc_2542_, 8, v_infoState_2517_);
lean_ctor_set(v_reuseFailAlloc_2542_, 9, v_snapshotTasks_2518_);
v___x_2524_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v_toCold_2526_; lean_object* v_currRecDepth_2527_; lean_object* v_ref_2528_; uint8_t v_suppressElabErrors_2529_; uint8_t v_checkDeprecated_2530_; uint8_t v_isRecordingDeps_2531_; lean_object* v_fileName_2532_; lean_object* v_fileMap_2533_; lean_object* v_currNamespace_2534_; lean_object* v_openDecls_2535_; lean_object* v_initHeartbeats_2536_; lean_object* v_maxHeartbeats_2537_; lean_object* v_quotContext_2538_; lean_object* v_currMacroScope_2539_; lean_object* v_cancelTk_x3f_2540_; lean_object* v_inheritedTraceOptions_2541_; 
v___x_2525_ = lean_st_ref_put(v___y_2508_, v___x_2524_);
v_toCold_2526_ = lean_ctor_get(v___y_2499_, 0);
lean_inc_ref(v_toCold_2526_);
v_currRecDepth_2527_ = lean_ctor_get(v___y_2499_, 1);
lean_inc(v_currRecDepth_2527_);
v_ref_2528_ = lean_ctor_get(v___y_2499_, 2);
lean_inc(v_ref_2528_);
v_suppressElabErrors_2529_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 2);
v_checkDeprecated_2530_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2531_ = lean_ctor_get_uint8(v___y_2499_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_2499_);
v_fileName_2532_ = lean_ctor_get(v_toCold_2526_, 0);
lean_inc_ref(v_fileName_2532_);
v_fileMap_2533_ = lean_ctor_get(v_toCold_2526_, 1);
lean_inc_ref(v_fileMap_2533_);
v_currNamespace_2534_ = lean_ctor_get(v_toCold_2526_, 4);
lean_inc(v_currNamespace_2534_);
v_openDecls_2535_ = lean_ctor_get(v_toCold_2526_, 5);
lean_inc(v_openDecls_2535_);
v_initHeartbeats_2536_ = lean_ctor_get(v_toCold_2526_, 6);
lean_inc(v_initHeartbeats_2536_);
v_maxHeartbeats_2537_ = lean_ctor_get(v_toCold_2526_, 7);
lean_inc(v_maxHeartbeats_2537_);
v_quotContext_2538_ = lean_ctor_get(v_toCold_2526_, 8);
lean_inc(v_quotContext_2538_);
v_currMacroScope_2539_ = lean_ctor_get(v_toCold_2526_, 9);
lean_inc(v_currMacroScope_2539_);
v_cancelTk_x3f_2540_ = lean_ctor_get(v_toCold_2526_, 10);
lean_inc(v_cancelTk_x3f_2540_);
v_inheritedTraceOptions_2541_ = lean_ctor_get(v_toCold_2526_, 11);
lean_inc_ref(v_inheritedTraceOptions_2541_);
lean_dec_ref(v_toCold_2526_);
lean_inc(v___y_2508_);
v___y_2447_ = v___y_2500_;
v___y_2448_ = v___y_2503_;
v___y_2449_ = v___y_2504_;
v___y_2450_ = v___y_2505_;
v___y_2451_ = v___y_2507_;
v___y_2452_ = v___y_2506_;
v___y_2453_ = v___y_2508_;
v_fileName_2454_ = v_fileName_2532_;
v_fileMap_2455_ = v_fileMap_2533_;
v_currNamespace_2456_ = v_currNamespace_2534_;
v_openDecls_2457_ = v_openDecls_2535_;
v_initHeartbeats_2458_ = v_initHeartbeats_2536_;
v_maxHeartbeats_2459_ = v_maxHeartbeats_2537_;
v_quotContext_2460_ = v_quotContext_2538_;
v_currMacroScope_2461_ = v_currMacroScope_2539_;
v_cancelTk_x3f_2462_ = v_cancelTk_x3f_2540_;
v_inheritedTraceOptions_2463_ = v_inheritedTraceOptions_2541_;
v_currRecDepth_2464_ = v_currRecDepth_2527_;
v_ref_2465_ = v_ref_2528_;
v_suppressElabErrors_2466_ = v_suppressElabErrors_2529_;
v_checkDeprecated_2467_ = v_checkDeprecated_2530_;
v_isRecordingDeps_2468_ = v_isRecordingDeps_2531_;
v___y_2469_ = v___y_2508_;
goto v___jp_2446_;
}
}
}
v___jp_2545_:
{
if (v___y_2546_ == 0)
{
uint8_t v___x_2547_; uint8_t v___x_2548_; 
lean_dec(v_pkgRoot_2384_);
lean_dec_ref(v_env_2383_);
lean_dec(v_sp_2382_);
v___x_2547_ = 1;
v___x_2548_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_2444_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2549_, 0, v___x_2548_);
v___y_2388_ = v___x_2549_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_2551_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set_uint8(v___x_2551_, sizeof(void*)*1, v___y_2546_);
v___y_2388_ = v___x_2551_;
goto v___jp_2387_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint16_t v___x_2565_; uint8_t v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_env_2585_; uint8_t v___x_2586_; uint8_t v___x_2587_; 
v___x_2552_ = lean_box(v___y_2546_);
lean_inc(v_docCheckedModules_2385_);
lean_inc(v_pkgRoot_2384_);
v___f_2553_ = lean_alloc_closure((void*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2553_, 0, v_pkgRoot_2384_);
lean_closure_set(v___f_2553_, 1, v_docCheckedModules_2385_);
lean_closure_set(v___f_2553_, 2, v___x_2552_);
v___x_2554_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_2555_ = l_Lean_instInhabitedFileMap_default;
v___x_2556_ = l_Lean_Options_empty;
v___x_2557_ = lean_unsigned_to_nat(1000u);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_2562_ = l_Lean_firstFrontendMacroScope;
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_2566_ = 0;
v___x_2567_ = 0;
v___x_2568_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_2569_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_2570_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_2571_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_2572_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_2573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_2574_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_2575_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_2576_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
lean_inc_ref(v_env_2383_);
v___x_2577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2577_, 0, v_env_2383_);
lean_ctor_set(v___x_2577_, 1, v___x_2568_);
lean_ctor_set(v___x_2577_, 2, v___x_2569_);
lean_ctor_set(v___x_2577_, 3, v___x_2570_);
lean_ctor_set(v___x_2577_, 4, v___x_2571_);
lean_ctor_set(v___x_2577_, 5, v___x_2572_);
lean_ctor_set(v___x_2577_, 6, v___x_2574_);
lean_ctor_set(v___x_2577_, 7, v___x_2575_);
lean_ctor_set(v___x_2577_, 8, v___x_2576_);
lean_ctor_set(v___x_2577_, 9, v___x_2573_);
v___x_2578_ = lean_io_get_num_heartbeats();
v___x_2579_ = lean_st_mk_ref(v___x_2577_);
v___x_2580_ = l_Lean_inheritedTraceOptions;
v___x_2581_ = lean_st_ref_get(v___x_2580_);
lean_inc(v___x_2581_);
lean_inc(v___x_2578_);
v___x_2582_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2554_);
lean_ctor_set(v___x_2582_, 1, v___x_2555_);
lean_ctor_set(v___x_2582_, 2, v___x_2556_);
lean_ctor_set(v___x_2582_, 3, v___x_2557_);
lean_ctor_set(v___x_2582_, 4, v___x_2558_);
lean_ctor_set(v___x_2582_, 5, v___x_2559_);
lean_ctor_set(v___x_2582_, 6, v___x_2578_);
lean_ctor_set(v___x_2582_, 7, v___x_2561_);
lean_ctor_set(v___x_2582_, 8, v___x_2558_);
lean_ctor_set(v___x_2582_, 9, v___x_2562_);
lean_ctor_set(v___x_2582_, 10, v___x_2563_);
lean_ctor_set(v___x_2582_, 11, v___x_2581_);
v___x_2583_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___x_2560_);
lean_ctor_set(v___x_2583_, 2, v___x_2564_);
lean_ctor_set_uint16(v___x_2583_, sizeof(void*)*3, v___x_2565_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3 + 2, v___x_2566_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3 + 3, v___x_2567_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3 + 4, v___x_2566_);
v___x_2584_ = lean_st_ref_get(v___x_2579_);
v_env_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_ref(v_env_2585_);
lean_dec(v___x_2584_);
v___x_2586_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2585_);
lean_dec_ref(v_env_2585_);
v___x_2587_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_2587_ == 0)
{
if (v___x_2586_ == 0)
{
lean_dec(v___x_2581_);
lean_dec(v___x_2578_);
v___y_2499_ = v___x_2583_;
v___y_2500_ = v___x_2556_;
v___y_2501_ = v___y_2546_;
v___y_2502_ = v___x_2572_;
v___y_2503_ = v___f_2553_;
v___y_2504_ = v___x_2566_;
v___y_2505_ = v___x_2560_;
v___y_2506_ = v___x_2565_;
v___y_2507_ = v___y_2546_;
v___y_2508_ = v___x_2579_;
goto v___jp_2498_;
}
else
{
lean_dec_ref_known(v___x_2583_, 3);
lean_inc(v___x_2579_);
v___y_2447_ = v___x_2556_;
v___y_2448_ = v___f_2553_;
v___y_2449_ = v___x_2566_;
v___y_2450_ = v___x_2560_;
v___y_2451_ = v___y_2546_;
v___y_2452_ = v___x_2565_;
v___y_2453_ = v___x_2579_;
v_fileName_2454_ = v___x_2554_;
v_fileMap_2455_ = v___x_2555_;
v_currNamespace_2456_ = v___x_2558_;
v_openDecls_2457_ = v___x_2559_;
v_initHeartbeats_2458_ = v___x_2578_;
v_maxHeartbeats_2459_ = v___x_2561_;
v_quotContext_2460_ = v___x_2558_;
v_currMacroScope_2461_ = v___x_2562_;
v_cancelTk_x3f_2462_ = v___x_2563_;
v_inheritedTraceOptions_2463_ = v___x_2581_;
v_currRecDepth_2464_ = v___x_2560_;
v_ref_2465_ = v___x_2564_;
v_suppressElabErrors_2466_ = v___x_2566_;
v_checkDeprecated_2467_ = v___x_2567_;
v_isRecordingDeps_2468_ = v___x_2566_;
v___y_2469_ = v___x_2579_;
goto v___jp_2446_;
}
}
else
{
if (v___x_2586_ == 0)
{
lean_dec_ref_known(v___x_2583_, 3);
lean_inc(v___x_2579_);
v___y_2447_ = v___x_2556_;
v___y_2448_ = v___f_2553_;
v___y_2449_ = v___x_2566_;
v___y_2450_ = v___x_2560_;
v___y_2451_ = v___y_2546_;
v___y_2452_ = v___x_2565_;
v___y_2453_ = v___x_2579_;
v_fileName_2454_ = v___x_2554_;
v_fileMap_2455_ = v___x_2555_;
v_currNamespace_2456_ = v___x_2558_;
v_openDecls_2457_ = v___x_2559_;
v_initHeartbeats_2458_ = v___x_2578_;
v_maxHeartbeats_2459_ = v___x_2561_;
v_quotContext_2460_ = v___x_2558_;
v_currMacroScope_2461_ = v___x_2562_;
v_cancelTk_x3f_2462_ = v___x_2563_;
v_inheritedTraceOptions_2463_ = v___x_2581_;
v_currRecDepth_2464_ = v___x_2560_;
v_ref_2465_ = v___x_2564_;
v_suppressElabErrors_2466_ = v___x_2566_;
v_checkDeprecated_2467_ = v___x_2567_;
v_isRecordingDeps_2468_ = v___x_2566_;
v___y_2469_ = v___x_2579_;
goto v___jp_2446_;
}
else
{
lean_dec(v___x_2581_);
lean_dec(v___x_2578_);
v___y_2499_ = v___x_2583_;
v___y_2500_ = v___x_2556_;
v___y_2501_ = v___x_2566_;
v___y_2502_ = v___x_2572_;
v___y_2503_ = v___f_2553_;
v___y_2504_ = v___x_2566_;
v___y_2505_ = v___x_2560_;
v___y_2506_ = v___x_2565_;
v___y_2507_ = v___y_2546_;
v___y_2508_ = v___x_2579_;
goto v___jp_2498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___boxed(lean_object* v_args_2593_, lean_object* v_linterOpts_2594_, lean_object* v_sp_2595_, lean_object* v_env_2596_, lean_object* v_pkgRoot_2597_, lean_object* v_docCheckedModules_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_2593_, v_linterOpts_2594_, v_sp_2595_, v_env_2596_, v_pkgRoot_2597_, v_docCheckedModules_2598_);
lean_dec_ref(v_linterOpts_2594_);
lean_dec_ref(v_args_2593_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(lean_object* v_sp_2601_, uint8_t v___y_2602_, lean_object* v_as_2603_, size_t v_sz_2604_, size_t v_i_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___redArg(v_sp_2601_, v___y_2602_, v_as_2603_, v_sz_2604_, v_i_2605_, v_b_2606_, v___y_2607_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3___boxed(lean_object* v_sp_2611_, lean_object* v___y_2612_, lean_object* v_as_2613_, lean_object* v_sz_2614_, lean_object* v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v___y_8593__boxed_2620_; size_t v_sz_boxed_2621_; size_t v_i_boxed_2622_; lean_object* v_res_2623_; 
v___y_8593__boxed_2620_ = lean_unbox(v___y_2612_);
v_sz_boxed_2621_ = lean_unbox_usize(v_sz_2614_);
lean_dec(v_sz_2614_);
v_i_boxed_2622_ = lean_unbox_usize(v_i_2615_);
lean_dec(v_i_2615_);
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__3(v_sp_2611_, v___y_8593__boxed_2620_, v_as_2613_, v_sz_boxed_2621_, v_i_boxed_2622_, v_b_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_as_2613_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(lean_object* v_linterOpts_2624_, lean_object* v_as_2625_, size_t v_i_2626_, size_t v_stop_2627_, lean_object* v_b_2628_){
_start:
{
lean_object* v___y_2630_; uint8_t v___x_2634_; 
v___x_2634_ = lean_usize_dec_eq(v_i_2626_, v_stop_2627_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v_linter_2636_; uint8_t v___x_2637_; 
v___x_2635_ = lean_array_uget_borrowed(v_as_2625_, v_i_2626_);
v_linter_2636_ = lean_ctor_get(v___x_2635_, 0);
v___x_2637_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_2636_, v_linterOpts_2624_);
if (v___x_2637_ == 0)
{
v___y_2630_ = v_b_2628_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2638_; 
lean_inc(v___x_2635_);
v___x_2638_ = lean_array_push(v_b_2628_, v___x_2635_);
v___y_2630_ = v___x_2638_;
goto v___jp_2629_;
}
}
else
{
return v_b_2628_;
}
v___jp_2629_:
{
size_t v___x_2631_; size_t v___x_2632_; 
v___x_2631_ = ((size_t)1ULL);
v___x_2632_ = lean_usize_add(v_i_2626_, v___x_2631_);
v_i_2626_ = v___x_2632_;
v_b_2628_ = v___y_2630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1___boxed(lean_object* v_linterOpts_2639_, lean_object* v_as_2640_, lean_object* v_i_2641_, lean_object* v_stop_2642_, lean_object* v_b_2643_){
_start:
{
size_t v_i_boxed_2644_; size_t v_stop_boxed_2645_; lean_object* v_res_2646_; 
v_i_boxed_2644_ = lean_unbox_usize(v_i_2641_);
lean_dec(v_i_2641_);
v_stop_boxed_2645_ = lean_unbox_usize(v_stop_2642_);
lean_dec(v_stop_2642_);
v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2639_, v_as_2640_, v_i_boxed_2644_, v_stop_boxed_2645_, v_b_2643_);
lean_dec_ref(v_as_2640_);
lean_dec_ref(v_linterOpts_2639_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(lean_object* v_linterOpts_2649_, lean_object* v_as_2650_, size_t v_i_2651_, size_t v_stop_2652_, lean_object* v_b_2653_){
_start:
{
lean_object* v___y_2655_; uint8_t v___x_2659_; 
v___x_2659_ = lean_usize_dec_eq(v_i_2651_, v_stop_2652_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2682_; 
v___x_2660_ = lean_array_uget(v_as_2650_, v_i_2651_);
v_fst_2661_ = lean_ctor_get(v___x_2660_, 0);
v_snd_2662_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2664_ = v___x_2660_;
v_isShared_2665_ = v_isSharedCheck_2682_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2662_);
lean_inc(v_fst_2661_);
lean_dec(v___x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2682_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___y_2667_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_array_get_size(v_snd_2662_);
v___x_2677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___closed__0));
v___x_2678_ = lean_nat_dec_lt(v___x_2675_, v___x_2676_);
if (v___x_2678_ == 0)
{
lean_dec(v_snd_2662_);
v___y_2667_ = v___x_2677_;
goto v___jp_2666_;
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2676_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__1(v_linterOpts_2649_, v_snd_2662_, v___x_2679_, v___x_2680_, v___x_2677_);
lean_dec(v_snd_2662_);
v___y_2667_ = v___x_2681_;
goto v___jp_2666_;
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_array_get_size(v___y_2667_);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = lean_nat_dec_eq(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2672_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___y_2667_);
v___x_2672_ = v___x_2664_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_fst_2661_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___y_2667_);
v___x_2672_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_array_push(v_b_2653_, v___x_2672_);
v___y_2655_ = v___x_2673_;
goto v___jp_2654_;
}
}
else
{
lean_dec_ref(v___y_2667_);
lean_del_object(v___x_2664_);
lean_dec(v_fst_2661_);
v___y_2655_ = v_b_2653_;
goto v___jp_2654_;
}
}
}
}
else
{
return v_b_2653_;
}
v___jp_2654_:
{
size_t v___x_2656_; size_t v___x_2657_; 
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2651_, v___x_2656_);
v_i_2651_ = v___x_2657_;
v_b_2653_ = v___y_2655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9___boxed(lean_object* v_linterOpts_2683_, lean_object* v_as_2684_, lean_object* v_i_2685_, lean_object* v_stop_2686_, lean_object* v_b_2687_){
_start:
{
size_t v_i_boxed_2688_; size_t v_stop_boxed_2689_; lean_object* v_res_2690_; 
v_i_boxed_2688_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_stop_boxed_2689_ = lean_unbox_usize(v_stop_2686_);
lean_dec(v_stop_2686_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2683_, v_as_2684_, v_i_boxed_2688_, v_stop_boxed_2689_, v_b_2687_);
lean_dec_ref(v_as_2684_);
lean_dec_ref(v_linterOpts_2683_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(lean_object* v_linterOpts_2691_, lean_object* v_as_2692_, lean_object* v_start_2693_, lean_object* v_stop_2694_){
_start:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_2696_ = lean_nat_dec_lt(v_start_2693_, v_stop_2694_);
if (v___x_2696_ == 0)
{
return v___x_2695_;
}
else
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = lean_array_get_size(v_as_2692_);
v___x_2698_ = lean_nat_dec_le(v_stop_2694_, v___x_2697_);
if (v___x_2698_ == 0)
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_lt(v_start_2693_, v___x_2697_);
if (v___x_2699_ == 0)
{
return v___x_2695_;
}
else
{
size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_usize_of_nat(v_start_2693_);
v___x_2701_ = lean_usize_of_nat(v___x_2697_);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2691_, v_as_2692_, v___x_2700_, v___x_2701_, v___x_2695_);
return v___x_2702_;
}
}
else
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_usize_of_nat(v_start_2693_);
v___x_2704_ = lean_usize_of_nat(v_stop_2694_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9_spec__9(v_linterOpts_2691_, v_as_2692_, v___x_2703_, v___x_2704_, v___x_2695_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9___boxed(lean_object* v_linterOpts_2706_, lean_object* v_as_2707_, lean_object* v_start_2708_, lean_object* v_stop_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2706_, v_as_2707_, v_start_2708_, v_stop_2709_);
lean_dec(v_stop_2709_);
lean_dec(v_start_2708_);
lean_dec_ref(v_as_2707_);
lean_dec_ref(v_linterOpts_2706_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(lean_object* v_fst_2711_, lean_object* v_init_2712_, lean_object* v_x_2713_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
lean_object* v_k_2715_; lean_object* v_v_2716_; lean_object* v_l_2717_; lean_object* v_r_2718_; uint8_t v_anyUnlocated_2719_; lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2735_; 
v_k_2715_ = lean_ctor_get(v_x_2713_, 1);
lean_inc(v_k_2715_);
v_v_2716_ = lean_ctor_get(v_x_2713_, 2);
lean_inc(v_v_2716_);
v_l_2717_ = lean_ctor_get(v_x_2713_, 3);
lean_inc(v_l_2717_);
v_r_2718_ = lean_ctor_get(v_x_2713_, 4);
lean_inc(v_r_2718_);
lean_dec_ref_known(v_x_2713_, 5);
v_anyUnlocated_2719_ = 1;
lean_inc(v_fst_2711_);
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2711_, v_init_2712_, v_l_2717_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v_a_2722_ = lean_ctor_get(v_a_2721_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2724_ = v_a_2721_;
v_isShared_2725_ = v_isSharedCheck_2735_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v_a_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2735_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = l_Lean_Name_toString(v_k_2715_, v_anyUnlocated_2719_);
lean_inc(v_fst_2711_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 0);
lean_ctor_set(v___x_2724_, 0, v_fst_2711_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2711_);
v___x_2728_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
double v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_float_of_nat(v_v_2716_);
v___x_2730_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_2730_, 0, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2726_);
lean_ctor_set(v___x_2731_, 1, v___x_2728_);
lean_ctor_set(v___x_2731_, 2, v___x_2730_);
v___x_2732_ = lean_array_push(v_a_2722_, v___x_2731_);
v_init_2712_ = v___x_2732_;
v_x_2713_ = v_r_2718_;
goto _start;
}
}
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v_fst_2711_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_init_2712_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3___boxed(lean_object* v_fst_2738_, lean_object* v_init_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2738_, v_init_2739_, v_x_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(lean_object* v_t_2743_, lean_object* v_k_2744_, lean_object* v_fallback_2745_){
_start:
{
if (lean_obj_tag(v_t_2743_) == 0)
{
lean_object* v_k_2746_; lean_object* v_v_2747_; lean_object* v_l_2748_; lean_object* v_r_2749_; uint8_t v___x_2750_; 
v_k_2746_ = lean_ctor_get(v_t_2743_, 1);
v_v_2747_ = lean_ctor_get(v_t_2743_, 2);
v_l_2748_ = lean_ctor_get(v_t_2743_, 3);
v_r_2749_ = lean_ctor_get(v_t_2743_, 4);
v___x_2750_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2744_, v_k_2746_);
switch(v___x_2750_)
{
case 0:
{
v_t_2743_ = v_l_2748_;
goto _start;
}
case 1:
{
lean_inc(v_v_2747_);
return v_v_2747_;
}
default: 
{
v_t_2743_ = v_r_2749_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2745_);
return v_fallback_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg___boxed(lean_object* v_t_2753_, lean_object* v_k_2754_, lean_object* v_fallback_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_2753_, v_k_2754_, v_fallback_2755_);
lean_dec(v_fallback_2755_);
lean_dec(v_k_2754_);
lean_dec(v_t_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(lean_object* v_as_2757_, size_t v_i_2758_, size_t v_stop_2759_, lean_object* v_b_2760_){
_start:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_usize_dec_eq(v_i_2758_, v_stop_2759_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v_linter_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; 
v___x_2762_ = lean_array_uget_borrowed(v_as_2757_, v_i_2758_);
v_linter_2763_ = lean_ctor_get(v___x_2762_, 0);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_b_2760_, v_linter_2763_, v___x_2764_);
v___x_2766_ = lean_unsigned_to_nat(1u);
v___x_2767_ = lean_nat_add(v___x_2765_, v___x_2766_);
lean_dec(v___x_2765_);
lean_inc(v_linter_2763_);
v___x_2768_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_linter_2763_, v___x_2767_, v_b_2760_);
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2758_, v___x_2769_);
v_i_2758_ = v___x_2770_;
v_b_2760_ = v___x_2768_;
goto _start;
}
else
{
return v_b_2760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4___boxed(lean_object* v_as_2772_, lean_object* v_i_2773_, lean_object* v_stop_2774_, lean_object* v_b_2775_){
_start:
{
size_t v_i_boxed_2776_; size_t v_stop_boxed_2777_; lean_object* v_res_2778_; 
v_i_boxed_2776_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_stop_boxed_2777_ = lean_unbox_usize(v_stop_2774_);
lean_dec(v_stop_2774_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_as_2772_, v_i_boxed_2776_, v_stop_boxed_2777_, v_b_2775_);
lean_dec_ref(v_as_2772_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(lean_object* v_as_2779_, size_t v_sz_2780_, size_t v_i_2781_, lean_object* v_b_2782_){
_start:
{
lean_object* v_a_2785_; uint8_t v___x_2789_; 
v___x_2789_ = lean_usize_dec_lt(v_i_2781_, v_sz_2780_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_b_2782_);
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v_fst_2792_; lean_object* v_snd_2793_; lean_object* v___y_2795_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_a_2791_ = lean_array_uget_borrowed(v_as_2779_, v_i_2781_);
v_fst_2792_ = lean_ctor_get(v_a_2791_, 0);
v_snd_2793_ = lean_ctor_get(v_a_2791_, 1);
v___x_2807_ = lean_box(1);
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = lean_array_get_size(v_snd_2793_);
v___x_2810_ = lean_nat_dec_lt(v___x_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
v___y_2795_ = v___x_2807_;
goto v___jp_2794_;
}
else
{
size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = ((size_t)0ULL);
v___x_2812_ = lean_usize_of_nat(v___x_2809_);
v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__4(v_snd_2793_, v___x_2811_, v___x_2812_, v___x_2807_);
v___y_2795_ = v___x_2813_;
goto v___jp_2794_;
}
v___jp_2794_:
{
lean_object* v___x_2796_; 
lean_inc(v_fst_2792_);
v___x_2796_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__3(v_fst_2792_, v_b_2782_, v___y_2795_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v_a_2798_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v_a_2798_ = lean_ctor_get(v_a_2797_, 0);
lean_inc(v_a_2798_);
lean_dec(v_a_2797_);
v_a_2785_ = v_a_2798_;
goto v___jp_2784_;
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2796_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2796_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
v___jp_2784_:
{
size_t v___x_2786_; size_t v___x_2787_; 
v___x_2786_ = ((size_t)1ULL);
v___x_2787_ = lean_usize_add(v_i_2781_, v___x_2786_);
v_i_2781_ = v___x_2787_;
v_b_2782_ = v_a_2785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8___boxed(lean_object* v_as_2814_, lean_object* v_sz_2815_, lean_object* v_i_2816_, lean_object* v_b_2817_, lean_object* v___y_2818_){
_start:
{
size_t v_sz_boxed_2819_; size_t v_i_boxed_2820_; lean_object* v_res_2821_; 
v_sz_boxed_2819_ = lean_unbox_usize(v_sz_2815_);
lean_dec(v_sz_2815_);
v_i_boxed_2820_ = lean_unbox_usize(v_i_2816_);
lean_dec(v_i_2816_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v_as_2814_, v_sz_boxed_2819_, v_i_boxed_2820_, v_b_2817_);
lean_dec_ref(v_as_2814_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(lean_object* v_fst_2825_, lean_object* v_as_2826_, size_t v_sz_2827_, size_t v_i_2828_, lean_object* v_b_2829_){
_start:
{
lean_object* v_a_2832_; uint8_t v_anyUnlocated_2836_; 
v_anyUnlocated_2836_ = lean_usize_dec_lt(v_i_2828_, v_sz_2827_);
if (v_anyUnlocated_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec(v_fst_2825_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_b_2829_);
return v___x_2837_;
}
else
{
lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2876_; 
v_fst_2838_ = lean_ctor_get(v_b_2829_, 0);
v_snd_2839_ = lean_ctor_get(v_b_2829_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_b_2829_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2841_ = v_b_2829_;
v_isShared_2842_ = v_isSharedCheck_2876_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_snd_2839_);
lean_inc(v_fst_2838_);
lean_dec(v_b_2829_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2876_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_a_2843_; lean_object* v_position_x3f_2844_; 
v_a_2843_ = lean_array_uget_borrowed(v_as_2826_, v_i_2828_);
v_position_x3f_2844_ = lean_ctor_get(v_a_2843_, 2);
if (lean_obj_tag(v_position_x3f_2844_) == 0)
{
lean_object* v_linter_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v_snd_2839_);
v_linter_2845_ = lean_ctor_get(v_a_2843_, 0);
v___x_2846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__0));
lean_inc(v_linter_2845_);
v___x_2847_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_linter_2845_, v_anyUnlocated_2836_);
v___x_2848_ = lean_string_append(v___x_2846_, v___x_2847_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__1));
v___x_2850_ = lean_string_append(v___x_2848_, v___x_2849_);
lean_inc(v_fst_2825_);
v___x_2851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2825_, v_anyUnlocated_2836_);
v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___closed__2));
v___x_2854_ = lean_string_append(v___x_2852_, v___x_2853_);
v___x_2855_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_dec_ref_known(v___x_2855_, 1);
v___x_2856_ = lean_box(v_anyUnlocated_2836_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v___x_2856_);
v___x_2858_ = v___x_2841_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_fst_2838_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
v_a_2832_ = v___x_2858_;
goto v___jp_2831_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_del_object(v___x_2841_);
lean_dec(v_fst_2838_);
lean_dec(v_fst_2825_);
v_a_2860_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2855_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2855_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_linter_2868_; lean_object* v_file_2869_; lean_object* v_val_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v_linter_2868_ = lean_ctor_get(v_a_2843_, 0);
v_file_2869_ = lean_ctor_get(v_a_2843_, 3);
v_val_2870_ = lean_ctor_get(v_position_x3f_2844_, 0);
lean_inc(v_linter_2868_);
lean_inc(v_val_2870_);
lean_inc_ref(v_file_2869_);
v___x_2871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2871_, 0, v_file_2869_);
lean_ctor_set(v___x_2871_, 1, v_val_2870_);
lean_ctor_set(v___x_2871_, 2, v_linter_2868_);
v___x_2872_ = lean_array_push(v_fst_2838_, v___x_2871_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2872_);
v___x_2874_ = v___x_2841_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_snd_2839_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v_a_2832_ = v___x_2874_;
goto v___jp_2831_;
}
}
}
}
v___jp_2831_:
{
size_t v___x_2833_; size_t v___x_2834_; 
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2828_, v___x_2833_);
v_i_2828_ = v___x_2834_;
v_b_2829_ = v_a_2832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2___boxed(lean_object* v_fst_2877_, lean_object* v_as_2878_, lean_object* v_sz_2879_, lean_object* v_i_2880_, lean_object* v_b_2881_, lean_object* v___y_2882_){
_start:
{
size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2879_);
lean_dec(v_sz_2879_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2877_, v_as_2878_, v_sz_boxed_2883_, v_i_boxed_2884_, v_b_2881_);
lean_dec_ref(v_as_2878_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(lean_object* v_as_2886_, size_t v_sz_2887_, size_t v_i_2888_, lean_object* v_b_2889_){
_start:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_usize_dec_lt(v_i_2888_, v_sz_2887_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_b_2889_);
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v_fst_2894_; lean_object* v_snd_2895_; lean_object* v_fst_2896_; lean_object* v_snd_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2920_; 
v_a_2893_ = lean_array_uget_borrowed(v_as_2886_, v_i_2888_);
v_fst_2894_ = lean_ctor_get(v_a_2893_, 0);
v_snd_2895_ = lean_ctor_get(v_a_2893_, 1);
v_fst_2896_ = lean_ctor_get(v_b_2889_, 0);
v_snd_2897_ = lean_ctor_get(v_b_2889_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_b_2889_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2899_ = v_b_2889_;
v_isShared_2900_ = v_isSharedCheck_2920_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_snd_2897_);
lean_inc(v_fst_2896_);
lean_dec(v_b_2889_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2920_;
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
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_fst_2896_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_snd_2897_);
v___x_2902_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v_sz_2903_ = lean_array_size(v_snd_2895_);
v___x_2904_ = ((size_t)0ULL);
lean_inc(v_fst_2894_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__2(v_fst_2894_, v_snd_2895_, v_sz_2903_, v___x_2904_, v___x_2902_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v_fst_2907_; lean_object* v_snd_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2918_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v_fst_2907_ = lean_ctor_get(v_a_2906_, 0);
v_snd_2908_ = lean_ctor_get(v_a_2906_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_a_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2910_ = v_a_2906_;
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_snd_2908_);
lean_inc(v_fst_2907_);
lean_dec(v_a_2906_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2918_;
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
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_snd_2908_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
size_t v___x_2914_; size_t v___x_2915_; 
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_add(v_i_2888_, v___x_2914_);
v_i_2888_ = v___x_2915_;
v_b_2889_ = v___x_2913_;
goto _start;
}
}
}
else
{
return v___x_2905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7___boxed(lean_object* v_as_2921_, lean_object* v_sz_2922_, lean_object* v_i_2923_, lean_object* v_b_2924_, lean_object* v___y_2925_){
_start:
{
size_t v_sz_boxed_2926_; size_t v_i_boxed_2927_; lean_object* v_res_2928_; 
v_sz_boxed_2926_ = lean_unbox_usize(v_sz_2922_);
lean_dec(v_sz_2922_);
v_i_boxed_2927_ = lean_unbox_usize(v_i_2923_);
lean_dec(v_i_2923_);
v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v_as_2921_, v_sz_boxed_2926_, v_i_boxed_2927_, v_b_2924_);
lean_dec_ref(v_as_2921_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(lean_object* v_as_2929_, size_t v_sz_2930_, size_t v_i_2931_, lean_object* v_b_2932_){
_start:
{
uint8_t v___x_2934_; 
v___x_2934_ = lean_usize_dec_lt(v_i_2931_, v_sz_2930_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_b_2932_);
return v___x_2935_;
}
else
{
lean_object* v_a_2936_; lean_object* v_message_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2936_ = lean_array_uget_borrowed(v_as_2929_, v_i_2931_);
v_message_2937_ = lean_ctor_get(v_a_2936_, 1);
v___x_2938_ = lean_box(0);
v___x_2939_ = 0;
lean_inc_ref(v_message_2937_);
v___x_2940_ = l_Lean_SerialMessage_toString(v_message_2937_, v___x_2939_);
v___x_2941_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_2940_);
if (lean_obj_tag(v___x_2941_) == 0)
{
size_t v___x_2942_; size_t v___x_2943_; 
lean_dec_ref_known(v___x_2941_, 1);
v___x_2942_ = ((size_t)1ULL);
v___x_2943_ = lean_usize_add(v_i_2931_, v___x_2942_);
v_i_2931_ = v___x_2943_;
v_b_2932_ = v___x_2938_;
goto _start;
}
else
{
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5___boxed(lean_object* v_as_2945_, lean_object* v_sz_2946_, lean_object* v_i_2947_, lean_object* v_b_2948_, lean_object* v___y_2949_){
_start:
{
size_t v_sz_boxed_2950_; size_t v_i_boxed_2951_; lean_object* v_res_2952_; 
v_sz_boxed_2950_ = lean_unbox_usize(v_sz_2946_);
lean_dec(v_sz_2946_);
v_i_boxed_2951_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_as_2945_, v_sz_boxed_2950_, v_i_boxed_2951_, v_b_2948_);
lean_dec_ref(v_as_2945_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(lean_object* v_as_2955_, size_t v_sz_2956_, size_t v_i_2957_, lean_object* v_b_2958_){
_start:
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_usize_dec_lt(v_i_2957_, v_sz_2956_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_b_2958_);
return v___x_2961_;
}
else
{
lean_object* v_a_2962_; lean_object* v_fst_2963_; lean_object* v_snd_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2962_ = lean_array_uget_borrowed(v_as_2955_, v_i_2957_);
v_fst_2963_ = lean_ctor_get(v_a_2962_, 0);
v_snd_2964_ = lean_ctor_get(v_a_2962_, 1);
v___x_2965_ = lean_box(0);
v___x_2966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__0));
lean_inc(v_fst_2963_);
v___x_2967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2963_, v___x_2960_);
v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___closed__1));
v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
v___x_2971_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_2970_);
if (lean_obj_tag(v___x_2971_) == 0)
{
size_t v_sz_2972_; size_t v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref_known(v___x_2971_, 1);
v_sz_2972_ = lean_array_size(v_snd_2964_);
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__5(v_snd_2964_, v_sz_2972_, v___x_2973_, v___x_2965_);
if (lean_obj_tag(v___x_2974_) == 0)
{
size_t v___x_2975_; size_t v___x_2976_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_i_2957_, v___x_2975_);
v_i_2957_ = v___x_2976_;
v_b_2958_ = v___x_2965_;
goto _start;
}
else
{
return v___x_2974_;
}
}
else
{
return v___x_2971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6___boxed(lean_object* v_as_2978_, lean_object* v_sz_2979_, lean_object* v_i_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2979_);
lean_dec(v_sz_2979_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2980_);
lean_dec(v_i_2980_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v_as_2978_, v_sz_boxed_2983_, v_i_boxed_2984_, v_b_2981_);
lean_dec_ref(v_as_2978_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(lean_object* v_args_2990_, lean_object* v_linterOpts_2991_, lean_object* v_env_2992_, lean_object* v_mod_2993_){
_start:
{
uint8_t v_lintOnly_2995_; uint8_t v_mode_2996_; lean_object* v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3067_; lean_object* v___x_3073_; lean_object* v_textGroups_3074_; 
v_lintOnly_2995_ = lean_ctor_get_uint8(v_args_2990_, sizeof(void*)*4);
v_mode_2996_ = lean_ctor_get_uint8(v_args_2990_, sizeof(void*)*4 + 1);
v___x_3073_ = l_Lean_Name_getRoot(v_mod_2993_);
v_textGroups_3074_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_2992_, v___x_3073_);
lean_dec(v___x_3073_);
if (v_lintOnly_2995_ == 0)
{
v___y_3067_ = v_textGroups_3074_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_array_get_size(v_textGroups_3074_);
v___x_3077_ = l_Array_filterMapM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__9(v_linterOpts_2991_, v_textGroups_3074_, v___x_3075_, v___x_3076_);
lean_dec_ref(v_textGroups_3074_);
v___y_3067_ = v___x_3077_;
goto v___jp_3066_;
}
v___jp_2997_:
{
switch(v_mode_2996_)
{
case 0:
{
lean_object* v___x_3000_; size_t v_sz_3001_; size_t v___x_3002_; lean_object* v___x_3003_; 
v___x_3000_ = lean_box(0);
v_sz_3001_ = lean_array_size(v___y_2998_);
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__6(v___y_2998_, v_sz_3001_, v___x_3002_, v___x_3000_);
lean_dec_ref(v___y_2998_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3011_; 
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v___x_3003_, 0);
lean_dec(v_unused_3012_);
v___x_3005_ = v___x_3003_;
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v___x_3003_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3007_, 0, v___y_2999_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v_a_3013_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3003_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3003_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
case 1:
{
lean_object* v___x_3021_; size_t v_sz_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___closed__0));
v_sz_3022_ = lean_array_size(v___y_2998_);
v___x_3023_ = ((size_t)0ULL);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__7(v___y_2998_, v_sz_3022_, v___x_3023_, v___x_3021_);
lean_dec_ref(v___y_2998_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3036_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3036_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3036_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3034_; 
v_fst_3029_ = lean_ctor_get(v_a_3025_, 0);
lean_inc(v_fst_3029_);
v_snd_3030_ = lean_ctor_get(v_a_3025_, 1);
lean_inc(v_snd_3030_);
lean_dec(v_a_3025_);
v___x_3031_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3031_, 0, v_fst_3029_);
v___x_3032_ = lean_unbox(v_snd_3030_);
lean_dec(v_snd_3030_);
lean_ctor_set_uint8(v___x_3031_, sizeof(void*)*1, v___x_3032_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3031_);
v___x_3034_ = v___x_3027_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3031_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
v_a_3037_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3024_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3024_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
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
default: 
{
lean_object* v_codeQualityEntries_3045_; size_t v_sz_3046_; size_t v___x_3047_; lean_object* v___x_3048_; 
v_codeQualityEntries_3045_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality___closed__0));
v_sz_3046_ = lean_array_size(v___y_2998_);
v___x_3047_ = ((size_t)0ULL);
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__8(v___y_2998_, v_sz_3046_, v___x_3047_, v_codeQualityEntries_3045_);
lean_dec_ref(v___y_2998_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3057_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_a_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3048_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3048_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
v___jp_3066_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3068_ = lean_array_get_size(v___y_3067_);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_nat_dec_eq(v___x_3068_, v___x_3069_);
if (v___x_3070_ == 0)
{
uint8_t v___x_3071_; 
v___x_3071_ = 1;
v___y_2998_ = v___y_3067_;
v___y_2999_ = v___x_3071_;
goto v___jp_2997_;
}
else
{
uint8_t v___x_3072_; 
v___x_3072_ = 0;
v___y_2998_ = v___y_3067_;
v___y_2999_ = v___x_3072_;
goto v___jp_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters___boxed(lean_object* v_args_3078_, lean_object* v_linterOpts_3079_, lean_object* v_env_3080_, lean_object* v_mod_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_3078_, v_linterOpts_3079_, v_env_3080_, v_mod_3081_);
lean_dec(v_mod_3081_);
lean_dec_ref(v_env_3080_);
lean_dec_ref(v_linterOpts_3079_);
lean_dec_ref(v_args_3078_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(lean_object* v_00_u03b4_3084_, lean_object* v_t_3085_, lean_object* v_k_3086_, lean_object* v_fallback_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___redArg(v_t_3085_, v_k_3086_, v_fallback_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0___boxed(lean_object* v_00_u03b4_3089_, lean_object* v_t_3090_, lean_object* v_k_3091_, lean_object* v_fallback_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters_spec__0(v_00_u03b4_3089_, v_t_3090_, v_k_3091_, v_fallback_3092_);
lean_dec(v_fallback_3092_);
lean_dec(v_k_3091_);
lean_dec(v_t_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(uint8_t v___y_3094_, lean_object* v_____r_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3099_, 0, v___y_3094_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0___boxed(lean_object* v___y_3101_, lean_object* v_____r_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v___y_16393__boxed_3106_; lean_object* v_res_3107_; 
v___y_16393__boxed_3106_ = lean_unbox(v___y_3101_);
v_res_3107_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_16393__boxed_3106_, v_____r_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
return v_res_3107_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__15);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3110_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3111_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
lean_ctor_set(v___x_3113_, 2, v___x_3112_);
lean_ctor_set(v___x_3113_, 3, v___x_3112_);
lean_ctor_set(v___x_3113_, 4, v___x_3111_);
lean_ctor_set(v___x_3113_, 5, v___x_3111_);
lean_ctor_set(v___x_3113_, 6, v___x_3111_);
lean_ctor_set(v___x_3113_, 7, v___x_3111_);
lean_ctor_set(v___x_3113_, 8, v___x_3111_);
lean_ctor_set(v___x_3113_, 9, v___x_3111_);
lean_ctor_set(v___x_3113_, 10, v___x_3111_);
lean_ctor_set(v___x_3113_, 11, v___x_3110_);
return v___x_3113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_unsigned_to_nat(32u);
v___x_3115_ = lean_mk_empty_array_with_capacity(v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3(void){
_start:
{
size_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3117_ = ((size_t)5ULL);
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_unsigned_to_nat(32u);
v___x_3120_ = lean_mk_empty_array_with_capacity(v___x_3119_);
v___x_3121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__2);
v___x_3122_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3120_);
lean_ctor_set(v___x_3122_, 2, v___x_3118_);
lean_ctor_set(v___x_3122_, 3, v___x_3118_);
lean_ctor_set_usize(v___x_3122_, 4, v___x_3117_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = lean_box(1);
v___x_3124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__3);
v___x_3125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__0);
v___x_3126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3124_);
lean_ctor_set(v___x_3126_, 2, v___x_3123_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(lean_object* v_msgData_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; lean_object* v_toCold_3132_; lean_object* v_env_3133_; lean_object* v_options_3134_; uint8_t v___x_3135_; lean_object* v_env_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3131_ = lean_st_ref_get(v___y_3129_);
v_toCold_3132_ = lean_ctor_get(v___y_3128_, 0);
v_env_3133_ = lean_ctor_get(v___x_3131_, 0);
lean_inc_ref(v_env_3133_);
lean_dec(v___x_3131_);
v_options_3134_ = lean_ctor_get(v_toCold_3132_, 2);
v___x_3135_ = 0;
v_env_3136_ = l_Lean_Environment_setRecordingDeps(v_env_3133_, v___x_3135_);
v___x_3137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
lean_inc_ref(v_options_3134_);
v___x_3139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3139_, 0, v_env_3136_);
lean_ctor_set(v___x_3139_, 1, v___x_3137_);
lean_ctor_set(v___x_3139_, 2, v___x_3138_);
lean_ctor_set(v___x_3139_, 3, v_options_3134_);
v___x_3140_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v_msgData_3127_);
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___boxed(lean_object* v_msgData_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msgData_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_ref_3151_; lean_object* v___x_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
v_ref_3151_ = lean_ctor_get(v___y_3148_, 2);
v___x_3152_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18(v_msg_3147_, v___y_3148_, v___y_3149_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_inc(v_ref_3151_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_ref_3151_);
lean_ctor_set(v___x_3157_, 1, v_a_3153_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg___boxed(lean_object* v_msg_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(lean_object* v_ref_3167_, lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_toCold_3172_; lean_object* v_currRecDepth_3173_; lean_object* v_ref_3174_; uint16_t v_optionFlags_3175_; uint8_t v_suppressElabErrors_3176_; uint8_t v_checkDeprecated_3177_; uint8_t v_isRecordingDeps_3178_; lean_object* v_ref_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_toCold_3172_ = lean_ctor_get(v___y_3169_, 0);
v_currRecDepth_3173_ = lean_ctor_get(v___y_3169_, 1);
v_ref_3174_ = lean_ctor_get(v___y_3169_, 2);
v_optionFlags_3175_ = lean_ctor_get_uint16(v___y_3169_, sizeof(void*)*3);
v_suppressElabErrors_3176_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*3 + 2);
v_checkDeprecated_3177_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3178_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*3 + 4);
v_ref_3179_ = l_Lean_replaceRef(v_ref_3167_, v_ref_3174_);
lean_inc(v_currRecDepth_3173_);
lean_inc_ref(v_toCold_3172_);
v___x_3180_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3180_, 0, v_toCold_3172_);
lean_ctor_set(v___x_3180_, 1, v_currRecDepth_3173_);
lean_ctor_set(v___x_3180_, 2, v_ref_3179_);
lean_ctor_set_uint16(v___x_3180_, sizeof(void*)*3, v_optionFlags_3175_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3 + 2, v_suppressElabErrors_3176_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3 + 3, v_checkDeprecated_3177_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3 + 4, v_isRecordingDeps_3178_);
v___x_3181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_3168_, v___x_3180_, v___y_3170_);
lean_dec_ref_known(v___x_3180_, 3);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg___boxed(lean_object* v_ref_3182_, lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3182_, v_msg_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v_ref_3182_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__0));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__2));
v___x_3193_ = l_Lean_stringToMessageData(v___x_3192_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__4));
v___x_3196_ = l_Lean_stringToMessageData(v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__6));
v___x_3199_ = l_Lean_stringToMessageData(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__8));
v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__10));
v___x_3205_ = l_Lean_stringToMessageData(v___x_3204_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__12));
v___x_3208_ = l_Lean_stringToMessageData(v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(lean_object* v_msg_3209_, lean_object* v_declHint_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v_env_3215_; uint8_t v___x_3216_; 
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_st_ref_get(v___y_3211_);
v_env_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_env_3215_);
lean_dec(v___x_3214_);
v___x_3216_ = l_Lean_Name_isAnonymous(v_declHint_3210_);
if (v___x_3216_ == 0)
{
uint8_t v_isExporting_3217_; 
v_isExporting_3217_ = lean_ctor_get_uint8(v_env_3215_, sizeof(void*)*13);
if (v_isExporting_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v_env_3215_);
lean_dec(v_declHint_3210_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_msg_3209_);
return v___x_3218_;
}
else
{
lean_object* v___x_3219_; uint8_t v___x_3220_; 
lean_inc_ref(v_env_3215_);
v___x_3219_ = l_Lean_Environment_setExporting(v_env_3215_, v___x_3216_);
lean_inc(v_declHint_3210_);
lean_inc_ref(v___x_3219_);
v___x_3220_ = l_Lean_Environment_contains(v___x_3219_, v_declHint_3210_, v_isExporting_3217_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v___x_3219_);
lean_dec_ref(v_env_3215_);
lean_dec(v_declHint_3210_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_msg_3209_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_c_3227_; lean_object* v___x_3228_; 
v___x_3222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__1);
v___x_3223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17_spec__18___closed__4);
v___x_3224_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3219_);
v___x_3225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3219_);
lean_ctor_set(v___x_3225_, 1, v___x_3222_);
lean_ctor_set(v___x_3225_, 2, v___x_3223_);
lean_ctor_set(v___x_3225_, 3, v___x_3224_);
lean_inc(v_declHint_3210_);
v___x_3226_ = l_Lean_MessageData_ofConstName(v_declHint_3210_, v___x_3216_);
v_c_3227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3227_, 0, v___x_3225_);
lean_ctor_set(v_c_3227_, 1, v___x_3226_);
v___x_3228_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3219_, v_declHint_3210_);
lean_dec_ref(v___x_3219_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_dec_ref(v_env_3215_);
lean_dec(v_declHint_3210_);
v___x_3229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v_c_3227_);
v___x_3231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__3);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = l_Lean_MessageData_note(v___x_3232_);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_msg_3209_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
return v___x_3235_;
}
else
{
lean_object* v_val_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3270_; 
v_val_3236_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3238_ = v___x_3228_;
v_isShared_3239_ = v_isSharedCheck_3270_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_val_3236_);
lean_dec(v___x_3228_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3270_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v_moduleNames_3241_; lean_object* v_mod_3242_; uint8_t v___x_3243_; 
v___x_3240_ = l_Lean_Environment_header(v_env_3215_);
lean_dec_ref(v_env_3215_);
v_moduleNames_3241_ = lean_ctor_get(v___x_3240_, 4);
lean_inc_ref(v_moduleNames_3241_);
lean_dec_ref(v___x_3240_);
v_mod_3242_ = lean_array_get(v___x_3213_, v_moduleNames_3241_, v_val_3236_);
lean_dec(v_val_3236_);
lean_dec_ref(v_moduleNames_3241_);
v___x_3243_ = l_Lean_isPrivateName(v_declHint_3210_);
lean_dec(v_declHint_3210_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__5);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v_c_3227_);
v___x_3246_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__7);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_MessageData_ofName(v_mod_3242_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__9);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_MessageData_note(v___x_3251_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_msg_3209_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set_tag(v___x_3238_, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3253_);
v___x_3255_ = v___x_3238_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__1);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v_c_3227_);
v___x_3259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__11);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_MessageData_ofName(v_mod_3242_);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___closed__13);
v___x_3264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_MessageData_note(v___x_3264_);
v___x_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_msg_3209_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set_tag(v___x_3238_, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3266_);
v___x_3268_ = v___x_3238_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3271_; 
lean_dec_ref(v_env_3215_);
lean_dec(v_declHint_3210_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_msg_3209_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg___boxed(lean_object* v_msg_3272_, lean_object* v_declHint_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3272_, v_declHint_3273_, v___y_3274_);
lean_dec(v___y_3274_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(lean_object* v_msg_3277_, lean_object* v_declHint_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3292_; 
v___x_3282_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_3277_, v_declHint_3278_, v___y_3280_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = l_Lean_unknownIdentifierMessageTag;
v___x_3288_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v_a_3283_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14___boxed(lean_object* v_msg_3293_, lean_object* v_declHint_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3293_, v_declHint_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(lean_object* v_ref_3299_, lean_object* v_msg_3300_, lean_object* v_declHint_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v_a_3306_; lean_object* v___x_3307_; 
v___x_3305_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14(v_msg_3300_, v_declHint_3301_, v___y_3302_, v___y_3303_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_3299_, v_a_3306_, v___y_3302_, v___y_3303_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg___boxed(lean_object* v_ref_3308_, lean_object* v_msg_3309_, lean_object* v_declHint_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3308_, v_msg_3309_, v_declHint_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v_ref_3308_);
return v_res_3314_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__0));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_describeSite___closed__1));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_ref_3320_, lean_object* v_constName_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3325_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__1);
v___x_3326_ = 0;
lean_inc(v_constName_3321_);
v___x_3327_ = l_Lean_MessageData_ofConstName(v_constName_3321_, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3325_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___closed__2);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_3320_, v___x_3330_, v_constName_3321_, v___y_3322_, v___y_3323_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_ref_3332_, lean_object* v_constName_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3332_, v_constName_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_ref_3332_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_ref_3342_; lean_object* v___x_3343_; 
v_ref_3342_ = lean_ctor_get(v___y_3339_, 2);
v___x_3343_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_3342_, v_constName_3338_, v___y_3339_, v___y_3340_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(lean_object* v_constName_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; lean_object* v_env_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_st_ref_get(v___y_3351_);
v_env_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_env_3354_);
lean_dec(v___x_3353_);
v___x_3355_ = 0;
lean_inc(v_constName_3349_);
v___x_3356_ = l_Lean_Environment_find_x3f(v_env_3354_, v_constName_3349_, v___x_3355_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_3349_, v___y_3350_, v___y_3351_);
return v___x_3357_;
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_constName_3349_);
v_val_3358_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3356_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_val_3358_);
lean_dec(v___x_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 0);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_val_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0___boxed(lean_object* v_constName_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_constName_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(lean_object* v_declName_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_box(0);
lean_inc(v_declName_3371_);
v___x_3376_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0(v_declName_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3402_; 
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3403_);
v___x_3378_ = v___x_3376_;
v_isShared_3379_ = v_isSharedCheck_3402_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v___x_3376_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3402_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v_env_3381_; lean_object* v___x_3382_; 
v___x_3380_ = lean_st_ref_get(v___y_3373_);
v_env_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_ref(v_env_3381_);
lean_dec(v___x_3380_);
v___x_3382_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3381_, v_declName_3371_);
lean_dec(v_declName_3371_);
lean_dec_ref(v_env_3381_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(0);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3383_);
v___x_3385_ = v___x_3378_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
else
{
lean_object* v_val_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3401_; 
v_val_3387_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3389_ = v___x_3382_;
v_isShared_3390_ = v_isSharedCheck_3401_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_val_3387_);
lean_dec(v___x_3382_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3401_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; lean_object* v_env_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3391_ = lean_st_ref_get(v___y_3373_);
v_env_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc_ref(v_env_3392_);
lean_dec(v___x_3391_);
v___x_3393_ = l_Lean_Environment_allImportedModuleNames(v_env_3392_);
lean_dec_ref(v_env_3392_);
v___x_3394_ = lean_array_get(v___x_3375_, v___x_3393_, v_val_3387_);
lean_dec(v_val_3387_);
lean_dec_ref(v___x_3393_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3394_);
v___x_3396_ = v___x_3389_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3396_);
v___x_3398_ = v___x_3378_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_declName_3371_);
v_a_3404_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3376_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3376_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0___boxed(lean_object* v_declName_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_declName_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(lean_object* v_fst_3418_, lean_object* v_sp_3419_, lean_object* v___x_3420_, lean_object* v_as_3421_, size_t v_sz_3422_, size_t v_i_3423_, lean_object* v_b_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_a_3429_; uint8_t v___x_3433_; 
v___x_3433_ = lean_usize_dec_lt(v_i_3423_, v_sz_3422_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v_b_3424_);
return v___x_3434_;
}
else
{
lean_object* v_a_3435_; lean_object* v_fst_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3564_; 
v_a_3435_ = lean_array_uget(v_as_3421_, v_i_3423_);
v_fst_3436_ = lean_ctor_get(v_a_3435_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_a_3435_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_a_3435_, 1);
lean_dec(v_unused_3565_);
v___x_3438_ = v_a_3435_;
v_isShared_3439_ = v_isSharedCheck_3564_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_fst_3436_);
lean_dec(v_a_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3564_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3563_; 
v_fst_3440_ = lean_ctor_get(v_b_3424_, 0);
v_snd_3441_ = lean_ctor_get(v_b_3424_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_b_3424_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3443_ = v_b_3424_;
v_isShared_3444_ = v_isSharedCheck_3563_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snd_3441_);
lean_inc(v_fst_3440_);
lean_dec(v_b_3424_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3563_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; 
lean_inc(v_fst_3436_);
v___x_3445_ = l_Lean_findDeclarationRanges_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_deferredSitePos_x3f_spec__0(v_fst_3436_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
if (lean_obj_tag(v_a_3446_) == 0)
{
lean_object* v_optName_3447_; lean_object* v_ref_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_dec(v_snd_3441_);
v_optName_3447_ = lean_ctor_get(v_fst_3418_, 1);
v_ref_3448_ = lean_ctor_get(v___y_3425_, 2);
v___x_3449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_3436_, v___x_3433_);
v___x_3450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___closed__0));
v___x_3451_ = lean_string_append(v___x_3450_, v___x_3449_);
lean_dec_ref(v___x_3449_);
v___x_3452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__2));
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
lean_inc(v_optName_3447_);
v___x_3454_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3447_, v___x_3433_);
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3457_ = lean_string_append(v___x_3455_, v___x_3456_);
v___x_3458_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_dec_ref_known(v___x_3458_, 1);
lean_del_object(v___x_3438_);
v___x_3459_ = lean_box(v___x_3433_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3459_);
v___x_3461_ = v___x_3443_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v_a_3429_ = v___x_3461_;
goto v___jp_3428_;
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_3443_);
lean_dec(v_fst_3440_);
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v_a_3463_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3465_ = v___x_3458_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3458_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3467_ = lean_io_error_to_string(v_a_3463_);
v___x_3468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
v___x_3469_ = l_Lean_MessageData_ofFormat(v___x_3468_);
lean_inc(v_ref_3448_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3469_);
lean_ctor_set(v___x_3438_, 0, v_ref_3448_);
v___x_3471_ = v___x_3438_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_ref_3448_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3471_);
v___x_3473_ = v___x_3465_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
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
else
{
lean_object* v_val_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3554_; 
v_val_3477_ = lean_ctor_get(v_a_3446_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3479_ = v_a_3446_;
v_isShared_3480_ = v_isSharedCheck_3554_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_val_3477_);
lean_dec(v_a_3446_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3554_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; 
v___x_3481_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_3436_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___y_3484_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
if (lean_obj_tag(v_a_3482_) == 0)
{
lean_inc(v___x_3420_);
v___y_3484_ = v___x_3420_;
goto v___jp_3483_;
}
else
{
lean_object* v_val_3545_; 
v_val_3545_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v_a_3482_, 1);
v___y_3484_ = v_val_3545_;
goto v___jp_3483_;
}
v___jp_3483_:
{
lean_object* v_ref_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_ref_3485_ = lean_ctor_get(v___y_3425_, 2);
v___x_3486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__4));
lean_inc(v___y_3484_);
lean_inc(v_sp_3419_);
v___x_3487_ = l_Lean_SearchPath_findWithExt(v_sp_3419_, v___x_3486_, v___y_3484_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
if (lean_obj_tag(v_a_3488_) == 0)
{
lean_object* v_optName_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_val_3477_);
lean_dec(v_snd_3441_);
v_optName_3489_ = lean_ctor_get(v_fst_3418_, 1);
v___x_3490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__5));
v___x_3491_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3484_, v___x_3433_);
v___x_3492_ = lean_string_append(v___x_3490_, v___x_3491_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__6));
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_inc(v_optName_3489_);
v___x_3495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_optName_3489_, v___x_3433_);
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__4___closed__3));
v___x_3498_ = lean_string_append(v___x_3496_, v___x_3497_);
v___x_3499_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_3498_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3499_, 1);
lean_del_object(v___x_3479_);
lean_del_object(v___x_3438_);
v___x_3500_ = lean_box(v___x_3433_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3500_);
v___x_3502_ = v___x_3443_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_fst_3440_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
v_a_3429_ = v___x_3502_;
goto v___jp_3428_;
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3519_; 
lean_del_object(v___x_3443_);
lean_dec(v_fst_3440_);
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v_a_3504_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3506_ = v___x_3499_;
v_isShared_3507_ = v_isSharedCheck_3519_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3519_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = lean_io_error_to_string(v_a_3504_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 3);
lean_ctor_set(v___x_3479_, 0, v___x_3508_);
v___x_3510_ = v___x_3479_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = l_Lean_MessageData_ofFormat(v___x_3510_);
lean_inc(v_ref_3485_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3511_);
lean_ctor_set(v___x_3438_, 0, v_ref_3485_);
v___x_3513_ = v___x_3438_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_ref_3485_);
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
lean_object* v_range_3520_; lean_object* v_val_3521_; lean_object* v_pos_3522_; lean_object* v_optName_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
lean_dec(v___y_3484_);
lean_del_object(v___x_3479_);
lean_del_object(v___x_3438_);
v_range_3520_ = lean_ctor_get(v_val_3477_, 0);
lean_inc_ref(v_range_3520_);
lean_dec(v_val_3477_);
v_val_3521_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v_a_3488_, 1);
v_pos_3522_ = lean_ctor_get(v_range_3520_, 0);
lean_inc_ref(v_pos_3522_);
lean_dec_ref(v_range_3520_);
v_optName_3523_ = lean_ctor_get(v_fst_3418_, 1);
lean_inc(v_optName_3523_);
v___x_3524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3524_, 0, v_val_3521_);
lean_ctor_set(v___x_3524_, 1, v_pos_3522_);
lean_ctor_set(v___x_3524_, 2, v_optName_3523_);
v___x_3525_ = lean_array_push(v_fst_3440_, v___x_3524_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3525_);
v___x_3527_ = v___x_3443_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_snd_3441_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
v_a_3429_ = v___x_3527_;
goto v___jp_3428_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v___y_3484_);
lean_dec(v_val_3477_);
lean_del_object(v___x_3443_);
lean_dec(v_snd_3441_);
lean_dec(v_fst_3440_);
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v_a_3529_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3531_ = v___x_3487_;
v_isShared_3532_ = v_isSharedCheck_3544_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3487_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3544_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_io_error_to_string(v_a_3529_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 3);
lean_ctor_set(v___x_3479_, 0, v___x_3533_);
v___x_3535_ = v___x_3479_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_MessageData_ofFormat(v___x_3535_);
lean_inc(v_ref_3485_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3536_);
lean_ctor_set(v___x_3438_, 0, v_ref_3485_);
v___x_3538_ = v___x_3438_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_ref_3485_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3540_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3538_);
v___x_3540_ = v___x_3531_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3479_);
lean_dec(v_val_3477_);
lean_del_object(v___x_3443_);
lean_dec(v_snd_3441_);
lean_dec(v_fst_3440_);
lean_del_object(v___x_3438_);
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v_a_3546_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3481_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3481_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_del_object(v___x_3443_);
lean_dec(v_snd_3441_);
lean_dec(v_fst_3440_);
lean_del_object(v___x_3438_);
lean_dec(v_fst_3436_);
lean_dec(v___x_3420_);
lean_dec(v_sp_3419_);
lean_dec_ref(v_fst_3418_);
v_a_3555_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3445_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3445_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
v___jp_3428_:
{
size_t v___x_3430_; size_t v___x_3431_; 
v___x_3430_ = ((size_t)1ULL);
v___x_3431_ = lean_usize_add(v_i_3423_, v___x_3430_);
v_i_3423_ = v___x_3431_;
v_b_3424_ = v_a_3429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1___boxed(lean_object* v_fst_3566_, lean_object* v_sp_3567_, lean_object* v___x_3568_, lean_object* v_as_3569_, lean_object* v_sz_3570_, lean_object* v_i_3571_, lean_object* v_b_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3570_);
lean_dec(v_sz_3570_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3571_);
lean_dec(v_i_3571_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3566_, v_sp_3567_, v___x_3568_, v_as_3569_, v_sz_boxed_3576_, v_i_boxed_3577_, v_b_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v_as_3569_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
if (lean_obj_tag(v_x_3580_) == 0)
{
return v_x_3579_;
}
else
{
lean_object* v_key_3581_; lean_object* v_value_3582_; lean_object* v_tail_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_key_3581_ = lean_ctor_get(v_x_3580_, 0);
v_value_3582_ = lean_ctor_get(v_x_3580_, 1);
v_tail_3583_ = lean_ctor_get(v_x_3580_, 2);
lean_inc(v_value_3582_);
lean_inc(v_key_3581_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_key_3581_);
lean_ctor_set(v___x_3584_, 1, v_value_3582_);
v___x_3585_ = lean_array_push(v_x_3579_, v___x_3584_);
v_x_3579_ = v___x_3585_;
v_x_3580_ = v_tail_3583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2___boxed(lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_x_3587_, v_x_3588_);
lean_dec(v_x_3588_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(lean_object* v_as_3590_, size_t v_i_3591_, size_t v_stop_3592_, lean_object* v_b_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_eq(v_i_3591_, v_stop_3592_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; size_t v___x_3597_; size_t v___x_3598_; 
v___x_3595_ = lean_array_uget_borrowed(v_as_3590_, v_i_3591_);
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__2(v_b_3593_, v___x_3595_);
v___x_3597_ = ((size_t)1ULL);
v___x_3598_ = lean_usize_add(v_i_3591_, v___x_3597_);
v_i_3591_ = v___x_3598_;
v_b_3593_ = v___x_3596_;
goto _start;
}
else
{
return v_b_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3___boxed(lean_object* v_as_3600_, lean_object* v_i_3601_, lean_object* v_stop_3602_, lean_object* v_b_3603_){
_start:
{
size_t v_i_boxed_3604_; size_t v_stop_boxed_3605_; lean_object* v_res_3606_; 
v_i_boxed_3604_ = lean_unbox_usize(v_i_3601_);
lean_dec(v_i_3601_);
v_stop_boxed_3605_ = lean_unbox_usize(v_stop_3602_);
lean_dec(v_stop_3602_);
v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_as_3600_, v_i_boxed_3604_, v_stop_boxed_3605_, v_b_3603_);
lean_dec_ref(v_as_3600_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(lean_object* v_sp_3607_, lean_object* v___x_3608_, lean_object* v_as_3609_, size_t v_sz_3610_, size_t v_i_3611_, lean_object* v_b_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_usize_dec_lt(v_i_3611_, v_sz_3610_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v___x_3608_);
lean_dec(v_sp_3607_);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v_b_3612_);
return v___x_3617_;
}
else
{
lean_object* v_a_3618_; lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3656_; 
v_a_3618_ = lean_array_uget_borrowed(v_as_3609_, v_i_3611_);
v_fst_3619_ = lean_ctor_get(v_a_3618_, 0);
v_snd_3620_ = lean_ctor_get(v_a_3618_, 1);
v_fst_3621_ = lean_ctor_get(v_b_3612_, 0);
v_snd_3622_ = lean_ctor_get(v_b_3612_, 1);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_b_3612_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3624_ = v_b_3612_;
v_isShared_3625_ = v_isSharedCheck_3656_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_snd_3622_);
lean_inc(v_fst_3621_);
lean_dec(v_b_3612_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3656_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___y_3627_; lean_object* v_size_3647_; lean_object* v_buckets_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v_size_3647_ = lean_ctor_get(v_snd_3620_, 0);
v_buckets_3648_ = lean_ctor_get(v_snd_3620_, 1);
v___x_3649_ = lean_mk_empty_array_with_capacity(v_size_3647_);
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = lean_array_get_size(v_buckets_3648_);
v___x_3652_ = lean_nat_dec_lt(v___x_3650_, v___x_3651_);
if (v___x_3652_ == 0)
{
v___y_3627_ = v___x_3649_;
goto v___jp_3626_;
}
else
{
size_t v___x_3653_; size_t v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = ((size_t)0ULL);
v___x_3654_ = lean_usize_of_nat(v___x_3651_);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_3648_, v___x_3653_, v___x_3654_, v___x_3649_);
v___y_3627_ = v___x_3655_;
goto v___jp_3626_;
}
v___jp_3626_:
{
lean_object* v___x_3629_; 
if (v_isShared_3625_ == 0)
{
v___x_3629_ = v___x_3624_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_fst_3621_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_snd_3622_);
v___x_3629_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
size_t v_sz_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v_sz_3630_ = lean_array_size(v___y_3627_);
v___x_3631_ = ((size_t)0ULL);
lean_inc(v___x_3608_);
lean_inc(v_sp_3607_);
lean_inc(v_fst_3619_);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__1(v_fst_3619_, v_sp_3607_, v___x_3608_, v___y_3627_, v_sz_3630_, v___x_3631_, v___x_3629_, v___y_3613_, v___y_3614_);
lean_dec_ref(v___y_3627_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v_fst_3634_; lean_object* v_snd_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3645_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v_fst_3634_ = lean_ctor_get(v_a_3633_, 0);
v_snd_3635_ = lean_ctor_get(v_a_3633_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_a_3633_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3637_ = v_a_3633_;
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3635_);
lean_inc(v_fst_3634_);
lean_dec(v_a_3633_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_fst_3634_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_snd_3635_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
size_t v___x_3641_; size_t v___x_3642_; 
v___x_3641_ = ((size_t)1ULL);
v___x_3642_ = lean_usize_add(v_i_3611_, v___x_3641_);
v_i_3611_ = v___x_3642_;
v_b_3612_ = v___x_3640_;
goto _start;
}
}
}
else
{
lean_dec(v___x_3608_);
lean_dec(v_sp_3607_);
return v___x_3632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4___boxed(lean_object* v_sp_3657_, lean_object* v___x_3658_, lean_object* v_as_3659_, lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
size_t v_sz_boxed_3666_; size_t v_i_boxed_3667_; lean_object* v_res_3668_; 
v_sz_boxed_3666_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3667_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_3657_, v___x_3658_, v_as_3659_, v_sz_boxed_3666_, v_i_boxed_3667_, v_b_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_as_3659_);
return v_res_3668_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(uint8_t v___y_3669_, lean_object* v_as_3670_, size_t v_i_3671_, size_t v_stop_3672_){
_start:
{
uint8_t v___x_3673_; 
v___x_3673_ = lean_usize_dec_eq(v_i_3671_, v_stop_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v_snd_3675_; lean_object* v_size_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3674_ = lean_array_uget_borrowed(v_as_3670_, v_i_3671_);
v_snd_3675_ = lean_ctor_get(v___x_3674_, 1);
v_size_3676_ = lean_ctor_get(v_snd_3675_, 0);
v___x_3677_ = 1;
v___x_3678_ = lean_unsigned_to_nat(0u);
v___x_3679_ = lean_nat_dec_eq(v_size_3676_, v___x_3678_);
if (v___x_3679_ == 0)
{
return v___x_3677_;
}
else
{
if (v___y_3669_ == 0)
{
size_t v___x_3680_; size_t v___x_3681_; 
v___x_3680_ = ((size_t)1ULL);
v___x_3681_ = lean_usize_add(v_i_3671_, v___x_3680_);
v_i_3671_ = v___x_3681_;
goto _start;
}
else
{
return v___x_3677_;
}
}
}
else
{
uint8_t v___x_3683_; 
v___x_3683_ = 0;
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10___boxed(lean_object* v___y_3684_, lean_object* v_as_3685_, lean_object* v_i_3686_, lean_object* v_stop_3687_){
_start:
{
uint8_t v___y_17368__boxed_3688_; size_t v_i_boxed_3689_; size_t v_stop_boxed_3690_; uint8_t v_res_3691_; lean_object* v_r_3692_; 
v___y_17368__boxed_3688_ = lean_unbox(v___y_3684_);
v_i_boxed_3689_ = lean_unbox_usize(v_i_3686_);
lean_dec(v_i_3686_);
v_stop_boxed_3690_ = lean_unbox_usize(v_stop_3687_);
lean_dec(v_stop_3687_);
v_res_3691_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_17368__boxed_3688_, v_as_3685_, v_i_boxed_3689_, v_stop_boxed_3690_);
lean_dec_ref(v_as_3685_);
v_r_3692_ = lean_box(v_res_3691_);
return v_r_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(lean_object* v_k_3693_, lean_object* v_v_3694_, lean_object* v_t_3695_){
_start:
{
lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; 
if (lean_obj_tag(v_t_3695_) == 0)
{
lean_object* v_size_3710_; lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v_l_3713_; lean_object* v_r_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3974_; 
v_size_3710_ = lean_ctor_get(v_t_3695_, 0);
v_k_3711_ = lean_ctor_get(v_t_3695_, 1);
v_v_3712_ = lean_ctor_get(v_t_3695_, 2);
v_l_3713_ = lean_ctor_get(v_t_3695_, 3);
v_r_3714_ = lean_ctor_get(v_t_3695_, 4);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_t_3695_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3716_ = v_t_3695_;
v_isShared_3717_ = v_isSharedCheck_3974_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_r_3714_);
lean_inc(v_l_3713_);
lean_inc(v_v_3712_);
lean_inc(v_k_3711_);
lean_inc(v_size_3710_);
lean_dec(v_t_3695_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3974_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; uint8_t v___y_3768_; lean_object* v_fst_3968_; lean_object* v_snd_3969_; lean_object* v_fst_3970_; lean_object* v_snd_3971_; uint8_t v___x_3972_; 
v_fst_3968_ = lean_ctor_get(v_k_3693_, 0);
v_snd_3969_ = lean_ctor_get(v_k_3693_, 1);
v_fst_3970_ = lean_ctor_get(v_k_3711_, 0);
v_snd_3971_ = lean_ctor_get(v_k_3711_, 1);
v___x_3972_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3968_, v_fst_3970_);
if (v___x_3972_ == 1)
{
uint8_t v___x_3973_; 
v___x_3973_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3969_, v_snd_3971_);
v___y_3768_ = v___x_3973_;
goto v___jp_3767_;
}
else
{
v___y_3768_ = v___x_3972_;
goto v___jp_3767_;
}
v___jp_3718_:
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3726_ = lean_nat_add(v___y_3719_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec(v___y_3719_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 3, v___y_3720_);
lean_ctor_set(v___x_3716_, 0, v___x_3726_);
v___x_3728_ = v___x_3716_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v___y_3720_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_r_3714_);
v___x_3728_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3729_, 0, v___y_3721_);
lean_ctor_set(v___x_3729_, 1, v___y_3723_);
lean_ctor_set(v___x_3729_, 2, v___y_3724_);
lean_ctor_set(v___x_3729_, 3, v___y_3722_);
lean_ctor_set(v___x_3729_, 4, v___x_3728_);
return v___x_3729_;
}
}
v___jp_3731_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = lean_nat_add(v___y_3733_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec(v___y_3733_);
v___x_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v___y_3736_);
lean_ctor_set(v___x_3745_, 2, v___y_3738_);
lean_ctor_set(v___x_3745_, 3, v___y_3734_);
lean_ctor_set(v___x_3745_, 4, v___y_3742_);
v___x_3746_ = lean_nat_add(v___y_3740_, v___y_3732_);
lean_dec(v___y_3732_);
if (lean_obj_tag(v___y_3735_) == 0)
{
lean_object* v_size_3747_; 
v_size_3747_ = lean_ctor_get(v___y_3735_, 0);
lean_inc(v_size_3747_);
v___y_3719_ = v___x_3746_;
v___y_3720_ = v___y_3735_;
v___y_3721_ = v___y_3737_;
v___y_3722_ = v___x_3745_;
v___y_3723_ = v___y_3739_;
v___y_3724_ = v___y_3741_;
v___y_3725_ = v_size_3747_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_unsigned_to_nat(0u);
v___y_3719_ = v___x_3746_;
v___y_3720_ = v___y_3735_;
v___y_3721_ = v___y_3737_;
v___y_3722_ = v___x_3745_;
v___y_3723_ = v___y_3739_;
v___y_3724_ = v___y_3741_;
v___y_3725_ = v___x_3748_;
goto v___jp_3718_;
}
}
v___jp_3749_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_nat_add(v___y_3757_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec(v___y_3757_);
v___x_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v_k_3711_);
lean_ctor_set(v___x_3763_, 2, v_v_3712_);
lean_ctor_set(v___x_3763_, 3, v_l_3713_);
lean_ctor_set(v___x_3763_, 4, v___y_3753_);
v___x_3764_ = lean_nat_add(v___y_3756_, v___y_3755_);
lean_dec(v___y_3755_);
if (lean_obj_tag(v___y_3750_) == 0)
{
lean_object* v_size_3765_; 
v_size_3765_ = lean_ctor_get(v___y_3750_, 0);
lean_inc(v_size_3765_);
v___y_3697_ = v___y_3750_;
v___y_3698_ = v___y_3751_;
v___y_3699_ = v___y_3752_;
v___y_3700_ = v___y_3754_;
v___y_3701_ = v___y_3758_;
v___y_3702_ = v___x_3763_;
v___y_3703_ = v___y_3759_;
v___y_3704_ = v___x_3764_;
v___y_3705_ = v___y_3760_;
v___y_3706_ = v_size_3765_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_unsigned_to_nat(0u);
v___y_3697_ = v___y_3750_;
v___y_3698_ = v___y_3751_;
v___y_3699_ = v___y_3752_;
v___y_3700_ = v___y_3754_;
v___y_3701_ = v___y_3758_;
v___y_3702_ = v___x_3763_;
v___y_3703_ = v___y_3759_;
v___y_3704_ = v___x_3764_;
v___y_3705_ = v___y_3760_;
v___y_3706_ = v___x_3766_;
goto v___jp_3696_;
}
}
v___jp_3767_:
{
switch(v___y_3768_)
{
case 0:
{
lean_object* v_impl_3769_; lean_object* v___x_3770_; 
lean_dec(v_size_3710_);
v_impl_3769_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3693_, v_v_3694_, v_l_3713_);
v___x_3770_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3714_) == 0)
{
lean_object* v_size_3771_; lean_object* v_size_3772_; lean_object* v_k_3773_; lean_object* v_v_3774_; lean_object* v_l_3775_; lean_object* v_r_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_size_3771_ = lean_ctor_get(v_r_3714_, 0);
v_size_3772_ = lean_ctor_get(v_impl_3769_, 0);
v_k_3773_ = lean_ctor_get(v_impl_3769_, 1);
v_v_3774_ = lean_ctor_get(v_impl_3769_, 2);
v_l_3775_ = lean_ctor_get(v_impl_3769_, 3);
v_r_3776_ = lean_ctor_get(v_impl_3769_, 4);
v___x_3777_ = lean_unsigned_to_nat(3u);
v___x_3778_ = lean_nat_mul(v___x_3777_, v_size_3771_);
v___x_3779_ = lean_nat_dec_lt(v___x_3778_, v_size_3772_);
lean_dec(v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_del_object(v___x_3716_);
v___x_3780_ = lean_nat_add(v___x_3770_, v_size_3772_);
v___x_3781_ = lean_nat_add(v___x_3780_, v_size_3771_);
lean_dec(v___x_3780_);
v___x_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
lean_ctor_set(v___x_3782_, 1, v_k_3711_);
lean_ctor_set(v___x_3782_, 2, v_v_3712_);
lean_ctor_set(v___x_3782_, 3, v_impl_3769_);
lean_ctor_set(v___x_3782_, 4, v_r_3714_);
return v___x_3782_;
}
else
{
lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3819_; 
lean_inc(v_r_3776_);
lean_inc(v_l_3775_);
lean_inc(v_v_3774_);
lean_inc(v_k_3773_);
lean_inc(v_size_3772_);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_impl_3769_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; lean_object* v_unused_3823_; lean_object* v_unused_3824_; 
v_unused_3820_ = lean_ctor_get(v_impl_3769_, 4);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_impl_3769_, 3);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_impl_3769_, 2);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_impl_3769_, 1);
lean_dec(v_unused_3823_);
v_unused_3824_ = lean_ctor_get(v_impl_3769_, 0);
lean_dec(v_unused_3824_);
v___x_3784_ = v_impl_3769_;
v_isShared_3785_ = v_isSharedCheck_3819_;
goto v_resetjp_3783_;
}
else
{
lean_dec(v_impl_3769_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3819_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_size_3786_; lean_object* v_size_3787_; lean_object* v_k_3788_; lean_object* v_v_3789_; lean_object* v_l_3790_; lean_object* v_r_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v_size_3786_ = lean_ctor_get(v_l_3775_, 0);
v_size_3787_ = lean_ctor_get(v_r_3776_, 0);
v_k_3788_ = lean_ctor_get(v_r_3776_, 1);
v_v_3789_ = lean_ctor_get(v_r_3776_, 2);
v_l_3790_ = lean_ctor_get(v_r_3776_, 3);
v_r_3791_ = lean_ctor_get(v_r_3776_, 4);
v___x_3792_ = lean_unsigned_to_nat(2u);
v___x_3793_ = lean_nat_mul(v___x_3792_, v_size_3786_);
v___x_3794_ = lean_nat_dec_lt(v_size_3787_, v___x_3793_);
lean_dec(v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_inc(v_r_3791_);
lean_inc(v_l_3790_);
lean_inc(v_v_3789_);
lean_inc(v_k_3788_);
lean_del_object(v___x_3784_);
lean_dec(v_r_3776_);
v___x_3795_ = lean_nat_add(v___x_3770_, v_size_3772_);
lean_dec(v_size_3772_);
v___x_3796_ = lean_nat_add(v___x_3795_, v_size_3771_);
lean_dec(v___x_3795_);
v___x_3797_ = lean_nat_add(v___x_3770_, v_size_3786_);
if (lean_obj_tag(v_l_3790_) == 0)
{
lean_object* v_size_3798_; 
v_size_3798_ = lean_ctor_get(v_l_3790_, 0);
lean_inc(v_size_3798_);
lean_inc(v_size_3771_);
v___y_3732_ = v_size_3771_;
v___y_3733_ = v___x_3797_;
v___y_3734_ = v_l_3775_;
v___y_3735_ = v_r_3791_;
v___y_3736_ = v_k_3773_;
v___y_3737_ = v___x_3796_;
v___y_3738_ = v_v_3774_;
v___y_3739_ = v_k_3788_;
v___y_3740_ = v___x_3770_;
v___y_3741_ = v_v_3789_;
v___y_3742_ = v_l_3790_;
v___y_3743_ = v_size_3798_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_3771_);
v___y_3732_ = v_size_3771_;
v___y_3733_ = v___x_3797_;
v___y_3734_ = v_l_3775_;
v___y_3735_ = v_r_3791_;
v___y_3736_ = v_k_3773_;
v___y_3737_ = v___x_3796_;
v___y_3738_ = v_v_3774_;
v___y_3739_ = v_k_3788_;
v___y_3740_ = v___x_3770_;
v___y_3741_ = v_v_3789_;
v___y_3742_ = v_l_3790_;
v___y_3743_ = v___x_3799_;
goto v___jp_3731_;
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
lean_del_object(v___x_3716_);
v___x_3800_ = lean_nat_add(v___x_3770_, v_size_3772_);
lean_dec(v_size_3772_);
v___x_3801_ = lean_nat_add(v___x_3800_, v_size_3771_);
lean_dec(v___x_3800_);
v___x_3802_ = lean_nat_add(v___x_3770_, v_size_3771_);
v___x_3803_ = lean_nat_add(v___x_3802_, v_size_3787_);
lean_dec(v___x_3802_);
lean_inc_ref(v_r_3714_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v_r_3714_);
lean_ctor_set(v___x_3784_, 3, v_r_3776_);
lean_ctor_set(v___x_3784_, 2, v_v_3712_);
lean_ctor_set(v___x_3784_, 1, v_k_3711_);
lean_ctor_set(v___x_3784_, 0, v___x_3803_);
v___x_3805_ = v___x_3784_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_r_3776_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_r_3714_);
v___x_3805_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
v_isSharedCheck_3812_ = !lean_is_exclusive(v_r_3714_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; lean_object* v_unused_3814_; lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; 
v_unused_3813_ = lean_ctor_get(v_r_3714_, 4);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_r_3714_, 3);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_r_3714_, 2);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_r_3714_, 1);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3714_, 0);
lean_dec(v_unused_3817_);
v___x_3807_ = v_r_3714_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v_r_3714_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 4, v___x_3805_);
lean_ctor_set(v___x_3807_, 3, v_l_3775_);
lean_ctor_set(v___x_3807_, 2, v_v_3774_);
lean_ctor_set(v___x_3807_, 1, v_k_3773_);
lean_ctor_set(v___x_3807_, 0, v___x_3801_);
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v___x_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3825_; 
lean_del_object(v___x_3716_);
v_l_3825_ = lean_ctor_get(v_impl_3769_, 3);
if (lean_obj_tag(v_l_3825_) == 0)
{
lean_object* v_r_3826_; lean_object* v_k_3827_; lean_object* v_v_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3837_; 
lean_inc_ref(v_l_3825_);
v_r_3826_ = lean_ctor_get(v_impl_3769_, 4);
v_k_3827_ = lean_ctor_get(v_impl_3769_, 1);
v_v_3828_ = lean_ctor_get(v_impl_3769_, 2);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_impl_3769_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; 
v_unused_3838_ = lean_ctor_get(v_impl_3769_, 3);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_impl_3769_, 0);
lean_dec(v_unused_3839_);
v___x_3830_ = v_impl_3769_;
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_r_3826_);
lean_inc(v_v_3828_);
lean_inc(v_k_3827_);
lean_dec(v_impl_3769_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3826_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 3, v_r_3826_);
lean_ctor_set(v___x_3830_, 2, v_v_3712_);
lean_ctor_set(v___x_3830_, 1, v_k_3711_);
lean_ctor_set(v___x_3830_, 0, v___x_3770_);
v___x_3834_ = v___x_3830_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_r_3826_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v_r_3826_);
v___x_3834_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3832_);
lean_ctor_set(v___x_3835_, 1, v_k_3827_);
lean_ctor_set(v___x_3835_, 2, v_v_3828_);
lean_ctor_set(v___x_3835_, 3, v_l_3825_);
lean_ctor_set(v___x_3835_, 4, v___x_3834_);
return v___x_3835_;
}
}
}
else
{
lean_object* v_r_3840_; 
v_r_3840_ = lean_ctor_get(v_impl_3769_, 4);
lean_inc(v_r_3840_);
if (lean_obj_tag(v_r_3840_) == 0)
{
lean_object* v_k_3841_; lean_object* v_v_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3863_; 
lean_inc(v_l_3825_);
v_k_3841_ = lean_ctor_get(v_impl_3769_, 1);
v_v_3842_ = lean_ctor_get(v_impl_3769_, 2);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_impl_3769_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; 
v_unused_3864_ = lean_ctor_get(v_impl_3769_, 4);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_impl_3769_, 3);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_impl_3769_, 0);
lean_dec(v_unused_3866_);
v___x_3844_ = v_impl_3769_;
v_isShared_3845_ = v_isSharedCheck_3863_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
lean_dec(v_impl_3769_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3863_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v_k_3846_; lean_object* v_v_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3859_; 
v_k_3846_ = lean_ctor_get(v_r_3840_, 1);
v_v_3847_ = lean_ctor_get(v_r_3840_, 2);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_r_3840_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; lean_object* v_unused_3861_; lean_object* v_unused_3862_; 
v_unused_3860_ = lean_ctor_get(v_r_3840_, 4);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_r_3840_, 3);
lean_dec(v_unused_3861_);
v_unused_3862_ = lean_ctor_get(v_r_3840_, 0);
lean_dec(v_unused_3862_);
v___x_3849_ = v_r_3840_;
v_isShared_3850_ = v_isSharedCheck_3859_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_v_3847_);
lean_inc(v_k_3846_);
lean_dec(v_r_3840_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3859_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3851_ = lean_unsigned_to_nat(3u);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 4, v_l_3825_);
lean_ctor_set(v___x_3849_, 3, v_l_3825_);
lean_ctor_set(v___x_3849_, 2, v_v_3842_);
lean_ctor_set(v___x_3849_, 1, v_k_3841_);
lean_ctor_set(v___x_3849_, 0, v___x_3770_);
v___x_3853_ = v___x_3849_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_l_3825_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_l_3825_);
v___x_3853_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 4, v_l_3825_);
lean_ctor_set(v___x_3844_, 2, v_v_3712_);
lean_ctor_set(v___x_3844_, 1, v_k_3711_);
lean_ctor_set(v___x_3844_, 0, v___x_3770_);
v___x_3855_ = v___x_3844_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v_l_3825_);
lean_ctor_set(v_reuseFailAlloc_3857_, 4, v_l_3825_);
v___x_3855_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3851_);
lean_ctor_set(v___x_3856_, 1, v_k_3846_);
lean_ctor_set(v___x_3856_, 2, v_v_3847_);
lean_ctor_set(v___x_3856_, 3, v___x_3853_);
lean_ctor_set(v___x_3856_, 4, v___x_3855_);
return v___x_3856_;
}
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_unsigned_to_nat(2u);
v___x_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v_k_3711_);
lean_ctor_set(v___x_3868_, 2, v_v_3712_);
lean_ctor_set(v___x_3868_, 3, v_impl_3769_);
lean_ctor_set(v___x_3868_, 4, v_r_3840_);
return v___x_3868_;
}
}
}
}
case 1:
{
lean_object* v___x_3869_; 
lean_del_object(v___x_3716_);
lean_dec(v_v_3712_);
lean_dec(v_k_3711_);
v___x_3869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3869_, 0, v_size_3710_);
lean_ctor_set(v___x_3869_, 1, v_k_3693_);
lean_ctor_set(v___x_3869_, 2, v_v_3694_);
lean_ctor_set(v___x_3869_, 3, v_l_3713_);
lean_ctor_set(v___x_3869_, 4, v_r_3714_);
return v___x_3869_;
}
default: 
{
lean_object* v_impl_3870_; lean_object* v___x_3871_; 
lean_del_object(v___x_3716_);
lean_dec(v_size_3710_);
v_impl_3870_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_3693_, v_v_3694_, v_r_3714_);
v___x_3871_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3713_) == 0)
{
lean_object* v_size_3872_; lean_object* v_size_3873_; lean_object* v_k_3874_; lean_object* v_v_3875_; lean_object* v_l_3876_; lean_object* v_r_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v_size_3872_ = lean_ctor_get(v_l_3713_, 0);
v_size_3873_ = lean_ctor_get(v_impl_3870_, 0);
v_k_3874_ = lean_ctor_get(v_impl_3870_, 1);
v_v_3875_ = lean_ctor_get(v_impl_3870_, 2);
v_l_3876_ = lean_ctor_get(v_impl_3870_, 3);
v_r_3877_ = lean_ctor_get(v_impl_3870_, 4);
v___x_3878_ = lean_unsigned_to_nat(3u);
v___x_3879_ = lean_nat_mul(v___x_3878_, v_size_3872_);
v___x_3880_ = lean_nat_dec_lt(v___x_3879_, v_size_3873_);
lean_dec(v___x_3879_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_nat_add(v___x_3871_, v_size_3872_);
v___x_3882_ = lean_nat_add(v___x_3881_, v_size_3873_);
lean_dec(v___x_3881_);
v___x_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v_k_3711_);
lean_ctor_set(v___x_3883_, 2, v_v_3712_);
lean_ctor_set(v___x_3883_, 3, v_l_3713_);
lean_ctor_set(v___x_3883_, 4, v_impl_3870_);
return v___x_3883_;
}
else
{
lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3918_; 
lean_inc(v_r_3877_);
lean_inc(v_l_3876_);
lean_inc(v_v_3875_);
lean_inc(v_k_3874_);
lean_inc(v_size_3873_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_impl_3870_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3919_ = lean_ctor_get(v_impl_3870_, 4);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_impl_3870_, 3);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_impl_3870_, 2);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_impl_3870_, 1);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_impl_3870_, 0);
lean_dec(v_unused_3923_);
v___x_3885_ = v_impl_3870_;
v_isShared_3886_ = v_isSharedCheck_3918_;
goto v_resetjp_3884_;
}
else
{
lean_dec(v_impl_3870_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3918_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_size_3887_; lean_object* v_k_3888_; lean_object* v_v_3889_; lean_object* v_l_3890_; lean_object* v_r_3891_; lean_object* v_size_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v_size_3887_ = lean_ctor_get(v_l_3876_, 0);
v_k_3888_ = lean_ctor_get(v_l_3876_, 1);
v_v_3889_ = lean_ctor_get(v_l_3876_, 2);
v_l_3890_ = lean_ctor_get(v_l_3876_, 3);
v_r_3891_ = lean_ctor_get(v_l_3876_, 4);
v_size_3892_ = lean_ctor_get(v_r_3877_, 0);
v___x_3893_ = lean_unsigned_to_nat(2u);
v___x_3894_ = lean_nat_mul(v___x_3893_, v_size_3892_);
v___x_3895_ = lean_nat_dec_lt(v_size_3887_, v___x_3894_);
lean_dec(v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_inc(v_size_3892_);
lean_inc(v_r_3891_);
lean_inc(v_l_3890_);
lean_inc(v_v_3889_);
lean_inc(v_k_3888_);
lean_del_object(v___x_3885_);
lean_dec(v_l_3876_);
v___x_3896_ = lean_nat_add(v___x_3871_, v_size_3872_);
v___x_3897_ = lean_nat_add(v___x_3896_, v_size_3873_);
lean_dec(v_size_3873_);
if (lean_obj_tag(v_l_3890_) == 0)
{
lean_object* v_size_3898_; 
v_size_3898_ = lean_ctor_get(v_l_3890_, 0);
lean_inc(v_size_3898_);
v___y_3750_ = v_r_3891_;
v___y_3751_ = v___x_3897_;
v___y_3752_ = v_k_3874_;
v___y_3753_ = v_l_3890_;
v___y_3754_ = v_r_3877_;
v___y_3755_ = v_size_3892_;
v___y_3756_ = v___x_3871_;
v___y_3757_ = v___x_3896_;
v___y_3758_ = v_k_3888_;
v___y_3759_ = v_v_3875_;
v___y_3760_ = v_v_3889_;
v___y_3761_ = v_size_3898_;
goto v___jp_3749_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_unsigned_to_nat(0u);
v___y_3750_ = v_r_3891_;
v___y_3751_ = v___x_3897_;
v___y_3752_ = v_k_3874_;
v___y_3753_ = v_l_3890_;
v___y_3754_ = v_r_3877_;
v___y_3755_ = v_size_3892_;
v___y_3756_ = v___x_3871_;
v___y_3757_ = v___x_3896_;
v___y_3758_ = v_k_3888_;
v___y_3759_ = v_v_3875_;
v___y_3760_ = v_v_3889_;
v___y_3761_ = v___x_3899_;
goto v___jp_3749_;
}
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3900_ = lean_nat_add(v___x_3871_, v_size_3872_);
v___x_3901_ = lean_nat_add(v___x_3900_, v_size_3873_);
lean_dec(v_size_3873_);
v___x_3902_ = lean_nat_add(v___x_3900_, v_size_3887_);
lean_dec(v___x_3900_);
lean_inc_ref(v_l_3713_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 4, v_l_3876_);
lean_ctor_set(v___x_3885_, 3, v_l_3713_);
lean_ctor_set(v___x_3885_, 2, v_v_3712_);
lean_ctor_set(v___x_3885_, 1, v_k_3711_);
lean_ctor_set(v___x_3885_, 0, v___x_3902_);
v___x_3904_ = v___x_3885_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_l_3713_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v_l_3876_);
v___x_3904_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v_l_3713_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3912_ = lean_ctor_get(v_l_3713_, 4);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_l_3713_, 3);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_l_3713_, 2);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_l_3713_, 1);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3713_, 0);
lean_dec(v_unused_3916_);
v___x_3906_ = v_l_3713_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_dec(v_l_3713_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 4, v_r_3877_);
lean_ctor_set(v___x_3906_, 3, v___x_3904_);
lean_ctor_set(v___x_3906_, 2, v_v_3875_);
lean_ctor_set(v___x_3906_, 1, v_k_3874_);
lean_ctor_set(v___x_3906_, 0, v___x_3901_);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_k_3874_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_v_3875_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v_r_3877_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3924_; 
v_l_3924_ = lean_ctor_get(v_impl_3870_, 3);
lean_inc(v_l_3924_);
if (lean_obj_tag(v_l_3924_) == 0)
{
lean_object* v_r_3925_; lean_object* v_k_3926_; lean_object* v_v_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3948_; 
v_r_3925_ = lean_ctor_get(v_impl_3870_, 4);
v_k_3926_ = lean_ctor_get(v_impl_3870_, 1);
v_v_3927_ = lean_ctor_get(v_impl_3870_, 2);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_impl_3870_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3949_ = lean_ctor_get(v_impl_3870_, 3);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_impl_3870_, 0);
lean_dec(v_unused_3950_);
v___x_3929_ = v_impl_3870_;
v_isShared_3930_ = v_isSharedCheck_3948_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_r_3925_);
lean_inc(v_v_3927_);
lean_inc(v_k_3926_);
lean_dec(v_impl_3870_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3948_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v_k_3931_; lean_object* v_v_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3944_; 
v_k_3931_ = lean_ctor_get(v_l_3924_, 1);
v_v_3932_ = lean_ctor_get(v_l_3924_, 2);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_l_3924_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; 
v_unused_3945_ = lean_ctor_get(v_l_3924_, 4);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_l_3924_, 3);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_l_3924_, 0);
lean_dec(v_unused_3947_);
v___x_3934_ = v_l_3924_;
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_v_3932_);
lean_inc(v_k_3931_);
lean_dec(v_l_3924_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3936_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3925_, 2);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 4, v_r_3925_);
lean_ctor_set(v___x_3934_, 3, v_r_3925_);
lean_ctor_set(v___x_3934_, 2, v_v_3712_);
lean_ctor_set(v___x_3934_, 1, v_k_3711_);
lean_ctor_set(v___x_3934_, 0, v___x_3871_);
v___x_3938_ = v___x_3934_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_r_3925_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v_r_3925_);
v___x_3938_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
lean_inc(v_r_3925_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 3, v_r_3925_);
lean_ctor_set(v___x_3929_, 0, v___x_3871_);
v___x_3940_ = v___x_3929_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_k_3926_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_v_3927_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_r_3925_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v_r_3925_);
v___x_3940_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3936_);
lean_ctor_set(v___x_3941_, 1, v_k_3931_);
lean_ctor_set(v___x_3941_, 2, v_v_3932_);
lean_ctor_set(v___x_3941_, 3, v___x_3938_);
lean_ctor_set(v___x_3941_, 4, v___x_3940_);
return v___x_3941_;
}
}
}
}
}
else
{
lean_object* v_r_3951_; 
v_r_3951_ = lean_ctor_get(v_impl_3870_, 4);
lean_inc(v_r_3951_);
if (lean_obj_tag(v_r_3951_) == 0)
{
lean_object* v_k_3952_; lean_object* v_v_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3962_; 
v_k_3952_ = lean_ctor_get(v_impl_3870_, 1);
v_v_3953_ = lean_ctor_get(v_impl_3870_, 2);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_impl_3870_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; 
v_unused_3963_ = lean_ctor_get(v_impl_3870_, 4);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_impl_3870_, 3);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_impl_3870_, 0);
lean_dec(v_unused_3965_);
v___x_3955_ = v_impl_3870_;
v_isShared_3956_ = v_isSharedCheck_3962_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_v_3953_);
lean_inc(v_k_3952_);
lean_dec(v_impl_3870_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3962_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3959_; 
v___x_3957_ = lean_unsigned_to_nat(3u);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_l_3924_);
lean_ctor_set(v___x_3955_, 2, v_v_3712_);
lean_ctor_set(v___x_3955_, 1, v_k_3711_);
lean_ctor_set(v___x_3955_, 0, v___x_3871_);
v___x_3959_ = v___x_3955_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_l_3924_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v_l_3924_);
v___x_3959_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3957_);
lean_ctor_set(v___x_3960_, 1, v_k_3952_);
lean_ctor_set(v___x_3960_, 2, v_v_3953_);
lean_ctor_set(v___x_3960_, 3, v___x_3959_);
lean_ctor_set(v___x_3960_, 4, v_r_3951_);
return v___x_3960_;
}
}
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = lean_unsigned_to_nat(2u);
v___x_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
lean_ctor_set(v___x_3967_, 1, v_k_3711_);
lean_ctor_set(v___x_3967_, 2, v_v_3712_);
lean_ctor_set(v___x_3967_, 3, v_r_3951_);
lean_ctor_set(v___x_3967_, 4, v_impl_3870_);
return v___x_3967_;
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
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v_k_3693_);
lean_ctor_set(v___x_3976_, 2, v_v_3694_);
lean_ctor_set(v___x_3976_, 3, v_t_3695_);
lean_ctor_set(v___x_3976_, 4, v_t_3695_);
return v___x_3976_;
}
v___jp_3696_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_nat_add(v___y_3704_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec(v___y_3704_);
v___x_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v___y_3699_);
lean_ctor_set(v___x_3708_, 2, v___y_3703_);
lean_ctor_set(v___x_3708_, 3, v___y_3697_);
lean_ctor_set(v___x_3708_, 4, v___y_3700_);
v___x_3709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3709_, 0, v___y_3698_);
lean_ctor_set(v___x_3709_, 1, v___y_3701_);
lean_ctor_set(v___x_3709_, 2, v___y_3705_);
lean_ctor_set(v___x_3709_, 3, v___y_3702_);
lean_ctor_set(v___x_3709_, 4, v___x_3708_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(lean_object* v_t_3977_, lean_object* v_k_3978_, lean_object* v_fallback_3979_){
_start:
{
if (lean_obj_tag(v_t_3977_) == 0)
{
lean_object* v_k_3980_; lean_object* v_v_3981_; lean_object* v_l_3982_; lean_object* v_r_3983_; uint8_t v___y_3985_; lean_object* v_fst_3988_; lean_object* v_snd_3989_; lean_object* v_fst_3990_; lean_object* v_snd_3991_; uint8_t v___x_3992_; 
v_k_3980_ = lean_ctor_get(v_t_3977_, 1);
v_v_3981_ = lean_ctor_get(v_t_3977_, 2);
v_l_3982_ = lean_ctor_get(v_t_3977_, 3);
v_r_3983_ = lean_ctor_get(v_t_3977_, 4);
v_fst_3988_ = lean_ctor_get(v_k_3978_, 0);
v_snd_3989_ = lean_ctor_get(v_k_3978_, 1);
v_fst_3990_ = lean_ctor_get(v_k_3980_, 0);
v_snd_3991_ = lean_ctor_get(v_k_3980_, 1);
v___x_3992_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_fst_3988_, v_fst_3990_);
if (v___x_3992_ == 1)
{
uint8_t v___x_3993_; 
v___x_3993_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_snd_3989_, v_snd_3991_);
v___y_3985_ = v___x_3993_;
goto v___jp_3984_;
}
else
{
v___y_3985_ = v___x_3992_;
goto v___jp_3984_;
}
v___jp_3984_:
{
switch(v___y_3985_)
{
case 0:
{
v_t_3977_ = v_l_3982_;
goto _start;
}
case 1:
{
lean_inc(v_v_3981_);
return v_v_3981_;
}
default: 
{
v_t_3977_ = v_r_3983_;
goto _start;
}
}
}
}
else
{
lean_inc(v_fallback_3979_);
return v_fallback_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg___boxed(lean_object* v_t_3994_, lean_object* v_k_3995_, lean_object* v_fallback_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_3994_, v_k_3995_, v_fallback_3996_);
lean_dec(v_fallback_3996_);
lean_dec_ref(v_k_3995_);
lean_dec(v_t_3994_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(lean_object* v___x_3998_, lean_object* v_as_3999_, size_t v_sz_4000_, size_t v_i_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_usize_dec_lt(v_i_4001_, v_sz_4000_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v___x_3998_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_b_4002_);
return v___x_4007_;
}
else
{
lean_object* v_a_4008_; lean_object* v_fst_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4037_; 
v_a_4008_ = lean_array_uget(v_as_3999_, v_i_4001_);
v_fst_4009_ = lean_ctor_get(v_a_4008_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_4008_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v_a_4008_, 1);
lean_dec(v_unused_4038_);
v___x_4011_ = v_a_4008_;
v_isShared_4012_ = v_isSharedCheck_4037_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_fst_4009_);
lean_dec(v_a_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4037_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_4009_);
v___x_4014_ = l_Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0(v_fst_4009_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___y_4017_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
if (lean_obj_tag(v_a_4015_) == 0)
{
lean_inc(v___x_3998_);
v___y_4017_ = v___x_3998_;
goto v___jp_4016_;
}
else
{
lean_object* v_val_4028_; 
v_val_4028_ = lean_ctor_get(v_a_4015_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_a_4015_, 1);
v___y_4017_ = v_val_4028_;
goto v___jp_4016_;
}
v___jp_4016_:
{
lean_object* v___x_4019_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 1, v_fst_4009_);
lean_ctor_set(v___x_4011_, 0, v___y_4017_);
v___x_4019_ = v___x_4011_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___y_4017_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_fst_4009_);
v___x_4019_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; size_t v___x_4024_; size_t v___x_4025_; 
v___x_4020_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_b_4002_, v___x_4019_, v___x_4013_);
v___x_4021_ = lean_unsigned_to_nat(1u);
v___x_4022_ = lean_nat_add(v___x_4020_, v___x_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v___x_4019_, v___x_4022_, v_b_4002_);
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_4001_, v___x_4024_);
v_i_4001_ = v___x_4025_;
v_b_4002_ = v___x_4023_;
goto _start;
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_del_object(v___x_4011_);
lean_dec(v_fst_4009_);
lean_dec(v_b_4002_);
lean_dec(v___x_3998_);
v_a_4029_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4014_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4014_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7___boxed(lean_object* v___x_4039_, lean_object* v_as_4040_, lean_object* v_sz_4041_, lean_object* v_i_4042_, lean_object* v_b_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
size_t v_sz_boxed_4047_; size_t v_i_boxed_4048_; lean_object* v_res_4049_; 
v_sz_boxed_4047_ = lean_unbox_usize(v_sz_4041_);
lean_dec(v_sz_4041_);
v_i_boxed_4048_ = lean_unbox_usize(v_i_4042_);
lean_dec(v_i_4042_);
v_res_4049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4039_, v_as_4040_, v_sz_boxed_4047_, v_i_boxed_4048_, v_b_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v_as_4040_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(lean_object* v_fst_4050_, lean_object* v_init_4051_, lean_object* v_x_4052_){
_start:
{
if (lean_obj_tag(v_x_4052_) == 0)
{
lean_object* v_k_4054_; lean_object* v_v_4055_; lean_object* v_l_4056_; lean_object* v_r_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v_a_4060_; lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4077_; 
v_k_4054_ = lean_ctor_get(v_x_4052_, 1);
lean_inc(v_k_4054_);
v_v_4055_ = lean_ctor_get(v_x_4052_, 2);
lean_inc(v_v_4055_);
v_l_4056_ = lean_ctor_get(v_x_4052_, 3);
lean_inc(v_l_4056_);
v_r_4057_ = lean_ctor_get(v_x_4052_, 4);
lean_inc(v_r_4057_);
lean_dec_ref_known(v_x_4052_, 5);
v___x_4058_ = 1;
lean_inc_ref(v_fst_4050_);
v___x_4059_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4050_, v_init_4051_, v_l_4056_);
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref(v___x_4059_);
v_a_4061_ = lean_ctor_get(v_a_4060_, 0);
lean_inc(v_a_4061_);
lean_dec(v_a_4060_);
v_fst_4062_ = lean_ctor_get(v_k_4054_, 0);
v_snd_4063_ = lean_ctor_get(v_k_4054_, 1);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_k_4054_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4065_ = v_k_4054_;
v_isShared_4066_ = v_isSharedCheck_4077_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_snd_4063_);
lean_inc(v_fst_4062_);
lean_dec(v_k_4054_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4077_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v_optName_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v_optName_4067_ = lean_ctor_get(v_fst_4050_, 1);
lean_inc(v_optName_4067_);
v___x_4068_ = l_Lean_Name_toString(v_optName_4067_, v___x_4058_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set_tag(v___x_4065_, 1);
v___x_4070_ = v___x_4065_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4062_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_snd_4063_);
v___x_4070_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
double v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4071_ = lean_float_of_nat(v_v_4055_);
v___x_4072_ = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_float(v___x_4072_, 0, v___x_4071_);
v___x_4073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4068_);
lean_ctor_set(v___x_4073_, 1, v___x_4070_);
lean_ctor_set(v___x_4073_, 2, v___x_4072_);
v___x_4074_ = lean_array_push(v_a_4061_, v___x_4073_);
v_init_4051_ = v___x_4074_;
v_x_4052_ = v_r_4057_;
goto _start;
}
}
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec_ref(v_fst_4050_);
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_init_4051_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg___boxed(lean_object* v_fst_4080_, lean_object* v_init_4081_, lean_object* v_x_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4080_, v_init_4081_, v_x_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(lean_object* v___x_4085_, lean_object* v_as_4086_, size_t v_sz_4087_, size_t v_i_4088_, lean_object* v_b_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_a_4094_; uint8_t v___x_4098_; 
v___x_4098_ = lean_usize_dec_lt(v_i_4088_, v_sz_4087_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; 
lean_dec(v___x_4085_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_b_4089_);
return v___x_4099_;
}
else
{
lean_object* v_a_4100_; lean_object* v_snd_4101_; lean_object* v_fst_4102_; lean_object* v_size_4103_; lean_object* v_buckets_4104_; lean_object* v___x_4105_; lean_object* v___y_4107_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v_a_4100_ = lean_array_uget_borrowed(v_as_4086_, v_i_4088_);
v_snd_4101_ = lean_ctor_get(v_a_4100_, 1);
v_fst_4102_ = lean_ctor_get(v_a_4100_, 0);
v_size_4103_ = lean_ctor_get(v_snd_4101_, 0);
v_buckets_4104_ = lean_ctor_get(v_snd_4101_, 1);
v___x_4105_ = lean_box(1);
v___x_4131_ = lean_mk_empty_array_with_capacity(v_size_4103_);
v___x_4132_ = lean_unsigned_to_nat(0u);
v___x_4133_ = lean_array_get_size(v_buckets_4104_);
v___x_4134_ = lean_nat_dec_lt(v___x_4132_, v___x_4133_);
if (v___x_4134_ == 0)
{
v___y_4107_ = v___x_4131_;
goto v___jp_4106_;
}
else
{
size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = lean_usize_of_nat(v___x_4133_);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__3(v_buckets_4104_, v___x_4135_, v___x_4136_, v___x_4131_);
v___y_4107_ = v___x_4137_;
goto v___jp_4106_;
}
v___jp_4106_:
{
size_t v_sz_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v_sz_4108_ = lean_array_size(v___y_4107_);
v___x_4109_ = ((size_t)0ULL);
lean_inc(v___x_4085_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__7(v___x_4085_, v___y_4107_, v_sz_4108_, v___x_4109_, v___x_4105_, v___y_4090_, v___y_4091_);
lean_dec_ref(v___y_4107_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4112_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4110_, 1);
lean_inc(v_fst_4102_);
v___x_4112_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4102_, v_b_4089_, v_a_4111_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_a_4114_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v_a_4114_ = lean_ctor_get(v_a_4113_, 0);
lean_inc(v_a_4114_);
lean_dec(v_a_4113_);
v_a_4094_ = v_a_4114_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v___x_4085_);
v_a_4115_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4112_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4112_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref(v_b_4089_);
lean_dec(v___x_4085_);
v_a_4123_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4110_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4110_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
v___jp_4093_:
{
size_t v___x_4095_; size_t v___x_4096_; 
v___x_4095_ = ((size_t)1ULL);
v___x_4096_ = lean_usize_add(v_i_4088_, v___x_4095_);
v_i_4088_ = v___x_4096_;
v_b_4089_ = v_a_4094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9___boxed(lean_object* v___x_4138_, lean_object* v_as_4139_, lean_object* v_sz_4140_, lean_object* v_i_4141_, lean_object* v_b_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_sz_boxed_4146_; size_t v_i_boxed_4147_; lean_object* v_res_4148_; 
v_sz_boxed_4146_ = lean_unbox_usize(v_sz_4140_);
lean_dec(v_sz_4140_);
v_i_boxed_4147_ = lean_unbox_usize(v_i_4141_);
lean_dec(v_i_4141_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4138_, v_as_4139_, v_sz_boxed_4146_, v_i_boxed_4147_, v_b_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v_as_4139_);
return v_res_4148_;
}
}
static lean_object* _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = l_Lean_maxRecDepth;
v___x_4156_ = l_Lean_Options_empty;
v___x_4157_ = l_Lean_Option_get___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks_spec__2(v___x_4156_, v___x_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(lean_object* v_args_4158_, lean_object* v_linterOpts_4159_, lean_object* v_sp_4160_, lean_object* v_env_4161_, lean_object* v_mod_4162_){
_start:
{
lean_object* v_a_4165_; lean_object* v_msg_4169_; lean_object* v_a_4174_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; uint16_t v___x_4199_; uint8_t v___x_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v_a_4216_; lean_object* v___y_4220_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; uint8_t v___y_4228_; lean_object* v___y_4229_; uint8_t v___y_4230_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; uint8_t v___y_4303_; lean_object* v___y_4304_; uint8_t v___y_4305_; lean_object* v___y_4315_; lean_object* v___y_4316_; uint8_t v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v_fileName_4345_; lean_object* v_fileMap_4346_; lean_object* v_currNamespace_4347_; lean_object* v_openDecls_4348_; lean_object* v_initHeartbeats_4349_; lean_object* v_maxHeartbeats_4350_; lean_object* v_quotContext_4351_; lean_object* v_currMacroScope_4352_; lean_object* v_cancelTk_x3f_4353_; lean_object* v_inheritedTraceOptions_4354_; lean_object* v_currRecDepth_4355_; lean_object* v_ref_4356_; uint8_t v_suppressElabErrors_4357_; uint8_t v_checkDeprecated_4358_; uint8_t v_isRecordingDeps_4359_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; uint8_t v___y_4381_; lean_object* v_env_4402_; uint8_t v___x_4403_; uint8_t v___x_4404_; 
v___x_4188_ = l_Lean_Name_getRoot(v_mod_4162_);
v___x_4189_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4190_ = l_Lean_instInhabitedFileMap_default;
v___x_4191_ = l_Lean_Options_empty;
v___x_4192_ = lean_box(0);
v___x_4193_ = lean_box(0);
v___x_4194_ = lean_unsigned_to_nat(0u);
v___x_4195_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4196_ = l_Lean_firstFrontendMacroScope;
v___x_4197_ = lean_box(0);
v___x_4198_ = lean_box(0);
v___x_4199_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4200_ = 0;
v___x_4201_ = 0;
v___x_4202_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4203_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4204_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4205_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4206_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4208_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4209_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4210_ = 1;
v___x_4211_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4212_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4212_, 0, v_env_4161_);
lean_ctor_set(v___x_4212_, 1, v___x_4202_);
lean_ctor_set(v___x_4212_, 2, v___x_4203_);
lean_ctor_set(v___x_4212_, 3, v___x_4204_);
lean_ctor_set(v___x_4212_, 4, v___x_4205_);
lean_ctor_set(v___x_4212_, 5, v___x_4206_);
lean_ctor_set(v___x_4212_, 6, v___x_4208_);
lean_ctor_set(v___x_4212_, 7, v___x_4209_);
lean_ctor_set(v___x_4212_, 8, v___x_4211_);
lean_ctor_set(v___x_4212_, 9, v___x_4207_);
v___x_4213_ = lean_io_get_num_heartbeats();
v___x_4214_ = lean_st_mk_ref(v___x_4212_);
v___x_4377_ = l_Lean_inheritedTraceOptions;
v___x_4378_ = lean_st_ref_get(v___x_4377_);
v___x_4379_ = lean_st_ref_get(v___x_4214_);
v_env_4402_ = lean_ctor_get(v___x_4379_, 0);
lean_inc_ref(v_env_4402_);
lean_dec(v___x_4379_);
v___x_4403_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4402_);
lean_dec_ref(v_env_4402_);
v___x_4404_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4404_ == 0)
{
if (v___x_4403_ == 0)
{
v___y_4381_ = v___x_4210_;
goto v___jp_4380_;
}
else
{
v_fileName_4345_ = v___x_4189_;
v_fileMap_4346_ = v___x_4190_;
v_currNamespace_4347_ = v___x_4192_;
v_openDecls_4348_ = v___x_4193_;
v_initHeartbeats_4349_ = v___x_4213_;
v_maxHeartbeats_4350_ = v___x_4195_;
v_quotContext_4351_ = v___x_4192_;
v_currMacroScope_4352_ = v___x_4196_;
v_cancelTk_x3f_4353_ = v___x_4197_;
v_inheritedTraceOptions_4354_ = v___x_4378_;
v_currRecDepth_4355_ = v___x_4194_;
v_ref_4356_ = v___x_4198_;
v_suppressElabErrors_4357_ = v___x_4200_;
v_checkDeprecated_4358_ = v___x_4201_;
v_isRecordingDeps_4359_ = v___x_4200_;
goto v___jp_4344_;
}
}
else
{
if (v___x_4403_ == 0)
{
v_fileName_4345_ = v___x_4189_;
v_fileMap_4346_ = v___x_4190_;
v_currNamespace_4347_ = v___x_4192_;
v_openDecls_4348_ = v___x_4193_;
v_initHeartbeats_4349_ = v___x_4213_;
v_maxHeartbeats_4350_ = v___x_4195_;
v_quotContext_4351_ = v___x_4192_;
v_currMacroScope_4352_ = v___x_4196_;
v_cancelTk_x3f_4353_ = v___x_4197_;
v_inheritedTraceOptions_4354_ = v___x_4378_;
v_currRecDepth_4355_ = v___x_4194_;
v_ref_4356_ = v___x_4198_;
v_suppressElabErrors_4357_ = v___x_4200_;
v_checkDeprecated_4358_ = v___x_4201_;
v_isRecordingDeps_4359_ = v___x_4200_;
goto v___jp_4344_;
}
else
{
v___y_4381_ = v___x_4200_;
goto v___jp_4380_;
}
}
v___jp_4164_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_mk_io_user_error(v_a_4165_);
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
v___jp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = l_Lean_MessageData_toString(v_msg_4169_);
v___x_4171_ = lean_mk_io_user_error(v___x_4170_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
v___jp_4173_:
{
if (lean_obj_tag(v_a_4174_) == 0)
{
lean_object* v_msg_4175_; 
v_msg_4175_ = lean_ctor_get(v_a_4174_, 1);
lean_inc_ref(v_msg_4175_);
lean_dec_ref_known(v_a_4174_, 2);
v_msg_4169_ = v_msg_4175_;
goto v___jp_4168_;
}
else
{
lean_object* v_id_4176_; lean_object* v___x_4177_; 
v_id_4176_ = lean_ctor_get(v_a_4174_, 0);
lean_inc(v_id_4176_);
lean_dec_ref_known(v_a_4174_, 2);
v___x_4177_ = l_Lean_InternalExceptionId_getName(v_id_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec(v_id_4176_);
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v___x_4179_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4180_ = 1;
v___x_4181_ = l_Lean_Name_toString(v_a_4178_, v___x_4180_);
v___x_4182_ = lean_string_append(v___x_4179_, v___x_4181_);
lean_dec_ref(v___x_4181_);
v_a_4165_ = v___x_4182_;
goto v___jp_4164_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec_ref_known(v___x_4177_, 1);
v___x_4183_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4184_ = l_Nat_reprFast(v_id_4176_);
v___x_4185_ = lean_string_append(v___x_4183_, v___x_4184_);
lean_dec_ref(v___x_4184_);
v___x_4186_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4187_ = lean_string_append(v___x_4185_, v___x_4186_);
v_a_4165_ = v___x_4187_;
goto v___jp_4164_;
}
}
}
v___jp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_st_ref_get(v___x_4214_);
lean_dec(v___x_4214_);
lean_dec(v___x_4217_);
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v_a_4216_);
return v___x_4218_;
}
v___jp_4219_:
{
lean_object* v_a_4221_; 
v_a_4221_ = lean_ctor_get(v___y_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref(v___y_4220_);
v_a_4216_ = v_a_4221_;
goto v___jp_4215_;
}
v___jp_4222_:
{
switch(v___y_4228_)
{
case 0:
{
lean_dec(v_sp_4160_);
if (v___y_4230_ == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4224_);
lean_dec_ref(v___y_4223_);
v___x_4231_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__0));
v___x_4232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4162_, v___x_4210_);
v___x_4233_ = lean_string_append(v___x_4231_, v___x_4232_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4235_ = lean_string_append(v___x_4233_, v___x_4234_);
v___x_4236_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4235_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4230_, v_a_4237_, v___y_4227_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4227_);
v___y_4220_ = v___x_4238_;
goto v___jp_4219_;
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4225_);
lean_dec(v___x_4214_);
v_a_4239_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4241_ = v___x_4236_;
v_isShared_4242_ = v_isSharedCheck_4248_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4236_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4248_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4243_ = lean_io_error_to_string(v_a_4239_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 3);
lean_ctor_set(v___x_4241_, 0, v___x_4243_);
v___x_4245_ = v___x_4241_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_MessageData_ofFormat(v___x_4245_);
v_msg_4169_ = v___x_4246_;
goto v___jp_4168_;
}
}
}
}
else
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4249_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__2));
v___x_4250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4162_, v___y_4230_);
v___x_4251_ = lean_string_append(v___x_4249_, v___x_4250_);
lean_dec_ref(v___x_4250_);
v___x_4252_ = lean_array_get_size(v___y_4224_);
lean_dec_ref(v___y_4224_);
v___x_4253_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_4223_, v___y_4229_, v___x_4210_, v___x_4251_, v___x_4252_, v___x_4210_, v___y_4227_, v___y_4225_);
lean_dec_ref(v___y_4229_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = l_Lean_MessageData_toString(v_a_4254_);
v___x_4256_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4255_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
v___x_4258_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___lam__0(v___y_4230_, v_a_4257_, v___y_4227_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4227_);
v___y_4220_ = v___x_4258_;
goto v___jp_4219_;
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4225_);
lean_dec(v___x_4214_);
v_a_4259_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4261_ = v___x_4256_;
v_isShared_4262_ = v_isSharedCheck_4268_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4256_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4268_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
v___x_4263_ = lean_io_error_to_string(v_a_4259_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set_tag(v___x_4261_, 3);
lean_ctor_set(v___x_4261_, 0, v___x_4263_);
v___x_4265_ = v___x_4261_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_MessageData_ofFormat(v___x_4265_);
v_msg_4169_ = v___x_4266_;
goto v___jp_4168_;
}
}
}
}
else
{
lean_object* v_a_4269_; 
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4225_);
lean_dec(v___x_4214_);
v_a_4269_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4253_, 1);
v_a_4174_ = v_a_4269_;
goto v___jp_4173_;
}
}
}
case 1:
{
lean_object* v___x_4270_; lean_object* v_env_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; size_t v_sz_4275_; size_t v___x_4276_; lean_object* v___x_4277_; 
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4224_);
lean_dec(v_mod_4162_);
v___x_4270_ = lean_st_ref_get(v___y_4225_);
v_env_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc_ref(v_env_4271_);
lean_dec(v___x_4270_);
v___x_4272_ = l_Lean_Environment_mainModule(v_env_4271_);
lean_dec_ref(v_env_4271_);
v___x_4273_ = lean_box(v___y_4226_);
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4207_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v_sz_4275_ = lean_array_size(v___y_4223_);
v___x_4276_ = ((size_t)0ULL);
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__4(v_sp_4160_, v___x_4272_, v___y_4223_, v_sz_4275_, v___x_4276_, v___x_4274_, v___y_4227_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4227_);
lean_dec_ref(v___y_4223_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v_fst_4279_; lean_object* v_snd_4280_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v_fst_4279_ = lean_ctor_get(v_a_4278_, 0);
lean_inc(v_fst_4279_);
v_snd_4280_ = lean_ctor_get(v_a_4278_, 1);
lean_inc(v_snd_4280_);
lean_dec(v_a_4278_);
v___x_4281_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_4281_, 0, v_fst_4279_);
v___x_4282_ = lean_unbox(v_snd_4280_);
lean_dec(v_snd_4280_);
lean_ctor_set_uint8(v___x_4281_, sizeof(void*)*1, v___x_4282_);
v_a_4216_ = v___x_4281_;
goto v___jp_4215_;
}
else
{
lean_object* v_a_4283_; 
lean_dec(v___x_4214_);
v_a_4283_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4277_, 1);
v_a_4174_ = v_a_4283_;
goto v___jp_4173_;
}
}
default: 
{
lean_object* v___x_4284_; lean_object* v_env_4285_; lean_object* v___x_4286_; size_t v_sz_4287_; size_t v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4224_);
lean_dec(v_mod_4162_);
lean_dec(v_sp_4160_);
v___x_4284_ = lean_st_ref_get(v___y_4225_);
v_env_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc_ref(v_env_4285_);
lean_dec(v___x_4284_);
v___x_4286_ = l_Lean_Environment_mainModule(v_env_4285_);
lean_dec_ref(v_env_4285_);
v_sz_4287_ = lean_array_size(v___y_4223_);
v___x_4288_ = ((size_t)0ULL);
v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__9(v___x_4286_, v___y_4223_, v_sz_4287_, v___x_4288_, v___x_4207_, v___y_4227_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4227_);
lean_dec_ref(v___y_4223_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 2);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
v_a_4216_ = v___x_4295_;
goto v___jp_4215_;
}
}
}
else
{
lean_object* v_a_4298_; 
lean_dec(v___x_4214_);
v_a_4298_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4289_, 1);
v_a_4174_ = v_a_4298_;
goto v___jp_4173_;
}
}
}
}
v___jp_4299_:
{
lean_object* v___x_4306_; 
lean_inc_ref(v___y_4300_);
v___x_4306_ = l_Lean_Linter_EnvLinter_lintCore(v___y_4304_, v___y_4300_, v___y_4302_, v___y_4301_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = lean_array_get_size(v_a_4307_);
v___x_4309_ = lean_nat_dec_lt(v___x_4194_, v___x_4308_);
if (v___x_4309_ == 0)
{
v___y_4223_ = v_a_4307_;
v___y_4224_ = v___y_4300_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___y_4305_;
v___y_4227_ = v___y_4302_;
v___y_4228_ = v___y_4303_;
v___y_4229_ = v___y_4304_;
v___y_4230_ = v___x_4309_;
goto v___jp_4222_;
}
else
{
if (v___x_4309_ == 0)
{
v___y_4223_ = v_a_4307_;
v___y_4224_ = v___y_4300_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___y_4305_;
v___y_4227_ = v___y_4302_;
v___y_4228_ = v___y_4303_;
v___y_4229_ = v___y_4304_;
v___y_4230_ = v___x_4309_;
goto v___jp_4222_;
}
else
{
size_t v___x_4310_; size_t v___x_4311_; uint8_t v___x_4312_; 
v___x_4310_ = ((size_t)0ULL);
v___x_4311_ = lean_usize_of_nat(v___x_4308_);
v___x_4312_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__10(v___y_4305_, v_a_4307_, v___x_4310_, v___x_4311_);
v___y_4223_ = v_a_4307_;
v___y_4224_ = v___y_4300_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___y_4305_;
v___y_4227_ = v___y_4302_;
v___y_4228_ = v___y_4303_;
v___y_4229_ = v___y_4304_;
v___y_4230_ = v___x_4312_;
goto v___jp_4222_;
}
}
}
else
{
lean_object* v_a_4313_; 
lean_dec_ref(v___y_4304_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___x_4214_);
lean_dec(v_mod_4162_);
lean_dec(v_sp_4160_);
v_a_4313_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4306_, 1);
v_a_4174_ = v_a_4313_;
goto v___jp_4173_;
}
}
v___jp_4314_:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_4319_, v___y_4316_, v___y_4315_);
lean_dec(v___y_4319_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4320_, 1);
v___x_4322_ = lean_array_get_size(v_a_4321_);
v___x_4323_ = lean_nat_dec_eq(v___x_4322_, v___x_4194_);
if (v___x_4323_ == 0)
{
v___y_4300_ = v_a_4321_;
v___y_4301_ = v___y_4315_;
v___y_4302_ = v___y_4316_;
v___y_4303_ = v___y_4317_;
v___y_4304_ = v___y_4318_;
v___y_4305_ = v___x_4323_;
goto v___jp_4299_;
}
else
{
uint8_t v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = 0;
v___x_4325_ = l_Lake_BuiltinLint_instBEqMode_beq(v___y_4317_, v___x_4324_);
if (v___x_4325_ == 0)
{
v___y_4300_ = v_a_4321_;
v___y_4301_ = v___y_4315_;
v___y_4302_ = v___y_4316_;
v___y_4303_ = v___y_4317_;
v___y_4304_ = v___y_4318_;
v___y_4305_ = v___x_4325_;
goto v___jp_4299_;
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
lean_dec(v_a_4321_);
lean_dec_ref(v___y_4318_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v_sp_4160_);
v___x_4326_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__3));
v___x_4327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_4162_, v___x_4325_);
v___x_4328_ = lean_string_append(v___x_4326_, v___x_4327_);
lean_dec_ref(v___x_4327_);
v___x_4329_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__1));
v___x_4330_ = lean_string_append(v___x_4328_, v___x_4329_);
v___x_4331_ = l_IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13(v___x_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v___x_4332_; 
lean_dec_ref_known(v___x_4331_, 1);
v___x_4332_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__4));
v_a_4216_ = v___x_4332_;
goto v___jp_4215_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v___x_4214_);
v_a_4333_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4335_ = v___x_4331_;
v_isShared_4336_ = v_isSharedCheck_4342_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4331_);
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
v_msg_4169_ = v___x_4340_;
goto v___jp_4168_;
}
}
}
}
}
}
else
{
lean_object* v_a_4343_; 
lean_dec_ref(v___y_4318_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v___x_4214_);
lean_dec(v_mod_4162_);
lean_dec(v_sp_4160_);
v_a_4343_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4320_, 1);
v_a_4174_ = v_a_4343_;
goto v___jp_4173_;
}
}
v___jp_4344_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4360_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_currMacroScope_4352_);
lean_inc(v_quotContext_4351_);
lean_inc(v_maxHeartbeats_4350_);
lean_inc(v_openDecls_4348_);
lean_inc(v_currNamespace_4347_);
lean_inc_ref(v_fileMap_4346_);
lean_inc_ref(v_fileName_4345_);
v___x_4361_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4361_, 0, v_fileName_4345_);
lean_ctor_set(v___x_4361_, 1, v_fileMap_4346_);
lean_ctor_set(v___x_4361_, 2, v___x_4191_);
lean_ctor_set(v___x_4361_, 3, v___x_4360_);
lean_ctor_set(v___x_4361_, 4, v_currNamespace_4347_);
lean_ctor_set(v___x_4361_, 5, v_openDecls_4348_);
lean_ctor_set(v___x_4361_, 6, v_initHeartbeats_4349_);
lean_ctor_set(v___x_4361_, 7, v_maxHeartbeats_4350_);
lean_ctor_set(v___x_4361_, 8, v_quotContext_4351_);
lean_ctor_set(v___x_4361_, 9, v_currMacroScope_4352_);
lean_ctor_set(v___x_4361_, 10, v_cancelTk_x3f_4353_);
lean_ctor_set(v___x_4361_, 11, v_inheritedTraceOptions_4354_);
lean_inc(v_ref_4356_);
v___x_4362_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
lean_ctor_set(v___x_4362_, 1, v_currRecDepth_4355_);
lean_ctor_set(v___x_4362_, 2, v_ref_4356_);
lean_ctor_set_uint16(v___x_4362_, sizeof(void*)*3, v___x_4199_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*3 + 2, v_suppressElabErrors_4357_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*3 + 3, v_checkDeprecated_4358_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*3 + 4, v_isRecordingDeps_4359_);
v___x_4363_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_4188_, v___x_4214_);
lean_dec(v___x_4188_);
if (lean_obj_tag(v___x_4363_) == 0)
{
uint8_t v_lintOnly_4364_; 
v_lintOnly_4364_ = lean_ctor_get_uint8(v_args_4158_, sizeof(void*)*4);
if (v_lintOnly_4364_ == 0)
{
lean_object* v_a_4365_; uint8_t v_mode_4366_; 
lean_dec_ref(v_linterOpts_4159_);
v_a_4365_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4363_, 1);
v_mode_4366_ = lean_ctor_get_uint8(v_args_4158_, sizeof(void*)*4 + 1);
lean_inc(v___x_4214_);
v___y_4315_ = v___x_4214_;
v___y_4316_ = v___x_4362_;
v___y_4317_ = v_mode_4366_;
v___y_4318_ = v_a_4365_;
v___y_4319_ = v___x_4197_;
goto v___jp_4314_;
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4375_; 
v_a_4367_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4369_ = v___x_4363_;
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4363_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
uint8_t v_mode_4371_; lean_object* v___x_4373_; 
v_mode_4371_ = lean_ctor_get_uint8(v_args_4158_, sizeof(void*)*4 + 1);
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 1);
lean_ctor_set(v___x_4369_, 0, v_linterOpts_4159_);
v___x_4373_ = v___x_4369_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_linterOpts_4159_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_inc(v___x_4214_);
v___y_4315_ = v___x_4214_;
v___y_4316_ = v___x_4362_;
v___y_4317_ = v_mode_4371_;
v___y_4318_ = v_a_4367_;
v___y_4319_ = v___x_4373_;
goto v___jp_4314_;
}
}
}
}
else
{
lean_object* v_a_4376_; 
lean_dec_ref_known(v___x_4362_, 3);
lean_dec(v___x_4214_);
lean_dec(v_mod_4162_);
lean_dec(v_sp_4160_);
lean_dec_ref(v_linterOpts_4159_);
v_a_4376_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4363_, 1);
v_a_4174_ = v_a_4376_;
goto v___jp_4173_;
}
}
v___jp_4380_:
{
lean_object* v___x_4382_; lean_object* v_env_4383_; lean_object* v_nextMacroScope_4384_; lean_object* v_ngen_4385_; lean_object* v_auxDeclNGen_4386_; lean_object* v_traceState_4387_; lean_object* v_recordedDeps_4388_; lean_object* v_messages_4389_; lean_object* v_infoState_4390_; lean_object* v_snapshotTasks_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4400_; 
v___x_4382_ = lean_st_ref_take(v___x_4214_);
v_env_4383_ = lean_ctor_get(v___x_4382_, 0);
v_nextMacroScope_4384_ = lean_ctor_get(v___x_4382_, 1);
v_ngen_4385_ = lean_ctor_get(v___x_4382_, 2);
v_auxDeclNGen_4386_ = lean_ctor_get(v___x_4382_, 3);
v_traceState_4387_ = lean_ctor_get(v___x_4382_, 4);
v_recordedDeps_4388_ = lean_ctor_get(v___x_4382_, 6);
v_messages_4389_ = lean_ctor_get(v___x_4382_, 7);
v_infoState_4390_ = lean_ctor_get(v___x_4382_, 8);
v_snapshotTasks_4391_ = lean_ctor_get(v___x_4382_, 9);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4382_, 5);
lean_dec(v_unused_4401_);
v___x_4393_ = v___x_4382_;
v_isShared_4394_ = v_isSharedCheck_4400_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_snapshotTasks_4391_);
lean_inc(v_infoState_4390_);
lean_inc(v_messages_4389_);
lean_inc(v_recordedDeps_4388_);
lean_inc(v_traceState_4387_);
lean_inc(v_auxDeclNGen_4386_);
lean_inc(v_ngen_4385_);
lean_inc(v_nextMacroScope_4384_);
lean_inc(v_env_4383_);
lean_dec(v___x_4382_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4400_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4395_ = l_Lean_Kernel_enableDiag(v_env_4383_, v___y_4381_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 5, v___x_4206_);
lean_ctor_set(v___x_4393_, 0, v___x_4395_);
v___x_4397_ = v___x_4393_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_nextMacroScope_4384_);
lean_ctor_set(v_reuseFailAlloc_4399_, 2, v_ngen_4385_);
lean_ctor_set(v_reuseFailAlloc_4399_, 3, v_auxDeclNGen_4386_);
lean_ctor_set(v_reuseFailAlloc_4399_, 4, v_traceState_4387_);
lean_ctor_set(v_reuseFailAlloc_4399_, 5, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4399_, 6, v_recordedDeps_4388_);
lean_ctor_set(v_reuseFailAlloc_4399_, 7, v_messages_4389_);
lean_ctor_set(v_reuseFailAlloc_4399_, 8, v_infoState_4390_);
lean_ctor_set(v_reuseFailAlloc_4399_, 9, v_snapshotTasks_4391_);
v___x_4397_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_st_ref_put(v___x_4214_, v___x_4397_);
v_fileName_4345_ = v___x_4189_;
v_fileMap_4346_ = v___x_4190_;
v_currNamespace_4347_ = v___x_4192_;
v_openDecls_4348_ = v___x_4193_;
v_initHeartbeats_4349_ = v___x_4213_;
v_maxHeartbeats_4350_ = v___x_4195_;
v_quotContext_4351_ = v___x_4192_;
v_currMacroScope_4352_ = v___x_4196_;
v_cancelTk_x3f_4353_ = v___x_4197_;
v_inheritedTraceOptions_4354_ = v___x_4378_;
v_currRecDepth_4355_ = v___x_4194_;
v_ref_4356_ = v___x_4198_;
v_suppressElabErrors_4357_ = v___x_4200_;
v_checkDeprecated_4358_ = v___x_4201_;
v_isRecordingDeps_4359_ = v___x_4200_;
goto v___jp_4344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___boxed(lean_object* v_args_4405_, lean_object* v_linterOpts_4406_, lean_object* v_sp_4407_, lean_object* v_env_4408_, lean_object* v_mod_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4405_, v_linterOpts_4406_, v_sp_4407_, v_env_4408_, v_mod_4409_);
lean_dec_ref(v_args_4405_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(lean_object* v_00_u03b4_4412_, lean_object* v_t_4413_, lean_object* v_k_4414_, lean_object* v_fallback_4415_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___redArg(v_t_4413_, v_k_4414_, v_fallback_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5___boxed(lean_object* v_00_u03b4_4417_, lean_object* v_t_4418_, lean_object* v_k_4419_, lean_object* v_fallback_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__5(v_00_u03b4_4417_, v_t_4418_, v_k_4419_, v_fallback_4420_);
lean_dec(v_fallback_4420_);
lean_dec_ref(v_k_4419_);
lean_dec(v_t_4418_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6(lean_object* v_00_u03b2_4422_, lean_object* v_k_4423_, lean_object* v_v_4424_, lean_object* v_t_4425_, lean_object* v_hl_4426_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__6___redArg(v_k_4423_, v_v_4424_, v_t_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(lean_object* v_fst_4428_, lean_object* v_init_4429_, lean_object* v_x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___redArg(v_fst_4428_, v_init_4429_, v_x_4430_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8___boxed(lean_object* v_fst_4435_, lean_object* v_init_4436_, lean_object* v_x_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__8(v_fst_4435_, v_init_4436_, v_x_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4442_, lean_object* v_constName_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___redArg(v_constName_4443_, v___y_4444_, v___y_4445_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4448_, lean_object* v_constName_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1(v_00_u03b1_4448_, v_constName_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b1_4454_, lean_object* v_ref_4455_, lean_object* v_constName_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___redArg(v_ref_4455_, v_constName_4456_, v___y_4457_, v___y_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b1_4461_, lean_object* v_ref_4462_, lean_object* v_constName_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12(v_00_u03b1_4461_, v_ref_4462_, v_constName_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v_ref_4462_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(lean_object* v_00_u03b1_4468_, lean_object* v_ref_4469_, lean_object* v_msg_4470_, lean_object* v_declHint_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___redArg(v_ref_4469_, v_msg_4470_, v_declHint_4471_, v___y_4472_, v___y_4473_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13___boxed(lean_object* v_00_u03b1_4476_, lean_object* v_ref_4477_, lean_object* v_msg_4478_, lean_object* v_declHint_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13(v_00_u03b1_4476_, v_ref_4477_, v_msg_4478_, v_declHint_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v_ref_4477_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(lean_object* v_msg_4484_, lean_object* v_declHint_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___redArg(v_msg_4484_, v_declHint_4485_, v___y_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15___boxed(lean_object* v_msg_4490_, lean_object* v_declHint_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__14_spec__15(v_msg_4490_, v_declHint_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(lean_object* v_00_u03b1_4496_, lean_object* v_ref_4497_, lean_object* v_msg_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___redArg(v_ref_4497_, v_msg_4498_, v___y_4499_, v___y_4500_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15___boxed(lean_object* v_00_u03b1_4503_, lean_object* v_ref_4504_, lean_object* v_msg_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15(v_00_u03b1_4503_, v_ref_4504_, v_msg_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v_ref_4504_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(lean_object* v_00_u03b1_4510_, lean_object* v_msg_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___redArg(v_msg_4511_, v___y_4512_, v___y_4513_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17___boxed(lean_object* v_00_u03b1_4516_, lean_object* v_msg_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters_spec__0_spec__0_spec__1_spec__12_spec__13_spec__15_spec__17(v_00_u03b1_4516_, v_msg_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(lean_object* v_s_4522_){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; uint32_t v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4524_ = l_Std_Format_defWidth;
v___x_4525_ = lean_unsigned_to_nat(0u);
v___x_4526_ = l_Std_Format_pretty(v_s_4522_, v___x_4524_, v___x_4525_, v___x_4525_);
v___x_4527_ = 10;
v___x_4528_ = lean_string_push(v___x_4526_, v___x_4527_);
v___x_4529_ = l_IO_eprint___at___00IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17_spec__29(v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0___boxed(lean_object* v_s_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v_s_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(lean_object* v_as_4533_, size_t v_sz_4534_, size_t v_i_4535_, lean_object* v_b_4536_, lean_object* v___y_4537_){
_start:
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_usize_dec_lt(v_i_4535_, v_sz_4534_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_b_4536_);
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; lean_object* v_a_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v_ref_4545_; lean_object* v___x_4546_; 
v___x_4541_ = lean_box(0);
v_a_4542_ = lean_array_uget_borrowed(v_as_4533_, v_i_4535_);
v___x_4543_ = lean_box(0);
lean_inc(v_a_4542_);
v___x_4544_ = l_Lean_MessageData_format(v_a_4542_, v___x_4543_);
v_ref_4545_ = lean_ctor_get(v___y_4537_, 2);
v___x_4546_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__0(v___x_4544_);
if (lean_obj_tag(v___x_4546_) == 0)
{
size_t v___x_4547_; size_t v___x_4548_; 
lean_dec_ref_known(v___x_4546_, 1);
v___x_4547_ = ((size_t)1ULL);
v___x_4548_ = lean_usize_add(v_i_4535_, v___x_4547_);
v_i_4535_ = v___x_4548_;
v_b_4536_ = v___x_4541_;
goto _start;
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4561_; 
v_a_4550_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4552_ = v___x_4546_;
v_isShared_4553_ = v_isSharedCheck_4561_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4546_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4561_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
v___x_4554_ = lean_io_error_to_string(v_a_4550_);
v___x_4555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
v___x_4556_ = l_Lean_MessageData_ofFormat(v___x_4555_);
lean_inc(v_ref_4545_);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v_ref_4545_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4557_);
v___x_4559_ = v___x_4552_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg___boxed(lean_object* v_as_4562_, lean_object* v_sz_4563_, lean_object* v_i_4564_, lean_object* v_b_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
size_t v_sz_boxed_4568_; size_t v_i_boxed_4569_; lean_object* v_res_4570_; 
v_sz_boxed_4568_ = lean_unbox_usize(v_sz_4563_);
lean_dec(v_sz_4563_);
v_i_boxed_4569_ = lean_unbox_usize(v_i_4564_);
lean_dec(v_i_4564_);
v_res_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4562_, v_sz_boxed_4568_, v_i_boxed_4569_, v_b_4565_, v___y_4566_);
lean_dec_ref(v___y_4566_);
lean_dec_ref(v_as_4562_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(lean_object* v_errors_4571_, lean_object* v_entries_4572_, lean_object* v_____r_4573_, uint8_t v_anyFailed_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___x_4578_; size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v___x_4578_ = lean_box(0);
v_sz_4579_ = lean_array_size(v_errors_4571_);
v___x_4580_ = ((size_t)0ULL);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_errors_4571_, v_sz_4579_, v___x_4580_, v___x_4578_, v___y_4575_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4590_; 
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; 
v_unused_4591_ = lean_ctor_get(v___x_4581_, 0);
lean_dec(v_unused_4591_);
v___x_4583_ = v___x_4581_;
v_isShared_4584_ = v_isSharedCheck_4590_;
goto v_resetjp_4582_;
}
else
{
lean_dec(v___x_4581_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4590_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v___x_4585_ = lean_box(v_anyFailed_4574_);
v___x_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4586_, 0, v_entries_4572_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4586_);
v___x_4588_ = v___x_4583_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec_ref(v_entries_4572_);
v_a_4592_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4581_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4581_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0___boxed(lean_object* v_errors_4600_, lean_object* v_entries_4601_, lean_object* v_____r_4602_, lean_object* v_anyFailed_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
uint8_t v_anyFailed_boxed_4607_; lean_object* v_res_4608_; 
v_anyFailed_boxed_4607_ = lean_unbox(v_anyFailed_4603_);
v_res_4608_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4600_, v_entries_4601_, v_____r_4602_, v_anyFailed_boxed_4607_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v_errors_4600_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(lean_object* v_sp_4609_, lean_object* v_env_4610_, lean_object* v_mod_4611_){
_start:
{
lean_object* v_a_4614_; lean_object* v_a_4618_; uint8_t v_anyFailed_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; uint16_t v___x_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___y_4664_; lean_object* v_fileName_4680_; lean_object* v_fileMap_4681_; lean_object* v_currNamespace_4682_; lean_object* v_openDecls_4683_; lean_object* v_initHeartbeats_4684_; lean_object* v_maxHeartbeats_4685_; lean_object* v_quotContext_4686_; lean_object* v_currMacroScope_4687_; lean_object* v_cancelTk_x3f_4688_; lean_object* v_inheritedTraceOptions_4689_; lean_object* v_currRecDepth_4690_; lean_object* v_ref_4691_; uint8_t v_suppressElabErrors_4692_; uint8_t v_checkDeprecated_4693_; uint8_t v_isRecordingDeps_4694_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___y_4717_; lean_object* v_env_4738_; uint8_t v___x_4739_; uint8_t v___x_4740_; 
v_anyFailed_4635_ = 0;
v___x_4636_ = ((lean_object*)(l_Lake_BuiltinLint_instInhabitedExceptionRecord_default___closed__0));
v___x_4637_ = l_Lean_instInhabitedFileMap_default;
v___x_4638_ = l_Lean_Options_empty;
v___x_4639_ = lean_box(0);
v___x_4640_ = lean_box(0);
v___x_4641_ = lean_unsigned_to_nat(0u);
v___x_4642_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__5);
v___x_4643_ = l_Lean_firstFrontendMacroScope;
v___x_4644_ = lean_box(0);
v___x_4645_ = lean_box(0);
v___x_4646_ = lean_uint16_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__6);
v___x_4647_ = 0;
v___x_4648_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__7);
v___x_4649_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__10));
v___x_4650_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__11));
v___x_4651_ = lean_unsigned_to_nat(32u);
v___x_4652_ = lean_mk_empty_array_with_capacity(v___x_4651_);
lean_dec_ref(v___x_4652_);
v___x_4653_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__14);
v___x_4654_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__17);
v___x_4655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__6___closed__0));
v___x_4656_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__18);
v___x_4657_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__19);
v___x_4658_ = 1;
v___x_4659_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__20);
v___x_4660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4660_, 0, v_env_4610_);
lean_ctor_set(v___x_4660_, 1, v___x_4648_);
lean_ctor_set(v___x_4660_, 2, v___x_4649_);
lean_ctor_set(v___x_4660_, 3, v___x_4650_);
lean_ctor_set(v___x_4660_, 4, v___x_4653_);
lean_ctor_set(v___x_4660_, 5, v___x_4654_);
lean_ctor_set(v___x_4660_, 6, v___x_4656_);
lean_ctor_set(v___x_4660_, 7, v___x_4657_);
lean_ctor_set(v___x_4660_, 8, v___x_4659_);
lean_ctor_set(v___x_4660_, 9, v___x_4655_);
v___x_4661_ = lean_io_get_num_heartbeats();
v___x_4662_ = lean_st_mk_ref(v___x_4660_);
v___x_4713_ = l_Lean_inheritedTraceOptions;
v___x_4714_ = lean_st_ref_get(v___x_4713_);
v___x_4715_ = lean_st_ref_get(v___x_4662_);
v_env_4738_ = lean_ctor_get(v___x_4715_, 0);
lean_inc_ref(v_env_4738_);
lean_dec(v___x_4715_);
v___x_4739_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4738_);
lean_dec_ref(v_env_4738_);
v___x_4740_ = lean_uint8_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__22);
if (v___x_4740_ == 0)
{
if (v___x_4739_ == 0)
{
v___y_4717_ = v___x_4658_;
goto v___jp_4716_;
}
else
{
v_fileName_4680_ = v___x_4636_;
v_fileMap_4681_ = v___x_4637_;
v_currNamespace_4682_ = v___x_4639_;
v_openDecls_4683_ = v___x_4640_;
v_initHeartbeats_4684_ = v___x_4661_;
v_maxHeartbeats_4685_ = v___x_4642_;
v_quotContext_4686_ = v___x_4639_;
v_currMacroScope_4687_ = v___x_4643_;
v_cancelTk_x3f_4688_ = v___x_4644_;
v_inheritedTraceOptions_4689_ = v___x_4714_;
v_currRecDepth_4690_ = v___x_4641_;
v_ref_4691_ = v___x_4645_;
v_suppressElabErrors_4692_ = v_anyFailed_4635_;
v_checkDeprecated_4693_ = v___x_4647_;
v_isRecordingDeps_4694_ = v_anyFailed_4635_;
goto v___jp_4679_;
}
}
else
{
if (v___x_4739_ == 0)
{
v_fileName_4680_ = v___x_4636_;
v_fileMap_4681_ = v___x_4637_;
v_currNamespace_4682_ = v___x_4639_;
v_openDecls_4683_ = v___x_4640_;
v_initHeartbeats_4684_ = v___x_4661_;
v_maxHeartbeats_4685_ = v___x_4642_;
v_quotContext_4686_ = v___x_4639_;
v_currMacroScope_4687_ = v___x_4643_;
v_cancelTk_x3f_4688_ = v___x_4644_;
v_inheritedTraceOptions_4689_ = v___x_4714_;
v_currRecDepth_4690_ = v___x_4641_;
v_ref_4691_ = v___x_4645_;
v_suppressElabErrors_4692_ = v_anyFailed_4635_;
v_checkDeprecated_4693_ = v___x_4647_;
v_isRecordingDeps_4694_ = v_anyFailed_4635_;
goto v___jp_4679_;
}
else
{
v___y_4717_ = v_anyFailed_4635_;
goto v___jp_4716_;
}
}
v___jp_4613_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_mk_io_user_error(v_a_4614_);
v___x_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
v___jp_4617_:
{
if (lean_obj_tag(v_a_4618_) == 0)
{
lean_object* v_msg_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_msg_4619_ = lean_ctor_get(v_a_4618_, 1);
lean_inc_ref(v_msg_4619_);
lean_dec_ref_known(v_a_4618_, 2);
v___x_4620_ = l_Lean_MessageData_toString(v_msg_4619_);
v___x_4621_ = lean_mk_io_user_error(v___x_4620_);
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
return v___x_4622_;
}
else
{
lean_object* v_id_4623_; lean_object* v___x_4624_; 
v_id_4623_ = lean_ctor_get(v_a_4618_, 0);
lean_inc(v_id_4623_);
lean_dec_ref_known(v_a_4618_, 2);
v___x_4624_ = l_Lean_InternalExceptionId_getName(v_id_4623_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_dec(v_id_4623_);
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__0));
v___x_4627_ = 1;
v___x_4628_ = l_Lean_Name_toString(v_a_4625_, v___x_4627_);
v___x_4629_ = lean_string_append(v___x_4626_, v___x_4628_);
lean_dec_ref(v___x_4628_);
v_a_4614_ = v___x_4629_;
goto v___jp_4613_;
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec_ref_known(v___x_4624_, 1);
v___x_4630_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__1));
v___x_4631_ = l_Nat_reprFast(v_id_4623_);
v___x_4632_ = lean_string_append(v___x_4630_, v___x_4631_);
lean_dec_ref(v___x_4631_);
v___x_4633_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__2));
v___x_4634_ = lean_string_append(v___x_4632_, v___x_4633_);
v_a_4614_ = v___x_4634_;
goto v___jp_4613_;
}
}
}
v___jp_4663_:
{
if (lean_obj_tag(v___y_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4677_; 
v_a_4665_ = lean_ctor_get(v___y_4664_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___y_4664_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4667_ = v___y_4664_;
v_isShared_4668_ = v_isSharedCheck_4677_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___y_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4677_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v_fst_4670_; lean_object* v_snd_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4675_; 
v___x_4669_ = lean_st_ref_get(v___x_4662_);
lean_dec(v___x_4662_);
lean_dec(v___x_4669_);
v_fst_4670_ = lean_ctor_get(v_a_4665_, 0);
lean_inc(v_fst_4670_);
v_snd_4671_ = lean_ctor_get(v_a_4665_, 1);
lean_inc(v_snd_4671_);
lean_dec(v_a_4665_);
v___x_4672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4672_, 0, v_fst_4670_);
v___x_4673_ = lean_unbox(v_snd_4671_);
lean_dec(v_snd_4671_);
lean_ctor_set_uint8(v___x_4672_, sizeof(void*)*1, v___x_4673_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v___x_4672_);
v___x_4675_ = v___x_4667_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4672_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
else
{
lean_object* v_a_4678_; 
lean_dec(v___x_4662_);
v_a_4678_ = lean_ctor_get(v___y_4664_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___y_4664_, 1);
v_a_4618_ = v_a_4678_;
goto v___jp_4617_;
}
}
v___jp_4679_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4695_ = lean_obj_once(&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5, &l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5_once, _init_l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters___closed__5);
lean_inc(v_cancelTk_x3f_4688_);
lean_inc(v_currMacroScope_4687_);
lean_inc(v_quotContext_4686_);
lean_inc(v_maxHeartbeats_4685_);
lean_inc(v_openDecls_4683_);
lean_inc(v_currNamespace_4682_);
lean_inc_ref(v_fileMap_4681_);
lean_inc_ref(v_fileName_4680_);
v___x_4696_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4696_, 0, v_fileName_4680_);
lean_ctor_set(v___x_4696_, 1, v_fileMap_4681_);
lean_ctor_set(v___x_4696_, 2, v___x_4638_);
lean_ctor_set(v___x_4696_, 3, v___x_4695_);
lean_ctor_set(v___x_4696_, 4, v_currNamespace_4682_);
lean_ctor_set(v___x_4696_, 5, v_openDecls_4683_);
lean_ctor_set(v___x_4696_, 6, v_initHeartbeats_4684_);
lean_ctor_set(v___x_4696_, 7, v_maxHeartbeats_4685_);
lean_ctor_set(v___x_4696_, 8, v_quotContext_4686_);
lean_ctor_set(v___x_4696_, 9, v_currMacroScope_4687_);
lean_ctor_set(v___x_4696_, 10, v_cancelTk_x3f_4688_);
lean_ctor_set(v___x_4696_, 11, v_inheritedTraceOptions_4689_);
lean_inc(v_ref_4691_);
v___x_4697_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v_currRecDepth_4690_);
lean_ctor_set(v___x_4697_, 2, v_ref_4691_);
lean_ctor_set_uint16(v___x_4697_, sizeof(void*)*3, v___x_4646_);
lean_ctor_set_uint8(v___x_4697_, sizeof(void*)*3 + 2, v_suppressElabErrors_4692_);
lean_ctor_set_uint8(v___x_4697_, sizeof(void*)*3 + 3, v_checkDeprecated_4693_);
lean_ctor_set_uint8(v___x_4697_, sizeof(void*)*3 + 4, v_isRecordingDeps_4694_);
v___x_4698_ = l_Lean_Linter_CodeQuality_getPackageChecks(v___x_4697_, v___x_4662_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4698_, 1);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v_sp_4609_);
lean_ctor_set(v___x_4700_, 1, v_mod_4611_);
v___x_4701_ = l_Lean_Linter_CodeQuality_runPackageChecks(v_a_4699_, v___x_4700_, v___x_4697_, v___x_4662_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v_entries_4703_; lean_object* v_errors_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v_entries_4703_ = lean_ctor_get(v_a_4702_, 0);
lean_inc_ref(v_entries_4703_);
v_errors_4704_ = lean_ctor_get(v_a_4702_, 1);
lean_inc_ref(v_errors_4704_);
lean_dec(v_a_4702_);
v___x_4705_ = lean_array_get_size(v_errors_4704_);
v___x_4706_ = lean_nat_dec_eq(v___x_4705_, v___x_4641_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_box(0);
v___x_4708_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4704_, v_entries_4703_, v___x_4707_, v___x_4658_, v___x_4697_, v___x_4662_);
lean_dec_ref_known(v___x_4697_, 3);
lean_dec_ref(v_errors_4704_);
v___y_4664_ = v___x_4708_;
goto v___jp_4663_;
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_box(0);
v___x_4710_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___lam__0(v_errors_4704_, v_entries_4703_, v___x_4709_, v_anyFailed_4635_, v___x_4697_, v___x_4662_);
lean_dec_ref_known(v___x_4697_, 3);
lean_dec_ref(v_errors_4704_);
v___y_4664_ = v___x_4710_;
goto v___jp_4663_;
}
}
else
{
lean_object* v_a_4711_; 
lean_dec_ref_known(v___x_4697_, 3);
lean_dec(v___x_4662_);
v_a_4711_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4701_, 1);
v_a_4618_ = v_a_4711_;
goto v___jp_4617_;
}
}
else
{
lean_object* v_a_4712_; 
lean_dec_ref_known(v___x_4697_, 3);
lean_dec(v___x_4662_);
lean_dec(v_mod_4611_);
lean_dec(v_sp_4609_);
v_a_4712_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4698_, 1);
v_a_4618_ = v_a_4712_;
goto v___jp_4617_;
}
}
v___jp_4716_:
{
lean_object* v___x_4718_; lean_object* v_env_4719_; lean_object* v_nextMacroScope_4720_; lean_object* v_ngen_4721_; lean_object* v_auxDeclNGen_4722_; lean_object* v_traceState_4723_; lean_object* v_recordedDeps_4724_; lean_object* v_messages_4725_; lean_object* v_infoState_4726_; lean_object* v_snapshotTasks_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4736_; 
v___x_4718_ = lean_st_ref_take(v___x_4662_);
v_env_4719_ = lean_ctor_get(v___x_4718_, 0);
v_nextMacroScope_4720_ = lean_ctor_get(v___x_4718_, 1);
v_ngen_4721_ = lean_ctor_get(v___x_4718_, 2);
v_auxDeclNGen_4722_ = lean_ctor_get(v___x_4718_, 3);
v_traceState_4723_ = lean_ctor_get(v___x_4718_, 4);
v_recordedDeps_4724_ = lean_ctor_get(v___x_4718_, 6);
v_messages_4725_ = lean_ctor_get(v___x_4718_, 7);
v_infoState_4726_ = lean_ctor_get(v___x_4718_, 8);
v_snapshotTasks_4727_ = lean_ctor_get(v___x_4718_, 9);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4736_ == 0)
{
lean_object* v_unused_4737_; 
v_unused_4737_ = lean_ctor_get(v___x_4718_, 5);
lean_dec(v_unused_4737_);
v___x_4729_ = v___x_4718_;
v_isShared_4730_ = v_isSharedCheck_4736_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_snapshotTasks_4727_);
lean_inc(v_infoState_4726_);
lean_inc(v_messages_4725_);
lean_inc(v_recordedDeps_4724_);
lean_inc(v_traceState_4723_);
lean_inc(v_auxDeclNGen_4722_);
lean_inc(v_ngen_4721_);
lean_inc(v_nextMacroScope_4720_);
lean_inc(v_env_4719_);
lean_dec(v___x_4718_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4736_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4731_ = l_Lean_Kernel_enableDiag(v_env_4719_, v___y_4717_);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 5, v___x_4654_);
lean_ctor_set(v___x_4729_, 0, v___x_4731_);
v___x_4733_ = v___x_4729_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_nextMacroScope_4720_);
lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_ngen_4721_);
lean_ctor_set(v_reuseFailAlloc_4735_, 3, v_auxDeclNGen_4722_);
lean_ctor_set(v_reuseFailAlloc_4735_, 4, v_traceState_4723_);
lean_ctor_set(v_reuseFailAlloc_4735_, 5, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4735_, 6, v_recordedDeps_4724_);
lean_ctor_set(v_reuseFailAlloc_4735_, 7, v_messages_4725_);
lean_ctor_set(v_reuseFailAlloc_4735_, 8, v_infoState_4726_);
lean_ctor_set(v_reuseFailAlloc_4735_, 9, v_snapshotTasks_4727_);
v___x_4733_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; 
v___x_4734_ = lean_st_ref_put(v___x_4662_, v___x_4733_);
v_fileName_4680_ = v___x_4636_;
v_fileMap_4681_ = v___x_4637_;
v_currNamespace_4682_ = v___x_4639_;
v_openDecls_4683_ = v___x_4640_;
v_initHeartbeats_4684_ = v___x_4661_;
v_maxHeartbeats_4685_ = v___x_4642_;
v_quotContext_4686_ = v___x_4639_;
v_currMacroScope_4687_ = v___x_4643_;
v_cancelTk_x3f_4688_ = v___x_4644_;
v_inheritedTraceOptions_4689_ = v___x_4714_;
v_currRecDepth_4690_ = v___x_4641_;
v_ref_4691_ = v___x_4645_;
v_suppressElabErrors_4692_ = v_anyFailed_4635_;
v_checkDeprecated_4693_ = v___x_4647_;
v_isRecordingDeps_4694_ = v_anyFailed_4635_;
goto v___jp_4679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks___boxed(lean_object* v_sp_4741_, lean_object* v_env_4742_, lean_object* v_mod_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v_sp_4741_, v_env_4742_, v_mod_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(lean_object* v_as_4746_, size_t v_sz_4747_, size_t v_i_4748_, lean_object* v_b_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___x_4753_; 
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___redArg(v_as_4746_, v_sz_4747_, v_i_4748_, v_b_4749_, v___y_4750_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1___boxed(lean_object* v_as_4754_, lean_object* v_sz_4755_, lean_object* v_i_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
size_t v_sz_boxed_4761_; size_t v_i_boxed_4762_; lean_object* v_res_4763_; 
v_sz_boxed_4761_ = lean_unbox_usize(v_sz_4755_);
lean_dec(v_sz_4755_);
v_i_boxed_4762_ = lean_unbox_usize(v_i_4756_);
lean_dec(v_i_4756_);
v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks_spec__1(v_as_4754_, v_sz_boxed_4761_, v_i_boxed_4762_, v_b_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec_ref(v_as_4754_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = lean_enable_initializer_execution();
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(lean_object* v_region_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_compacted_region_free(v_region_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_4771_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_4777_, lean_object* v_k_4778_, uint8_t v_v_4779_){
_start:
{
lean_object* v_map_4780_; uint8_t v_hasTrace_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4795_; 
v_map_4780_ = lean_ctor_get(v_o_4777_, 0);
v_hasTrace_4781_ = lean_ctor_get_uint8(v_o_4777_, sizeof(void*)*1);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_o_4777_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4783_ = v_o_4777_;
v_isShared_4784_ = v_isSharedCheck_4795_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_map_4780_);
lean_dec(v_o_4777_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4795_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4785_, 0, v_v_4779_);
lean_inc(v_k_4778_);
v___x_4786_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4778_, v___x_4785_, v_map_4780_);
if (v_hasTrace_4781_ == 0)
{
lean_object* v___x_4787_; uint8_t v___x_4788_; lean_object* v___x_4790_; 
v___x_4787_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_4788_ = l_Lean_Name_isPrefixOf(v___x_4787_, v_k_4778_);
lean_dec(v_k_4778_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4786_);
v___x_4790_ = v___x_4783_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4786_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_ctor_set_uint8(v___x_4790_, sizeof(void*)*1, v___x_4788_);
return v___x_4790_;
}
}
else
{
lean_object* v___x_4793_; 
lean_dec(v_k_4778_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4786_);
v___x_4793_ = v___x_4783_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4786_);
lean_ctor_set_uint8(v_reuseFailAlloc_4794_, sizeof(void*)*1, v_hasTrace_4781_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_4796_, lean_object* v_k_4797_, lean_object* v_v_4798_){
_start:
{
uint8_t v_v_boxed_4799_; lean_object* v_res_4800_; 
v_v_boxed_4799_ = lean_unbox(v_v_4798_);
v_res_4800_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_4796_, v_k_4797_, v_v_boxed_4799_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_s_4801_){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; uint32_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4803_ = lean_unsigned_to_nat(80u);
v___x_4804_ = l_Lean_Json_pretty(v_s_4801_, v___x_4803_);
v___x_4805_ = 10;
v___x_4806_ = lean_string_push(v___x_4804_, v___x_4805_);
v___x_4807_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__13_spec__23(v___x_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_s_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v_s_4808_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_as_4811_, size_t v_sz_4812_, size_t v_i_4813_, lean_object* v_b_4814_){
_start:
{
uint8_t v___x_4816_; 
v___x_4816_ = lean_usize_dec_lt(v_i_4813_, v_sz_4812_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_b_4814_);
return v___x_4817_;
}
else
{
lean_object* v___x_4818_; lean_object* v_a_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4818_ = lean_box(0);
v_a_4819_ = lean_array_uget_borrowed(v_as_4811_, v_i_4813_);
lean_inc(v_a_4819_);
v___x_4820_ = l_Lean_Linter_CodeQuality_instToJsonEntry_toJson(v_a_4819_);
v___x_4821_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__4(v___x_4820_);
if (lean_obj_tag(v___x_4821_) == 0)
{
size_t v___x_4822_; size_t v___x_4823_; 
lean_dec_ref_known(v___x_4821_, 1);
v___x_4822_ = ((size_t)1ULL);
v___x_4823_ = lean_usize_add(v_i_4813_, v___x_4822_);
v_i_4813_ = v___x_4823_;
v_b_4814_ = v___x_4818_;
goto _start;
}
else
{
return v___x_4821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_as_4825_, lean_object* v_sz_4826_, lean_object* v_i_4827_, lean_object* v_b_4828_, lean_object* v___y_4829_){
_start:
{
size_t v_sz_boxed_4830_; size_t v_i_boxed_4831_; lean_object* v_res_4832_; 
v_sz_boxed_4830_ = lean_unbox_usize(v_sz_4826_);
lean_dec(v_sz_4826_);
v_i_boxed_4831_ = lean_unbox_usize(v_i_4827_);
lean_dec(v_i_4827_);
v_res_4832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_as_4825_, v_sz_boxed_4830_, v_i_boxed_4831_, v_b_4828_);
lean_dec_ref(v_as_4825_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_4833_, size_t v_sz_4834_, size_t v_i_4835_, lean_object* v_bs_4836_){
_start:
{
uint8_t v_anyUnlocated_4837_; 
v_anyUnlocated_4837_ = lean_usize_dec_lt(v_i_4835_, v_sz_4834_);
if (v_anyUnlocated_4837_ == 0)
{
return v_bs_4836_;
}
else
{
lean_object* v___x_4838_; uint8_t v_anyFailed_4839_; lean_object* v_v_4840_; lean_object* v_bs_x27_4841_; lean_object* v___x_4842_; size_t v___x_4843_; size_t v___x_4844_; lean_object* v___x_4845_; 
v___x_4838_ = lean_unsigned_to_nat(0u);
v_anyFailed_4839_ = lean_nat_dec_eq(v___x_4833_, v___x_4838_);
v_v_4840_ = lean_array_uget(v_bs_4836_, v_i_4835_);
v_bs_x27_4841_ = lean_array_uset(v_bs_4836_, v_i_4835_, v___x_4838_);
v___x_4842_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_4842_, 0, v_v_4840_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1, v_anyFailed_4839_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1 + 1, v_anyUnlocated_4837_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1 + 2, v_anyFailed_4839_);
v___x_4843_ = ((size_t)1ULL);
v___x_4844_ = lean_usize_add(v_i_4835_, v___x_4843_);
v___x_4845_ = lean_array_uset(v_bs_x27_4841_, v_i_4835_, v___x_4842_);
v_i_4835_ = v___x_4844_;
v_bs_4836_ = v___x_4845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_4847_, lean_object* v_sz_4848_, lean_object* v_i_4849_, lean_object* v_bs_4850_){
_start:
{
size_t v_sz_boxed_4851_; size_t v_i_boxed_4852_; lean_object* v_res_4853_; 
v_sz_boxed_4851_ = lean_unbox_usize(v_sz_4848_);
lean_dec(v_sz_4848_);
v_i_boxed_4852_ = lean_unbox_usize(v_i_4849_);
lean_dec(v_i_4849_);
v_res_4853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_4847_, v_sz_boxed_4851_, v_i_boxed_4852_, v_bs_4850_);
lean_dec(v___x_4847_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_as_4854_, size_t v_i_4855_, size_t v_stop_4856_, lean_object* v_b_4857_){
_start:
{
uint8_t v___x_4858_; 
v___x_4858_ = lean_usize_dec_eq(v_i_4855_, v_stop_4856_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v_fst_4860_; lean_object* v_snd_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; size_t v___x_4864_; size_t v___x_4865_; 
v___x_4859_ = lean_array_uget_borrowed(v_as_4854_, v_i_4855_);
v_fst_4860_ = lean_ctor_get(v___x_4859_, 0);
v_snd_4861_ = lean_ctor_get(v___x_4859_, 1);
v___x_4862_ = lean_unbox(v_snd_4861_);
lean_inc(v_fst_4860_);
v___x_4863_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_4857_, v_fst_4860_, v___x_4862_);
v___x_4864_ = ((size_t)1ULL);
v___x_4865_ = lean_usize_add(v_i_4855_, v___x_4864_);
v_i_4855_ = v___x_4865_;
v_b_4857_ = v___x_4863_;
goto _start;
}
else
{
return v_b_4857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_as_4867_, lean_object* v_i_4868_, lean_object* v_stop_4869_, lean_object* v_b_4870_){
_start:
{
size_t v_i_boxed_4871_; size_t v_stop_boxed_4872_; lean_object* v_res_4873_; 
v_i_boxed_4871_ = lean_unbox_usize(v_i_4868_);
lean_dec(v_i_4868_);
v_stop_boxed_4872_ = lean_unbox_usize(v_stop_4869_);
lean_dec(v_stop_4869_);
v_res_4873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_as_4867_, v_i_boxed_4871_, v_stop_boxed_4872_, v_b_4870_);
lean_dec_ref(v_as_4867_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_4883_, lean_object* v_checkImports_4884_, lean_object* v_args_4885_, lean_object* v___x_4886_, lean_object* v_as_4887_, size_t v_sz_4888_, size_t v_i_4889_, lean_object* v_b_4890_){
_start:
{
lean_object* v_a_4893_; lean_object* v___x_4897_; uint8_t v_anyFailed_4898_; uint8_t v_anyUnlocated_4899_; lean_object* v___x_4900_; lean_object* v_envLinterModule_4901_; uint8_t v___x_4902_; 
v___x_4897_ = lean_unsigned_to_nat(0u);
v_anyFailed_4898_ = lean_nat_dec_eq(v___x_4883_, v___x_4897_);
v_anyUnlocated_4899_ = 1;
v___x_4900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__3));
v_envLinterModule_4901_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_4901_, 0, v___x_4900_);
lean_ctor_set_uint8(v_envLinterModule_4901_, sizeof(void*)*1, v_anyFailed_4898_);
lean_ctor_set_uint8(v_envLinterModule_4901_, sizeof(void*)*1 + 1, v_anyUnlocated_4899_);
lean_ctor_set_uint8(v_envLinterModule_4901_, sizeof(void*)*1 + 2, v_anyFailed_4898_);
v___x_4902_ = lean_usize_dec_lt(v_i_4889_, v_sz_4888_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; 
lean_dec_ref_known(v_envLinterModule_4901_, 1);
lean_dec(v___x_4886_);
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v_b_4890_);
return v___x_4903_;
}
else
{
lean_object* v_snd_4904_; lean_object* v_snd_4905_; lean_object* v_snd_4906_; lean_object* v_snd_4907_; lean_object* v_fst_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_5217_; 
v_snd_4904_ = lean_ctor_get(v_b_4890_, 1);
lean_inc(v_snd_4904_);
v_snd_4905_ = lean_ctor_get(v_snd_4904_, 1);
lean_inc(v_snd_4905_);
v_snd_4906_ = lean_ctor_get(v_snd_4905_, 1);
lean_inc(v_snd_4906_);
v_snd_4907_ = lean_ctor_get(v_snd_4906_, 1);
lean_inc(v_snd_4907_);
v_fst_4908_ = lean_ctor_get(v_b_4890_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v_b_4890_);
if (v_isSharedCheck_5217_ == 0)
{
lean_object* v_unused_5218_; 
v_unused_5218_ = lean_ctor_get(v_b_4890_, 1);
lean_dec(v_unused_5218_);
v___x_4910_ = v_b_4890_;
v_isShared_4911_ = v_isSharedCheck_5217_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_fst_4908_);
lean_dec(v_b_4890_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_5217_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v_fst_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_5215_; 
v_fst_4912_ = lean_ctor_get(v_snd_4904_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_snd_4904_);
if (v_isSharedCheck_5215_ == 0)
{
lean_object* v_unused_5216_; 
v_unused_5216_ = lean_ctor_get(v_snd_4904_, 1);
lean_dec(v_unused_5216_);
v___x_4914_ = v_snd_4904_;
v_isShared_4915_ = v_isSharedCheck_5215_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_fst_4912_);
lean_dec(v_snd_4904_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_5215_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v_fst_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_5213_; 
v_fst_4916_ = lean_ctor_get(v_snd_4905_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v_snd_4905_);
if (v_isSharedCheck_5213_ == 0)
{
lean_object* v_unused_5214_; 
v_unused_5214_ = lean_ctor_get(v_snd_4905_, 1);
lean_dec(v_unused_5214_);
v___x_4918_ = v_snd_4905_;
v_isShared_4919_ = v_isSharedCheck_5213_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_fst_4916_);
lean_dec(v_snd_4905_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_5213_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v_fst_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_5211_; 
v_fst_4920_ = lean_ctor_get(v_snd_4906_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v_snd_4906_);
if (v_isSharedCheck_5211_ == 0)
{
lean_object* v_unused_5212_; 
v_unused_5212_ = lean_ctor_get(v_snd_4906_, 1);
lean_dec(v_unused_5212_);
v___x_4922_ = v_snd_4906_;
v_isShared_4923_ = v_isSharedCheck_5211_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_fst_4920_);
lean_dec(v_snd_4906_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_5211_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v_fst_4924_; lean_object* v_snd_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_5210_; 
v_fst_4924_ = lean_ctor_get(v_snd_4907_, 0);
v_snd_4925_ = lean_ctor_get(v_snd_4907_, 1);
v_isSharedCheck_5210_ = !lean_is_exclusive(v_snd_4907_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_4927_ = v_snd_4907_;
v_isShared_4928_ = v_isSharedCheck_5210_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_snd_4925_);
lean_inc(v_fst_4924_);
lean_dec(v_snd_4907_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_5210_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; lean_object* v_a_4930_; lean_object* v___y_4932_; lean_object* v___y_4933_; uint8_t v_anyFailed_4934_; uint8_t v_anyUnlocated_4935_; lean_object* v_records_4936_; lean_object* v_codeQualityEntries_4937_; lean_object* v___y_5084_; lean_object* v___y_5085_; uint8_t v_anyFailed_5086_; uint8_t v_anyUnlocated_5087_; lean_object* v_records_5088_; lean_object* v_codeQualityEntries_5089_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_4929_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v_a_4930_ = lean_array_uget_borrowed(v_as_4887_, v_i_4889_);
v___x_5147_ = lean_enable_initializer_execution();
lean_inc(v_a_4930_);
v___x_5148_ = l_Lean_findOLean(v_a_4930_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5150_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_a_5149_);
lean_dec_ref_known(v___x_5148_, 1);
v___x_5150_ = l_Lean_readModuleData(v_a_5149_);
lean_dec(v_a_5149_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; lean_object* v_fst_5152_; lean_object* v_snd_5153_; uint8_t v___x_5154_; uint8_t v___y_5156_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
lean_dec_ref_known(v___x_5150_, 1);
v_fst_5152_ = lean_ctor_get(v_a_5151_, 0);
lean_inc(v_fst_5152_);
v_snd_5153_ = lean_ctor_get(v_a_5151_, 1);
lean_inc(v_snd_5153_);
lean_dec(v_a_5151_);
v___x_5154_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_5152_);
lean_dec(v_fst_5152_);
if (v___x_5154_ == 0)
{
uint8_t v___x_5192_; 
v___x_5192_ = 2;
v___y_5156_ = v___x_5192_;
goto v___jp_5155_;
}
else
{
uint8_t v___x_5193_; 
v___x_5193_ = 1;
v___y_5156_ = v___x_5193_;
goto v___jp_5155_;
}
v___jp_5155_:
{
lean_object* v___x_5157_; 
v___x_5157_ = lean_compacted_region_free(v_snd_5153_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; uint32_t v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_dec_ref_known(v___x_5157_, 1);
lean_inc(v_a_4930_);
v___x_5158_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_5158_, 0, v_a_4930_);
lean_ctor_set_uint8(v___x_5158_, sizeof(void*)*1, v_anyFailed_4898_);
lean_ctor_set_uint8(v___x_5158_, sizeof(void*)*1 + 1, v_anyUnlocated_4899_);
lean_ctor_set_uint8(v___x_5158_, sizeof(void*)*1 + 2, v_anyFailed_4898_);
v___x_5159_ = lean_unsigned_to_nat(2u);
v___x_5160_ = lean_mk_empty_array_with_capacity(v___x_5159_);
v___x_5161_ = lean_array_push(v___x_5160_, v___x_5158_);
v___x_5162_ = lean_array_push(v___x_5161_, v_envLinterModule_4901_);
v___x_5163_ = l_Array_append___redArg(v___x_5162_, v_checkImports_4884_);
v___x_5164_ = l_Lean_Options_empty;
v___x_5165_ = 1024;
v___x_5166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__4));
v___x_5167_ = lean_box(1);
v___x_5168_ = l_Lean_importModules(v___x_5163_, v___x_5164_, v___x_5165_, v___x_5166_, v_anyFailed_4898_, v_anyUnlocated_4899_, v___y_5156_, v___x_5167_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v_linterOverrides_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
v_linterOverrides_5170_ = lean_ctor_get(v_args_4885_, 0);
v___x_5171_ = lean_array_get_size(v_linterOverrides_5170_);
v___x_5172_ = lean_nat_dec_lt(v___x_4897_, v___x_5171_);
if (v___x_5172_ == 0)
{
v___y_5107_ = v_a_5169_;
v___y_5108_ = v___x_5164_;
goto v___jp_5106_;
}
else
{
size_t v___x_5173_; size_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5173_ = ((size_t)0ULL);
v___x_5174_ = lean_usize_of_nat(v___x_5171_);
v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__2(v_linterOverrides_5170_, v___x_5173_, v___x_5174_, v___x_5164_);
v___y_5107_ = v_a_5169_;
v___y_5108_ = v___x_5175_;
goto v___jp_5106_;
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_dec(v_fst_4920_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4916_);
lean_del_object(v___x_4914_);
lean_dec(v_fst_4912_);
lean_del_object(v___x_4910_);
lean_dec(v_fst_4908_);
lean_dec(v___x_4886_);
v_a_5176_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5168_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5168_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_dec(v_fst_4920_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4916_);
lean_del_object(v___x_4914_);
lean_dec(v_fst_4912_);
lean_del_object(v___x_4910_);
lean_dec(v_fst_4908_);
lean_dec_ref_known(v_envLinterModule_4901_, 1);
lean_dec(v___x_4886_);
v_a_5184_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5157_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5157_);
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
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_dec(v_fst_4920_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4916_);
lean_del_object(v___x_4914_);
lean_dec(v_fst_4912_);
lean_del_object(v___x_4910_);
lean_dec(v_fst_4908_);
lean_dec_ref_known(v_envLinterModule_4901_, 1);
lean_dec(v___x_4886_);
v_a_5194_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5150_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5150_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_dec(v_fst_4920_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4916_);
lean_del_object(v___x_4914_);
lean_dec(v_fst_4912_);
lean_del_object(v___x_4910_);
lean_dec(v_fst_4908_);
lean_dec_ref_known(v_envLinterModule_4901_, 1);
lean_dec(v___x_4886_);
v_a_5202_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5148_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5148_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
v___jp_4931_:
{
uint8_t v_mode_4938_; uint8_t v___x_4939_; uint8_t v___x_4940_; 
v_mode_4938_ = lean_ctor_get_uint8(v_args_4885_, sizeof(void*)*4 + 1);
v___x_4939_ = 2;
v___x_4940_ = l_Lake_BuiltinLint_instBEqMode_beq(v_mode_4938_, v___x_4939_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = l_Lean_Name_getRoot(v_a_4930_);
lean_inc(v___x_4886_);
v___x_4942_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks(v_args_4885_, v___y_4933_, v___x_4886_, v___y_4932_, v___x_4941_, v_fst_4924_);
lean_dec_ref(v___y_4933_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v_outcome_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___x_4942_, 1);
v_outcome_4944_ = lean_ctor_get(v_a_4943_, 0);
if (lean_obj_tag(v_outcome_4944_) == 0)
{
uint8_t v_failed_4945_; 
v_failed_4945_ = lean_ctor_get_uint8(v_outcome_4944_, 0);
if (v_failed_4945_ == 0)
{
lean_object* v_checkedModules_4946_; lean_object* v___x_4948_; 
v_checkedModules_4946_ = lean_ctor_get(v_a_4943_, 1);
lean_inc(v_checkedModules_4946_);
lean_dec(v_a_4943_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v_checkedModules_4946_);
v___x_4948_ = v___x_4927_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_checkedModules_4946_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_snd_4925_);
v___x_4948_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4950_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_4948_);
lean_ctor_set(v___x_4922_, 0, v_codeQualityEntries_4937_);
v___x_4950_ = v___x_4922_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_codeQualityEntries_4937_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v___x_4948_);
v___x_4950_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
lean_object* v___x_4952_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_4950_);
lean_ctor_set(v___x_4918_, 0, v_records_4936_);
v___x_4952_ = v___x_4918_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_records_4936_);
lean_ctor_set(v_reuseFailAlloc_4961_, 1, v___x_4950_);
v___x_4952_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4955_; 
v___x_4953_ = lean_box(v_anyUnlocated_4935_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_4952_);
lean_ctor_set(v___x_4914_, 0, v___x_4953_);
v___x_4955_ = v___x_4914_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4953_);
lean_ctor_set(v_reuseFailAlloc_4960_, 1, v___x_4952_);
v___x_4955_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
lean_object* v___x_4956_; lean_object* v___x_4958_; 
v___x_4956_ = lean_box(v_anyFailed_4934_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 1, v___x_4955_);
lean_ctor_set(v___x_4910_, 0, v___x_4956_);
v___x_4958_ = v___x_4910_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___x_4955_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
v_a_4893_ = v___x_4958_;
goto v___jp_4892_;
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4964_; lean_object* v___x_4966_; 
v_checkedModules_4964_ = lean_ctor_get(v_a_4943_, 1);
lean_inc(v_checkedModules_4964_);
lean_dec(v_a_4943_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v_checkedModules_4964_);
v___x_4966_ = v___x_4927_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_checkedModules_4964_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_snd_4925_);
v___x_4966_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
lean_object* v___x_4968_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_4966_);
lean_ctor_set(v___x_4922_, 0, v_codeQualityEntries_4937_);
v___x_4968_ = v___x_4922_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_codeQualityEntries_4937_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4970_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_4968_);
lean_ctor_set(v___x_4918_, 0, v_records_4936_);
v___x_4970_ = v___x_4918_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_records_4936_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = lean_box(v_anyUnlocated_4935_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_4970_);
lean_ctor_set(v___x_4914_, 0, v___x_4971_);
v___x_4973_ = v___x_4914_;
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
v___x_4974_ = lean_box(v_anyUnlocated_4899_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 1, v___x_4973_);
lean_ctor_set(v___x_4910_, 0, v___x_4974_);
v___x_4976_ = v___x_4910_;
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
v_a_4893_ = v___x_4976_;
goto v___jp_4892_;
}
}
}
}
}
}
}
else
{
lean_object* v_checkedModules_4982_; lean_object* v_records_4983_; uint8_t v_unlocated_4984_; lean_object* v___x_4985_; 
lean_inc_ref(v_outcome_4944_);
v_checkedModules_4982_ = lean_ctor_get(v_a_4943_, 1);
lean_inc(v_checkedModules_4982_);
lean_dec(v_a_4943_);
v_records_4983_ = lean_ctor_get(v_outcome_4944_, 0);
lean_inc_ref(v_records_4983_);
v_unlocated_4984_ = lean_ctor_get_uint8(v_outcome_4944_, sizeof(void*)*1);
lean_dec_ref_known(v_outcome_4944_, 1);
v___x_4985_ = l_Array_append___redArg(v_records_4936_, v_records_4983_);
lean_dec_ref(v_records_4983_);
if (v_unlocated_4984_ == 0)
{
lean_object* v___x_4987_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v_checkedModules_4982_);
v___x_4987_ = v___x_4927_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_checkedModules_4982_);
lean_ctor_set(v_reuseFailAlloc_5002_, 1, v_snd_4925_);
v___x_4987_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4989_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_4987_);
lean_ctor_set(v___x_4922_, 0, v_codeQualityEntries_4937_);
v___x_4989_ = v___x_4922_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_codeQualityEntries_4937_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4991_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_4989_);
lean_ctor_set(v___x_4918_, 0, v___x_4985_);
v___x_4991_ = v___x_4918_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4992_ = lean_box(v_anyUnlocated_4935_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_4991_);
lean_ctor_set(v___x_4914_, 0, v___x_4992_);
v___x_4994_ = v___x_4914_;
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
v___x_4995_ = lean_box(v_anyFailed_4934_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 1, v___x_4994_);
lean_ctor_set(v___x_4910_, 0, v___x_4995_);
v___x_4997_ = v___x_4910_;
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
v_a_4893_ = v___x_4997_;
goto v___jp_4892_;
}
}
}
}
}
}
else
{
lean_object* v___x_5004_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v_checkedModules_4982_);
v___x_5004_ = v___x_4927_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_checkedModules_4982_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_snd_4925_);
v___x_5004_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5006_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_5004_);
lean_ctor_set(v___x_4922_, 0, v_codeQualityEntries_4937_);
v___x_5006_ = v___x_4922_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_codeQualityEntries_4937_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5008_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_5006_);
lean_ctor_set(v___x_4918_, 0, v___x_4985_);
v___x_5008_ = v___x_4918_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5006_);
v___x_5008_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5009_ = lean_box(v_anyUnlocated_4899_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_5008_);
lean_ctor_set(v___x_4914_, 0, v___x_5009_);
v___x_5011_ = v___x_4914_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___x_5008_);
v___x_5011_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5012_ = lean_box(v_anyFailed_4934_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 1, v___x_5011_);
lean_ctor_set(v___x_4910_, 0, v___x_5012_);
v___x_5014_ = v___x_4910_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5012_);
lean_ctor_set(v_reuseFailAlloc_5015_, 1, v___x_5011_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
v_a_4893_ = v___x_5014_;
goto v___jp_4892_;
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
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec_ref(v_codeQualityEntries_4937_);
lean_dec_ref(v_records_4936_);
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_del_object(v___x_4922_);
lean_del_object(v___x_4918_);
lean_del_object(v___x_4914_);
lean_del_object(v___x_4910_);
lean_dec(v___x_4886_);
v_a_5020_ = lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_4942_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4942_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
else
{
lean_object* v___x_5028_; lean_object* v_fst_5029_; lean_object* v_snd_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5082_; 
lean_del_object(v___x_4910_);
v___x_5028_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectRecordedCodeQuality(v_args_4885_, v___y_4933_, v___y_4932_, v_a_4930_, v_snd_4925_);
lean_dec_ref(v___y_4933_);
v_fst_5029_ = lean_ctor_get(v___x_5028_, 0);
v_snd_5030_ = lean_ctor_get(v___x_5028_, 1);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5032_ = v___x_5028_;
v_isShared_5033_ = v_isSharedCheck_5082_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_snd_5030_);
lean_inc(v_fst_5029_);
lean_dec(v___x_5028_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5082_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = l_Array_append___redArg(v_codeQualityEntries_4937_, v_fst_5029_);
lean_dec(v_fst_5029_);
lean_inc(v_a_4930_);
lean_inc(v___x_4886_);
v___x_5035_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runPackageCodeQualityChecks(v___x_4886_, v___y_4932_, v_a_4930_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v_entries_5037_; uint8_t v_failed_5038_; lean_object* v___x_5039_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v_entries_5037_ = lean_ctor_get(v_a_5036_, 0);
lean_inc_ref(v_entries_5037_);
v_failed_5038_ = lean_ctor_get_uint8(v_a_5036_, sizeof(void*)*1);
lean_dec(v_a_5036_);
v___x_5039_ = l_Array_append___redArg(v___x_5034_, v_entries_5037_);
lean_dec_ref(v_entries_5037_);
if (v_failed_5038_ == 0)
{
lean_object* v___x_5041_; 
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 0, v_fst_4924_);
v___x_5041_ = v___x_5032_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_fst_4924_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v_snd_5030_);
v___x_5041_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5043_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 1, v___x_5041_);
lean_ctor_set(v___x_4927_, 0, v___x_5039_);
v___x_5043_ = v___x_4927_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5045_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_5043_);
lean_ctor_set(v___x_4922_, 0, v_records_4936_);
v___x_5045_ = v___x_4922_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_records_4936_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5046_ = lean_box(v_anyUnlocated_4935_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_5045_);
lean_ctor_set(v___x_4918_, 0, v___x_5046_);
v___x_5048_ = v___x_4918_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5045_);
v___x_5048_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5049_; lean_object* v___x_5051_; 
v___x_5049_ = lean_box(v_anyFailed_4934_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_5048_);
lean_ctor_set(v___x_4914_, 0, v___x_5049_);
v___x_5051_ = v___x_4914_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5049_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v___x_5048_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
v_a_4893_ = v___x_5051_;
goto v___jp_4892_;
}
}
}
}
}
}
else
{
lean_object* v___x_5058_; 
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 0, v_fst_4924_);
v___x_5058_ = v___x_5032_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_fst_4924_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v_snd_5030_);
v___x_5058_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5060_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 1, v___x_5058_);
lean_ctor_set(v___x_4927_, 0, v___x_5039_);
v___x_5060_ = v___x_4927_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5062_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 1, v___x_5060_);
lean_ctor_set(v___x_4922_, 0, v_records_4936_);
v___x_5062_ = v___x_4922_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_records_4936_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5065_; 
v___x_5063_ = lean_box(v_anyUnlocated_4935_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_5062_);
lean_ctor_set(v___x_4918_, 0, v___x_5063_);
v___x_5065_ = v___x_4918_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5063_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v___x_5062_);
v___x_5065_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
lean_object* v___x_5066_; lean_object* v___x_5068_; 
v___x_5066_ = lean_box(v_anyUnlocated_4899_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 1, v___x_5065_);
lean_ctor_set(v___x_4914_, 0, v___x_5066_);
v___x_5068_ = v___x_4914_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
lean_ctor_set(v_reuseFailAlloc_5069_, 1, v___x_5065_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
v_a_4893_ = v___x_5068_;
goto v___jp_4892_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_dec_ref(v___x_5034_);
lean_del_object(v___x_5032_);
lean_dec(v_snd_5030_);
lean_dec_ref(v_records_4936_);
lean_del_object(v___x_4927_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_del_object(v___x_4918_);
lean_del_object(v___x_4914_);
lean_dec(v___x_4886_);
v_a_5074_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_5035_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5035_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
}
}
v___jp_5083_:
{
lean_object* v___x_5090_; 
lean_inc(v_a_4930_);
lean_inc_ref(v___y_5084_);
lean_inc(v___x_4886_);
lean_inc_ref(v___y_5085_);
v___x_5090_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runEnvironmentLinters(v_args_4885_, v___y_5085_, v___x_4886_, v___y_5084_, v_a_4930_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5090_, 1);
switch(lean_obj_tag(v_a_5091_))
{
case 0:
{
uint8_t v_failed_5092_; 
v_failed_5092_ = lean_ctor_get_uint8(v_a_5091_, 0);
lean_dec_ref_known(v_a_5091_, 0);
if (v_failed_5092_ == 0)
{
v___y_4932_ = v___y_5084_;
v___y_4933_ = v___y_5085_;
v_anyFailed_4934_ = v_anyFailed_5086_;
v_anyUnlocated_4935_ = v_anyUnlocated_5087_;
v_records_4936_ = v_records_5088_;
v_codeQualityEntries_4937_ = v_codeQualityEntries_5089_;
goto v___jp_4931_;
}
else
{
v___y_4932_ = v___y_5084_;
v___y_4933_ = v___y_5085_;
v_anyFailed_4934_ = v_anyUnlocated_4899_;
v_anyUnlocated_4935_ = v_anyUnlocated_5087_;
v_records_4936_ = v_records_5088_;
v_codeQualityEntries_4937_ = v_codeQualityEntries_5089_;
goto v___jp_4931_;
}
}
case 1:
{
lean_object* v_records_5093_; uint8_t v_unlocated_5094_; lean_object* v___x_5095_; 
v_records_5093_ = lean_ctor_get(v_a_5091_, 0);
lean_inc_ref(v_records_5093_);
v_unlocated_5094_ = lean_ctor_get_uint8(v_a_5091_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5091_, 1);
v___x_5095_ = l_Array_append___redArg(v_records_5088_, v_records_5093_);
lean_dec_ref(v_records_5093_);
if (v_unlocated_5094_ == 0)
{
v___y_4932_ = v___y_5084_;
v___y_4933_ = v___y_5085_;
v_anyFailed_4934_ = v_anyFailed_5086_;
v_anyUnlocated_4935_ = v_anyUnlocated_5087_;
v_records_4936_ = v___x_5095_;
v_codeQualityEntries_4937_ = v_codeQualityEntries_5089_;
goto v___jp_4931_;
}
else
{
v___y_4932_ = v___y_5084_;
v___y_4933_ = v___y_5085_;
v_anyFailed_4934_ = v_anyFailed_5086_;
v_anyUnlocated_4935_ = v_anyUnlocated_4899_;
v_records_4936_ = v___x_5095_;
v_codeQualityEntries_4937_ = v_codeQualityEntries_5089_;
goto v___jp_4931_;
}
}
default: 
{
lean_object* v_entries_5096_; lean_object* v___x_5097_; 
v_entries_5096_ = lean_ctor_get(v_a_5091_, 0);
lean_inc_ref(v_entries_5096_);
lean_dec_ref_known(v_a_5091_, 1);
v___x_5097_ = l_Array_append___redArg(v_codeQualityEntries_5089_, v_entries_5096_);
lean_dec_ref(v_entries_5096_);
v___y_4932_ = v___y_5084_;
v___y_4933_ = v___y_5085_;
v_anyFailed_4934_ = v_anyFailed_5086_;
v_anyUnlocated_4935_ = v_anyUnlocated_5087_;
v_records_4936_ = v_records_5088_;
v_codeQualityEntries_4937_ = v___x_5097_;
goto v___jp_4931_;
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec_ref(v_codeQualityEntries_5089_);
lean_dec_ref(v_records_5088_);
lean_dec_ref(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_del_object(v___x_4918_);
lean_del_object(v___x_4914_);
lean_del_object(v___x_4910_);
lean_dec(v___x_4886_);
v_a_5098_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5090_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5090_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
v___jp_5106_:
{
lean_object* v___x_5109_; lean_object* v_toEnvExtension_5110_; lean_object* v_asyncMode_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v_merged_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5145_; 
v___x_5109_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_5110_ = lean_ctor_get(v___x_5109_, 0);
v_asyncMode_5111_ = lean_ctor_get(v_toEnvExtension_5110_, 2);
v___x_5112_ = lean_box(0);
lean_inc_ref(v___y_5107_);
v___x_5113_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4929_, v___x_5109_, v___y_5107_, v_asyncMode_5111_, v___x_5112_, v_anyFailed_4898_);
v_merged_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5145_ == 0)
{
lean_object* v_unused_5146_; 
v_unused_5146_ = lean_ctor_get(v___x_5113_, 1);
lean_dec(v_unused_5146_);
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5145_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_merged_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5145_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 1, v_merged_5114_);
lean_ctor_set(v___x_5116_, 0, v___y_5108_);
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___y_5108_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_merged_5114_);
v___x_5119_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
lean_object* v___x_5120_; 
v___x_5120_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runTextLinters(v_args_4885_, v___x_5119_, v___y_5107_, v_a_4930_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5120_, 1);
switch(lean_obj_tag(v_a_5121_))
{
case 0:
{
uint8_t v___x_5122_; 
v___x_5122_ = lean_unbox(v_fst_4908_);
lean_dec(v_fst_4908_);
if (v___x_5122_ == 0)
{
uint8_t v_failed_5123_; uint8_t v___x_5124_; 
v_failed_5123_ = lean_ctor_get_uint8(v_a_5121_, 0);
lean_dec_ref_known(v_a_5121_, 0);
v___x_5124_ = lean_unbox(v_fst_4912_);
lean_dec(v_fst_4912_);
v___y_5084_ = v___y_5107_;
v___y_5085_ = v___x_5119_;
v_anyFailed_5086_ = v_failed_5123_;
v_anyUnlocated_5087_ = v___x_5124_;
v_records_5088_ = v_fst_4916_;
v_codeQualityEntries_5089_ = v_fst_4920_;
goto v___jp_5083_;
}
else
{
uint8_t v___x_5125_; 
lean_dec_ref_known(v_a_5121_, 0);
v___x_5125_ = lean_unbox(v_fst_4912_);
lean_dec(v_fst_4912_);
v___y_5084_ = v___y_5107_;
v___y_5085_ = v___x_5119_;
v_anyFailed_5086_ = v_anyUnlocated_4899_;
v_anyUnlocated_5087_ = v___x_5125_;
v_records_5088_ = v_fst_4916_;
v_codeQualityEntries_5089_ = v_fst_4920_;
goto v___jp_5083_;
}
}
case 1:
{
lean_object* v_records_5126_; uint8_t v_unlocated_5127_; lean_object* v___x_5128_; 
v_records_5126_ = lean_ctor_get(v_a_5121_, 0);
lean_inc_ref(v_records_5126_);
v_unlocated_5127_ = lean_ctor_get_uint8(v_a_5121_, sizeof(void*)*1);
lean_dec_ref_known(v_a_5121_, 1);
v___x_5128_ = l_Array_append___redArg(v_fst_4916_, v_records_5126_);
lean_dec_ref(v_records_5126_);
if (v_unlocated_5127_ == 0)
{
uint8_t v___x_5129_; uint8_t v___x_5130_; 
v___x_5129_ = lean_unbox(v_fst_4908_);
lean_dec(v_fst_4908_);
v___x_5130_ = lean_unbox(v_fst_4912_);
lean_dec(v_fst_4912_);
v___y_5084_ = v___y_5107_;
v___y_5085_ = v___x_5119_;
v_anyFailed_5086_ = v___x_5129_;
v_anyUnlocated_5087_ = v___x_5130_;
v_records_5088_ = v___x_5128_;
v_codeQualityEntries_5089_ = v_fst_4920_;
goto v___jp_5083_;
}
else
{
uint8_t v___x_5131_; 
lean_dec(v_fst_4912_);
v___x_5131_ = lean_unbox(v_fst_4908_);
lean_dec(v_fst_4908_);
v___y_5084_ = v___y_5107_;
v___y_5085_ = v___x_5119_;
v_anyFailed_5086_ = v___x_5131_;
v_anyUnlocated_5087_ = v_anyUnlocated_4899_;
v_records_5088_ = v___x_5128_;
v_codeQualityEntries_5089_ = v_fst_4920_;
goto v___jp_5083_;
}
}
default: 
{
lean_object* v_entries_5132_; lean_object* v___x_5133_; uint8_t v___x_5134_; uint8_t v___x_5135_; 
v_entries_5132_ = lean_ctor_get(v_a_5121_, 0);
lean_inc_ref(v_entries_5132_);
lean_dec_ref_known(v_a_5121_, 1);
v___x_5133_ = l_Array_append___redArg(v_fst_4920_, v_entries_5132_);
lean_dec_ref(v_entries_5132_);
v___x_5134_ = lean_unbox(v_fst_4908_);
lean_dec(v_fst_4908_);
v___x_5135_ = lean_unbox(v_fst_4912_);
lean_dec(v_fst_4912_);
v___y_5084_ = v___y_5107_;
v___y_5085_ = v___x_5119_;
v_anyFailed_5086_ = v___x_5134_;
v_anyUnlocated_5087_ = v___x_5135_;
v_records_5088_ = v_fst_4916_;
v_codeQualityEntries_5089_ = v___x_5133_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_dec_ref(v___x_5119_);
lean_dec_ref(v___y_5107_);
lean_del_object(v___x_4927_);
lean_dec(v_snd_4925_);
lean_dec(v_fst_4924_);
lean_del_object(v___x_4922_);
lean_dec(v_fst_4920_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4916_);
lean_del_object(v___x_4914_);
lean_dec(v_fst_4912_);
lean_del_object(v___x_4910_);
lean_dec(v_fst_4908_);
lean_dec(v___x_4886_);
v_a_5136_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5120_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5120_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
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
v___jp_4892_:
{
size_t v___x_4894_; size_t v___x_4895_; 
v___x_4894_ = ((size_t)1ULL);
v___x_4895_ = lean_usize_add(v_i_4889_, v___x_4894_);
v_i_4889_ = v___x_4895_;
v_b_4890_ = v_a_4893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_5219_, lean_object* v_checkImports_5220_, lean_object* v_args_5221_, lean_object* v___x_5222_, lean_object* v_as_5223_, lean_object* v_sz_5224_, lean_object* v_i_5225_, lean_object* v_b_5226_, lean_object* v___y_5227_){
_start:
{
size_t v_sz_boxed_5228_; size_t v_i_boxed_5229_; lean_object* v_res_5230_; 
v_sz_boxed_5228_ = lean_unbox_usize(v_sz_5224_);
lean_dec(v_sz_5224_);
v_i_boxed_5229_ = lean_unbox_usize(v_i_5225_);
lean_dec(v_i_5225_);
v_res_5230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5219_, v_checkImports_5220_, v_args_5221_, v___x_5222_, v_as_5223_, v_sz_boxed_5228_, v_i_boxed_5229_, v_b_5226_);
lean_dec_ref(v_as_5223_);
lean_dec_ref(v_args_5221_);
lean_dec_ref(v_checkImports_5220_);
lean_dec(v___x_5219_);
return v_res_5230_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__0(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; 
v___x_5231_ = l_Lean_NameSet_empty;
v___x_5232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
return v___x_5232_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__1(void){
_start:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v___x_5233_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__0, &l_Lake_BuiltinLint_run___closed__0_once, _init_l_Lake_BuiltinLint_run___closed__0);
v___x_5234_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5234_);
lean_ctor_set(v___x_5235_, 1, v___x_5233_);
return v___x_5235_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___closed__2(void){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5236_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__1, &l_Lake_BuiltinLint_run___closed__1_once, _init_l_Lake_BuiltinLint_run___closed__1);
v___x_5237_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_runDeferredChecks___closed__4));
v___x_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5237_);
lean_ctor_set(v___x_5238_, 1, v___x_5236_);
return v___x_5238_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = 0;
v___x_5241_ = lean_box_uint32(v___x_5240_);
return v___x_5241_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_5242_; lean_object* v___x_5243_; 
v___x_5242_ = 1;
v___x_5243_ = lean_box_uint32(v___x_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_5244_){
_start:
{
lean_object* v_mods_5246_; uint8_t v_mode_5247_; lean_object* v_checks_5248_; lean_object* v_srcSearchPath_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; uint8_t v_anyFailed_5252_; 
v_mods_5246_ = lean_ctor_get(v_args_5244_, 1);
lean_inc_ref(v_mods_5246_);
v_mode_5247_ = lean_ctor_get_uint8(v_args_5244_, sizeof(void*)*4 + 1);
v_checks_5248_ = lean_ctor_get(v_args_5244_, 2);
v_srcSearchPath_5249_ = lean_ctor_get(v_args_5244_, 3);
v___x_5250_ = lean_array_get_size(v_mods_5246_);
v___x_5251_ = lean_unsigned_to_nat(0u);
v_anyFailed_5252_ = lean_nat_dec_eq(v___x_5250_, v___x_5251_);
if (v_anyFailed_5252_ == 0)
{
size_t v_sz_5253_; size_t v___x_5254_; lean_object* v_checkImports_5255_; lean_object* v___x_5256_; 
v_sz_5253_ = lean_array_size(v_checks_5248_);
v___x_5254_ = ((size_t)0ULL);
lean_inc_ref(v_checks_5248_);
v_checkImports_5255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_run_spec__1(v___x_5250_, v_sz_5253_, v___x_5254_, v_checks_5248_);
v___x_5256_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; size_t v_sz_5264_; lean_object* v___x_5265_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_a_5257_);
lean_dec_ref_known(v___x_5256_, 1);
lean_inc(v_srcSearchPath_5249_);
v___x_5258_ = l_List_appendTR___redArg(v_srcSearchPath_5249_, v_a_5257_);
v___x_5259_ = lean_obj_once(&l_Lake_BuiltinLint_run___closed__2, &l_Lake_BuiltinLint_run___closed__2_once, _init_l_Lake_BuiltinLint_run___closed__2);
v___x_5260_ = lean_box(v_anyFailed_5252_);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v___x_5259_);
v___x_5262_ = lean_box(v_anyFailed_5252_);
v___x_5263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5262_);
lean_ctor_set(v___x_5263_, 1, v___x_5261_);
v_sz_5264_ = lean_array_size(v_mods_5246_);
v___x_5265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_5250_, v_checkImports_5255_, v_args_5244_, v___x_5258_, v_mods_5246_, v_sz_5264_, v___x_5254_, v___x_5263_);
lean_dec_ref(v_mods_5246_);
lean_dec_ref(v_args_5244_);
lean_dec_ref(v_checkImports_5255_);
if (lean_obj_tag(v___x_5265_) == 0)
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5337_; 
v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5268_ = v___x_5265_;
v_isShared_5269_ = v_isSharedCheck_5337_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5265_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5337_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
switch(v_mode_5247_)
{
case 0:
{
lean_object* v_fst_5270_; uint8_t v___x_5271_; 
v_fst_5270_ = lean_ctor_get(v_a_5266_, 0);
lean_inc(v_fst_5270_);
lean_dec(v_a_5266_);
v___x_5271_ = lean_unbox(v_fst_5270_);
lean_dec(v_fst_5270_);
if (v___x_5271_ == 0)
{
lean_object* v___x_5272_; lean_object* v___x_5274_; 
v___x_5272_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 0, v___x_5272_);
v___x_5274_ = v___x_5268_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5278_; 
v___x_5276_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 0, v___x_5276_);
v___x_5278_ = v___x_5268_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
case 1:
{
lean_object* v_snd_5280_; lean_object* v_snd_5281_; lean_object* v_fst_5282_; lean_object* v_fst_5283_; lean_object* v___x_5284_; 
v_snd_5280_ = lean_ctor_get(v_a_5266_, 1);
lean_inc(v_snd_5280_);
lean_del_object(v___x_5268_);
lean_dec(v_a_5266_);
v_snd_5281_ = lean_ctor_get(v_snd_5280_, 1);
lean_inc(v_snd_5281_);
v_fst_5282_ = lean_ctor_get(v_snd_5280_, 0);
lean_inc(v_fst_5282_);
lean_dec(v_snd_5280_);
v_fst_5283_ = lean_ctor_get(v_snd_5281_, 0);
lean_inc(v_fst_5283_);
lean_dec(v_snd_5281_);
v___x_5284_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles(v_fst_5283_);
lean_dec(v_fst_5283_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5297_; 
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; 
v_unused_5298_ = lean_ctor_get(v___x_5284_, 0);
lean_dec(v_unused_5298_);
v___x_5286_ = v___x_5284_;
v_isShared_5287_ = v_isSharedCheck_5297_;
goto v_resetjp_5285_;
}
else
{
lean_dec(v___x_5284_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5297_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
uint8_t v___x_5288_; 
v___x_5288_ = lean_unbox(v_fst_5282_);
lean_dec(v_fst_5282_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5289_);
v___x_5291_ = v___x_5286_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5295_; 
v___x_5293_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5293_);
v___x_5295_ = v___x_5286_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v___x_5293_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec(v_fst_5282_);
v_a_5299_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5284_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5284_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
default: 
{
lean_object* v_snd_5307_; lean_object* v_snd_5308_; lean_object* v_snd_5309_; lean_object* v_fst_5310_; lean_object* v_fst_5311_; lean_object* v___x_5312_; size_t v_sz_5313_; lean_object* v___x_5314_; 
v_snd_5307_ = lean_ctor_get(v_a_5266_, 1);
lean_del_object(v___x_5268_);
v_snd_5308_ = lean_ctor_get(v_snd_5307_, 1);
v_snd_5309_ = lean_ctor_get(v_snd_5308_, 1);
lean_inc(v_snd_5309_);
v_fst_5310_ = lean_ctor_get(v_a_5266_, 0);
lean_inc(v_fst_5310_);
lean_dec(v_a_5266_);
v_fst_5311_ = lean_ctor_get(v_snd_5309_, 0);
lean_inc(v_fst_5311_);
lean_dec(v_snd_5309_);
v___x_5312_ = lean_box(0);
v_sz_5313_ = lean_array_size(v_fst_5311_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v_fst_5311_, v_sz_5313_, v___x_5254_, v___x_5312_);
lean_dec(v_fst_5311_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5327_; 
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5327_ == 0)
{
lean_object* v_unused_5328_; 
v_unused_5328_ = lean_ctor_get(v___x_5314_, 0);
lean_dec(v_unused_5328_);
v___x_5316_ = v___x_5314_;
v_isShared_5317_ = v_isSharedCheck_5327_;
goto v_resetjp_5315_;
}
else
{
lean_dec(v___x_5314_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5327_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
uint8_t v___x_5318_; 
v___x_5318_ = lean_unbox(v_fst_5310_);
lean_dec(v_fst_5310_);
if (v___x_5318_ == 0)
{
lean_object* v___x_5319_; lean_object* v___x_5321_; 
v___x_5319_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 0, v___x_5319_);
v___x_5321_ = v___x_5316_;
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
else
{
lean_object* v___x_5323_; lean_object* v___x_5325_; 
v___x_5323_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 0, v___x_5323_);
v___x_5325_ = v___x_5316_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5323_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec(v_fst_5310_);
v_a_5329_ = lean_ctor_get(v___x_5314_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5314_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5314_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_a_5338_ = lean_ctor_get(v___x_5265_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5265_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5265_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec_ref(v_checkImports_5255_);
lean_dec_ref(v_mods_5246_);
lean_dec_ref(v_args_5244_);
v_a_5346_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5256_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5256_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
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
lean_object* v___x_5354_; lean_object* v___x_5355_; 
lean_dec_ref(v_mods_5246_);
lean_dec_ref(v_args_5244_);
v___x_5354_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__3));
v___x_5355_ = l_IO_eprintln___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_recordExceptionsToFiles_spec__17(v___x_5354_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5363_; 
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5363_ == 0)
{
lean_object* v_unused_5364_; 
v_unused_5364_ = lean_ctor_get(v___x_5355_, 0);
lean_dec(v_unused_5364_);
v___x_5357_ = v___x_5355_;
v_isShared_5358_ = v_isSharedCheck_5363_;
goto v_resetjp_5356_;
}
else
{
lean_dec(v___x_5355_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5363_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 0, v___x_5359_);
v___x_5361_ = v___x_5357_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
v_a_5365_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5355_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5355_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Lake_BuiltinLint_run(v_args_5373_);
return v_res_5375_;
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
